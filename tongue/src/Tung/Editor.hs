{-# LANGUAGE OverloadedStrings #-}

-- | the editor session: one persistent process that answereth json requests
-- on standard input, one per line, with one response line each. requests run
-- concurrently and may be cancelled; responses never interleave.
module Tung.Editor (editorSession) where

import Control.Concurrent (MVar, ThreadId, forkIO, killThread, modifyMVar, modifyMVar_, newEmptyMVar, newMVar, putMVar, takeMVar, withMVar)
import Control.Exception qualified as Exception
import Control.Monad (unless)
import Data.Aeson (FromJSON (..), Value, eitherDecodeStrict', encode, object, withObject, (.!=), (.:), (.:?), (.=))
import Data.ByteString.Char8 qualified as ByteString
import Data.ByteString.Lazy qualified as LazyByteString
import Data.Either (fromLeft, isRight)
import Data.Functor ((<&>))
import Data.Map.Strict qualified as Map
import System.Directory (getCurrentDirectory)
import System.FilePath ((</>))
import System.IO (hFlush, isEOF, stdout)
import Tung.Diagnostic (Diagnostic (..), failureDiagnostic, goalDiagnostics, proofReport)
import Tung.Format (formatSource)
import Tung.Highlight (DeclarationSummary (..), ImportSummary (..), SourceSyntax (..), sourceSyntaxSummary)
import Tung.Identity (ModuleId (..), SymbolId (..))
import Tung.Library (axiomPolicy, cacheDirectory, findManifest, resolveLibraryRoots)
import Tung.Project (Project (..), loadEditorProject)
import Tung.Source qualified as Source
import Tung.Token (SourceSpan (..))

-- the protocol version is independent of the document version, which
-- identifyeth the source snapshot being checked.
data EditorRequest = EditorRequest
  { requestId :: Int,
    requestVersion :: Int,
    requestCommand :: String,
    requestName :: String,
    requestSource :: String,
    -- unsaved texts of open files, by path; other modules are read from disk.
    requestTexts :: Map.Map FilePath String,
    requestPath :: Maybe FilePath,
    requestAllowedAxioms :: Maybe [String]
  }

instance FromJSON EditorRequest where
  parseJSON = withObject "editor request" \request -> do
    protocol <- request .: "protocol"
    unless (protocol == (1 :: Int)) (fail "unsupported editor protocol")
    EditorRequest
      <$> request .: "id"
      <*> request .: "version"
      <*> request .: "command"
      <*> request .:? "name" .!= ""
      <*> request .: "source"
      <*> request .:? "texts" .!= Map.empty
      <*> request .:? "path"
      <*> request .:? "allowedAxioms"

-- the root's result, its goals and resolved names, and the names it may write.
type CompilationReport = (Either Source.CompileFailure Source.SourceProgram, Source.Report, [(String, SymbolId, Bool)])

-- the session keepeth checked modules by interface key, so editing one file
-- rechecketh only the modules that depend on it. a request that nameth its
-- file also loadeth and saveth interfaces in that project's disk cache. the
-- last root result is kept for a repeated request.
data SessionCache = SessionCache
  { cacheBuild :: String,
    cacheState :: MVar (Map.Map String Source.SourceProgram, Maybe ((String, Map.Map String String), CompilationReport)),
    -- module roots by manifest and its text, so a pinned checkout is
    -- verified again only after its manifest changeth.
    cacheRoots :: MVar (Map.Map (Maybe FilePath, Maybe ByteString.ByteString) [FilePath])
  }

editorSession :: IO ()
editorSession = do
  workers <- newMVar Map.empty
  outputLock <- newMVar ()
  build <- Source.compilerBuild
  state <- newMVar (Map.empty, Nothing)
  roots <- newMVar Map.empty
  sessionLoop (SessionCache build state roots) workers outputLock

sessionLoop :: SessionCache -> MVar (Map.Map Int ThreadId) -> MVar () -> IO ()
sessionLoop cache workers outputLock = go 0
  where
    go previousId = do
      eof <- isEOF
      unless eof do
        line <- ByteString.getLine
        request@EditorRequest {requestId, requestCommand} <- either (ioError . userError . ("invalid editor request: " ++)) pure (eitherDecodeStrict' line)
        unless (requestCommand == "cancel" || requestId > previousId) (ioError (userError "editor request ids must increase"))
        dispatchEditorRequest cache workers outputLock request
        go (if requestCommand == "cancel" then previousId else requestId)

dispatchEditorRequest :: SessionCache -> MVar (Map.Map Int ThreadId) -> MVar () -> EditorRequest -> IO ()
dispatchEditorRequest cache workers outputLock request@EditorRequest {..}
  | requestCommand == "cancel" = cancelEditorRequest workers outputLock requestId
  | otherwise = do
      gate <- newEmptyMVar
      thread <- forkIO $ do
        takeMVar gate
        run `Exception.finally` modifyMVar_ workers (pure . Map.delete requestId)
      modifyMVar_ workers (pure . Map.insert requestId thread)
      putMVar gate ()
  where
    run =
      (editorResponse cache request >>= sendEditorResponse outputLock requestId requestVersion)
        `Exception.catch` \exception ->
          case Exception.fromException exception of
            Just Exception.ThreadKilled -> pure ()
            _ -> sendEditorResponse outputLock requestId requestVersion (editorError ("checker session failed: " ++ Exception.displayException exception))

cancelEditorRequest :: MVar (Map.Map Int ThreadId) -> MVar () -> Int -> IO ()
cancelEditorRequest workers outputLock requestId =
  -- cancellation must not interrupt a response halfway through its json line.
  withMVar outputLock \_ -> do
    thread <- modifyMVar workers \running -> pure (Map.delete requestId running, Map.lookup requestId running)
    mapM_ killThread thread

-- tidying and highlighting read only the source. every other command
-- checketh it with the modules its brings reach, resolved as the command
-- line resolveth them.
editorResponse :: SessionCache -> EditorRequest -> IO Value
editorResponse cache request@EditorRequest {requestCommand, requestSource = source} =
  case requestCommand of
    "format" -> pure (either (editorError . ("tidy error: " ++)) (\formatted -> object ["kind" .= ("format" :: String), "source" .= formatted]) (formatSource source))
    "highlight" -> pure (syntaxResponse (sourceSyntaxSummary source))
    _ ->
      editorProject cache request >>= \case
        Left message -> pure (editorError ("project error: " ++ message))
        Right Project {projectImports, projectImportPaths} -> projectResponse cache request projectImports projectImportPaths

-- a document's project: its brings, read through the unsaved texts. an
-- unresolved bring is left for checking to report at its span.
editorProject :: SessionCache -> EditorRequest -> IO (Either String Project)
editorProject cache EditorRequest {requestPath, requestTexts, requestSource} = do
  owner <- maybe ((</> "<untitled>.tung") <$> getCurrentDirectory) pure requestPath
  sessionRoots cache owner >>= \case
    Left message -> pure (Left message)
    Right roots -> loadEditorProject roots requestTexts owner requestSource

-- module roots are resolved again only when the manifest's text changeth.
sessionRoots :: SessionCache -> FilePath -> IO (Either String [FilePath])
sessionRoots SessionCache {cacheRoots} owner =
  findManifest owner >>= \case
    Left message -> pure (Left message)
    Right manifest -> do
      text <- traverse ByteString.readFile manifest
      modifyMVar cacheRoots \known -> case Map.lookup (manifest, text) known of
        Just roots -> pure (known, Right roots)
        Nothing -> resolveLibraryRoots owner <&> \resolved -> (either (const known) (\roots -> Map.insert (manifest, text) roots known) resolved, resolved)

projectResponse :: SessionCache -> EditorRequest -> Map.Map String String -> Map.Map String FilePath -> IO Value
projectResponse cache EditorRequest {requestCommand, requestName, requestSource = source, requestPath, requestAllowedAxioms} imports files =
  case requestCommand of
    "check" ->
      compilationReport cache requestPath source imports <&> \(result, report, _) ->
        object ["kind" .= ("check" :: String), "diagnostics" .= (either (pure . failureDiagnostic source imports) (const []) result ++ goalDiagnostics (Source.reportHoles report))]
    -- each written name checking resolved to a global, by its span: the
    -- names of every declaration that checketh, even beside an error, and
    -- the file of each bring path.
    "names" ->
      compilationReport cache requestPath source imports <&> \(_, report, visible) ->
        object
          [ "kind" .= ("names" :: String),
            "files" .= files,
            "resolved" .= [(spanStart span, spanEnd span, moduleLabel owner, name, namesType) | (span, SymbolId owner name, namesType) <- Source.reportNames report],
            "visible" .= [(written, moduleLabel owner, name, constructor) | (written, SymbolId owner name, constructor) <- visible]
          ]
    "type" ->
      compiled cache requestPath source imports <&> \case
        Left failure -> editorError (diagnosticMessage (failureDiagnostic source imports failure))
        Right program -> either (editorError . ("type error: " ++)) (\ty -> object ["kind" .= ("type" :: String), "type" .= ty]) (Source.typeOfName program requestName)
    -- the editor's audit is always strict.
    "proof" ->
      compiled cache requestPath source imports >>= \case
        Left failure -> pure (editorError (diagnosticMessage (failureDiagnostic source imports failure)))
        Right program -> do
          path <- maybe getCurrentDirectory pure requestPath
          policy <- axiomPolicy requestAllowedAxioms path
          pure $ either (editorError . ("name error: " ++)) (uncurry proofResponse) (Source.auditVerified program True policy requestName)
    _ -> pure (editorError ("checker session failed: unknown command '" ++ requestCommand ++ "'"))

-- the parser's roles and the concrete tree's structure, from one parse.
syntaxResponse :: SourceSyntax -> Value
syntaxResponse SourceSyntax {..} =
  object
    [ "kind" .= ("highlight" :: String),
      "roles" .= syntaxRoles,
      "tokens" .= syntaxTokens,
      "declarations" .= [object ["kind" .= declarationKind, "start" .= declarationStart, "end" .= declarationEnd, "headerEnd" .= declarationHeaderEnd, "shown" .= declarationShown, "doc" .= declarationDoc] | DeclarationSummary {..} <- syntaxDeclarations],
      "imports" .= [object ["path" .= importPath, "alias" .= importAlias, "start" .= importStart, "end" .= importEnd] | ImportSummary {..} <- syntaxImports],
      "scopes" .= syntaxScopes
    ]

editorError :: String -> Value
editorError message = object ["kind" .= ("error" :: String), "message" .= message]

proofResponse :: Source.ProofAudit -> Either String () -> Value
proofResponse audit verified =
  object
    [ "kind" .= ("proof" :: String),
      "audit" .= object ["name" .= Source.auditName audit, "type" .= Source.auditType audit, "dependencies" .= map dependencyJSON (Source.auditDependencies audit)],
      "verified" .= isRight verified,
      "message" .= fromLeft "name ok" verified,
      "report" .= proofReport audit verified
    ]
  where
    dependencyJSON Source.ProofDependency {dependencySymbol = SymbolId owner name, dependencyName, dependencyType, dependencyKind} =
      object $
        [ "symbol" .= object ["module" .= moduleLabel owner, "name" .= name],
          "name" .= dependencyName,
          "type" .= dependencyType
        ]
          ++ case dependencyKind of
            Source.SorryDependency -> ["kind" .= ("sorry" :: String)]
            Source.AxiomDependency -> ["kind" .= ("axiom" :: String)]
            Source.HostDependency key -> ["kind" .= ("host" :: String), "host" .= key]

moduleLabel :: ModuleId -> String
moduleLabel = \case
  RootModule -> "<root>"
  SourceModule path -> path
  PrimitiveModule -> "<primitive>"

compiled :: SessionCache -> Maybe FilePath -> String -> Map.Map String String -> IO (Either Source.CompileFailure Source.SourceProgram)
compiled cache path source = fmap (\(result, _, _) -> result) . compilationReport cache path source

compilationReport :: SessionCache -> Maybe FilePath -> String -> Map.Map String String -> IO CompilationReport
compilationReport SessionCache {cacheBuild, cacheState} path source imports = modifyMVar cacheState \previous@(memory, root) ->
  case root of
    Just (request, result) | request == (source, imports) -> pure (previous, result)
    _ -> do
      let snapshot = Source.sourceSnapshot source
          modules = Map.map Source.sourceSnapshot imports
          keys = Source.cacheKeys cacheBuild modules
          remembered = Map.mapMaybe (`Map.lookup` memory) keys
          kept reached = Map.fromList [(key, program) | (name, program) <- Map.toList reached, Just key <- [Map.lookup name keys]]
      directory <- traverse cacheDirectory path
      (available, imported) <- Source.compileImportsCached directory keys remembered modules (Source.snapshotImportPaths snapshot)
      case imported of
        Left failure ->
          let result = (Left failure, Source.recoverSnapshotReport available RootModule snapshot modules, Source.snapshotVisible available snapshot modules)
           in pure ((kept available, Just ((source, imports), result)), result)
        Right reached -> do
          let result = fst <$> Source.compileSnapshot reached RootModule snapshot modules
              report = (result, either (const (Source.recoverSnapshotReport reached RootModule snapshot modules)) (\program -> Source.Report (reverse (Source.sourceHoles program)) (Source.sourceNames program)) result, Source.snapshotVisible reached snapshot modules)
          _ <- Exception.evaluate result
          pure ((kept reached, Just ((source, imports), report)), report)

sendEditorResponse :: MVar () -> Int -> Int -> Value -> IO ()
sendEditorResponse outputLock requestId version output = do
  let response = encode (object ["protocol" .= (1 :: Int), "id" .= requestId, "version" .= version, "result" .= output])
  _ <- Exception.evaluate (LazyByteString.length response)
  withMVar outputLock \_ -> do
    LazyByteString.hPut stdout response
    putChar '\n'
    hFlush stdout
