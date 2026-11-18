{-# LANGUAGE MultilineStrings #-}

-- the cli shares one project loader across running, checking, and inspection.
-- `--editor-session` starteth the persistent bridge the editor useth.
module Main where

import Control.Exception qualified as Exception
import Control.Monad (unless)
import Data.List (isPrefixOf)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import System.Directory (getCurrentDirectory)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitFailure, exitWith)
import System.FilePath ((</>))
import Tung
import Tung.Run qualified as Run
import Tung.Source qualified as Source

main :: IO ()
main = do
  arguments <- getArgs
  (strict, allowed, args) <- either (\message -> putStrLn message >> exitFailure) pure (commandOptions arguments)
  case args of
    ["--name", name, path] -> checkNameFile strict allowed name path
    _ | Just _ <- allowed -> putStrLn "axiom options require --name" >> exitFailure
    ["--check-stdin"] -> checkStdin strict
    ["--editor-session"] -> editorSession
    ["--language-metadata"] -> putStr languageMetadata
    ["--library-paths"] -> getCurrentDirectory >>= listLibraryPaths
    ["--library-paths", path] -> listLibraryPaths path
    ["--check", path] -> checkFile strict path
    ["--tidy-stdin"] -> getContents >>= either (\message -> putStrLn ("tidy error: " ++ message) >> exitFailure) putStr . formatSource
    "--tidy" : paths | not (null paths) -> mapM formatFile paths >>= \results -> unless (and results) exitFailure
    ["--help"] -> putStr usage
    path : programArgs
      | not ("-" `isPrefixOf` path) -> runFile strict path programArgs
    _ -> putStr usage >> exitFailure

-- proof-policy options precede the command. an explicit empty allowlist
-- cannot be combined with named allowances.
commandOptions :: [String] -> Either String (Bool, Maybe [String], [String])
commandOptions = go False Nothing False
  where
    go _ allowed empty ("--no-sorry" : rest) = go True allowed empty rest
    go strict allowed empty ("--allow-axiom" : name : rest)
      | not ("--" `isPrefixOf` name), not empty = go strict (Just (fromMaybe [] allowed ++ [name])) False rest
    go _ _ _ ["--allow-axiom"] = Left "--allow-axiom requireth a name"
    go strict allowed _ ("--no-axiom" : rest)
      | maybe True null allowed = go strict (Just []) True rest
    go _ _ _ ("--allow-axiom" : _) = Left "--allow-axiom requireth a name and cannot accompany --no-axiom"
    go _ _ _ ("--no-axiom" : _) = Left "--no-axiom cannot accompany --allow-axiom"
    go strict allowed _ args = Right (strict, allowed, args)

-- a project loaded from the library roots of `base`, and the `bring` paths it
-- reacheth, checked together.
withProject :: FilePath -> ([FilePath] -> IO (Either String Project)) -> (Project -> Diagnostic -> [Source.Hole] -> IO ()) -> (Source.SourceProgram -> IO ()) -> IO ()
withProject base load failed action =
  resolveLibraryRoots base >>= \case
    Left message -> projectFailure message
    Right roots ->
      load roots >>= \case
        Left message -> projectFailure message
        Right project@Project {projectPath, projectSource, projectImports, projectSnapshot, projectImportSnapshots} -> do
          -- imports reuse checked interfaces; newly checked ones are saved.
          directory <- cacheDirectory projectPath
          keys <- (`Source.cacheKeys` projectImportSnapshots) <$> Source.compilerBuild
          (available, imported) <- Source.compileImportsCached (Just directory) keys Map.empty projectImportSnapshots (Source.snapshotImportPaths projectSnapshot)
          let failure known problem = failed project (failureDiagnostic projectSource projectImports problem) (Source.recoverSnapshotHoles known (SourceModule projectPath) projectSnapshot projectImportSnapshots)
          case imported of
            Left problem -> failure available problem
            Right reached -> either (failure reached) (action . fst) (Source.compileSnapshot reached (SourceModule projectPath) projectSnapshot projectImportSnapshots)

-- a file's failure is reported in the file that raised it.
withProgram :: FilePath -> (Source.SourceProgram -> IO ()) -> IO ()
withProgram path = withProject path (`loadProjectFile` path) (\project diagnostic _ -> report project diagnostic [])

-- a failure in an imported module is reported at that module's file.
-- checking still faileth, but unrelated unfinished proofs retain their goals.
report :: Project -> Diagnostic -> [Source.Hole] -> IO a
report Project {projectPath, projectSource, projectImports, projectImportPaths} diagnostic@Diagnostic {diagnosticPath} holes = do
  putStrLn
    ( renderFileDiagnostic
        (maybe projectPath (\owner -> Map.findWithDefault owner owner projectImportPaths) diagnosticPath)
        (maybe projectSource (\owner -> Map.findWithDefault projectSource owner projectImports) diagnosticPath)
        diagnostic
    )
  printGoals projectPath projectSource holes
  exitFailure

printGoals :: FilePath -> String -> [Source.Hole] -> IO ()
printGoals path source = mapM_ \hole@Source.Hole {holeSpan} ->
  putStrLn case holeSpan of
    Just span -> renderFileDiagnostic path source (Diagnostic GoalDiagnostic Nothing span (goalMessage hole))
    Nothing -> goalMessage hole

-- main runneth only after the whole program is checked.
runProgram :: [String] -> Source.SourceProgram -> IO ()
runProgram programArgs program = do
  host <- Run.ioHost programArgs
  case Run.runMain host program of
    Left message -> typeFailure message
    Right action ->
      action >>= \case
        Left message -> putStrLn ("runtime error: " ++ message) >> exitFailure
        Right 0 -> pure ()
        Right status -> exitWith (ExitFailure (fromInteger status))

-- each file is tidied on its own; one that doth not parse is reported and
-- left unchanged.
formatFile :: FilePath -> IO Bool
formatFile path = do
  source <- readFile path
  _ <- Exception.evaluate (length source)
  case formatSource source of
    Left message -> putStrLn ("tidy error: " ++ path ++ ": " ++ message) >> pure False
    Right formatted -> unless (formatted == source) (writeFile path formatted) >> pure True

runFile :: Bool -> FilePath -> [String] -> IO ()
runFile strict path programArgs = withProgram path \program -> do
  refuseSorry strict program
  runProgram programArgs program

-- a checked file is a module or a program: a `main` it defineth must be
-- `𝟙 effect`.
checkFile :: Bool -> FilePath -> IO ()
checkFile strict path = withProject path (`loadProjectFile` path) report \program -> do
  source <- readFile path
  checkedOk strict path source program

-- a checked program printeth `type ok`, each declaration or law that assumeth
-- `sorry`, and then the goal and named context of each `sorry` in the file.
-- under `--no-sorry` an assumption faileth instead.
checkedOk :: Bool -> FilePath -> String -> Source.SourceProgram -> IO ()
checkedOk strict path source program = do
  either typeFailure pure (Run.checkMain program)
  refuseSorry strict program
  putStrLn "type ok"
  mapM_ (putStrLn . ("sorry: " ++)) (Source.sorryAssumptions program)
  mapM_ (putStrLn . ("axiom: " ++)) (Source.axiomAssumptions program)
  printGoals path source (reverse (Source.sourceHoles program))

refuseSorry :: Bool -> Source.SourceProgram -> IO ()
refuseSorry strict program = case Source.sorryAssumptions program of
  assumptions@(_ : _)
    | strict -> mapM_ (putStrLn . ("sorry: " ++)) assumptions >> exitFailure
  _ -> pure ()

-- one name is audited independently of unfinished, unrelated declarations.
checkNameFile :: Bool -> Maybe [String] -> String -> FilePath -> IO ()
checkNameFile strict explicit name path = withProgram path \program -> do
  policy <- axiomPolicy explicit path
  case Source.auditVerified program strict policy name of
    Left message -> putStrLn ("name error: " ++ message) >> exitFailure
    Right (audit, verified) -> do
      putStr (proofReport audit verified)
      either (const exitFailure) pure verified

-- standard input is checked as a file in the current directory. it hath no
-- file position, so a failure printeth only its message.
checkStdin :: Bool -> IO ()
checkStdin strict = do
  source <- getContents
  current <- getCurrentDirectory
  withProject current (\roots -> loadProjectSource roots (current </> "<stdin>.tung") source) (\_ diagnostic holes -> putStrLn (diagnosticMessage diagnostic) >> printGoals "<stdin>" source holes >> exitFailure) $
    checkedOk strict "<stdin>" source

listLibraryPaths :: FilePath -> IO ()
listLibraryPaths path = resolveLibraryRoots path >>= either projectFailure (mapM_ putStrLn)

typeFailure :: String -> IO a
typeFailure message = putStrLn ("type error: " ++ message) >> exitFailure

projectFailure :: String -> IO a
projectFailure message = putStrLn ("project error: " ++ message) >> exitFailure

usage :: String
usage =
  """
  usage: tung <file.tung> [arguments...]
         tung --check <file.tung>
         tung --name <name> <file.tung>
         tung --tidy <file.tung>...
         tung --tidy-stdin
         tung --language-metadata
         tung --library-paths [project-path]

  --name printeth the name's type and the sorry, axioms, and hosts it reacheth.
  --no-sorry before a command rejecteth any reachable sorry.
  --allow-axiom <name> may precede --name repeatedly; --no-axiom alloweth none.
  without either option, --name useth the nearest tung.yaml proof policy.

  """
