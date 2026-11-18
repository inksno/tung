-- | the source boundary: parsing, elaboration, and checking. types and values
-- share one syntax and namespace. only closed, kernel-checked definitions
-- enter a source program.
module Tung.Source
  ( SourceProgram,
    sourceEnvironment,
    sourceDefinitions,
    sourceGlobal,
    compileSnapshot,
    compileImports,
    compileImportsCached,
    recoverSnapshotHoles,
    recoverSnapshotReport,
    snapshotVisible,
    sourceNames,
    Report (..),
    cacheKeys,
    compilerBuild,
    loadInterfaces,
    saveInterfaces,
    CompileFailure (..),
    FailureKind (..),
    SourceSnapshot,
    sourceSnapshot,
    recoverSnapshot,
    snapshotText,
    snapshotImportPaths,
    typeOfName,
    sorryAssumptions,
    axiomAssumptions,
    DependencyKind (..),
    ProofDependency (..),
    ProofAudit,
    auditName,
    auditType,
    auditDependencies,
    auditProof,
    verifyProof,
    auditVerified,
    Hole (..),
    sourceHoles,
    sourceExports,
    inferSourceExpression,
    normaliseSourceExpression,
    Expression,
    Parameter (..),
    Binder (..),
    Argument (..),
    Declaration (..),
    ConstructorDeclaration (..),
    Row (..),
    parseSource,
    parseProgram,
    sketch,
    parseExpression,
  )
where

import Data.Either (fromRight)
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Tung.Core.Check qualified as K
import Tung.Core.Normalise qualified as N
import Tung.Core.Syntax hiding (Lambda, Literal)
import Tung.Identity (ModuleId (..), SymbolId (..))
import Tung.Source.Cache (cacheKeys, compilerBuild, loadInterfaces, saveInterfaces)
import Tung.Source.Declaration (insertDeclarations, recoverDeclarations)
import Tung.Source.Elaborate (elaborateHoles, elaborateHolesReport)
import Tung.Source.Environment
import Tung.Source.Error (CompileFailure (..), FailureKind (..))
import Tung.Source.Error qualified as Error
import Tung.Source.Expression (inferExpression)
import Tung.Source.Module qualified as Modules
import Tung.Source.Parse (SourceSnapshot, parseExpression, parseProgram, parseSource, recoverSnapshot, snapshotImportPaths, snapshotText, sourceSnapshot)
import Tung.Source.Proof
import Tung.Source.Scope
import Tung.Source.Syntax
import Tung.Token (SourceFailure (..), SourceSpan (..))

-- a root module and the modules it useth, keyed by `bring` path. each is checked
-- once, in dependency order, and modules already compiled are reused
-- unchanged; a cycle is an error. a root that endeth in `yield` returneth the
-- yielded expression, checked against the finished module.
compileSnapshot :: Map.Map String SourceProgram -> ModuleId -> SourceSnapshot -> Map.Map String SourceSnapshot -> Either CompileFailure (SourceProgram, Maybe K.Inferred)
compileSnapshot compiled owner source modules = do
  (program, yielded) <- Modules.compileProject insertDeclarations compiled owner source modules
  checked <- traverse (Error.compilationFailure CheckFailure . inferInHoles program) yielded
  let holes = maybe [] snd checked
  pure (program {programHoles = reverse holes ++ programHoles program}, fst <$> checked)

-- the named modules and everything they use.
compileImports :: Map.Map String SourceProgram -> Map.Map String SourceSnapshot -> [String] -> Either CompileFailure (Map.Map String SourceProgram)
compileImports = Modules.compileImports insertDeclarations

-- the named modules and everything they use, each compiled once: a known
-- module is kept, the rest are loaded from interfaces saved in the cache
-- directory under their keys, and what remaineth is checked and saved there.
-- the modules available before checking come back beside the outcome, so a
-- failure can still recover goals from them.
compileImportsCached :: Maybe FilePath -> Map.Map String String -> Map.Map String SourceProgram -> Map.Map String SourceSnapshot -> [String] -> IO (Map.Map String SourceProgram, Either CompileFailure (Map.Map String SourceProgram))
compileImportsCached directory keys known modules paths = do
  loaded <- maybe (pure Map.empty) (\cache -> loadInterfaces cache modules (Map.difference keys known)) directory
  let available = Map.union known loaded
  case compileImports available modules paths of
    Left failure -> pure (available, Left failure)
    Right reached -> do
      mapM_ (\cache -> saveInterfaces cache keys (Map.difference reached available)) directory
      pure (available, Right reached)

-- best-effort goals for diagnostics. imports still check in full; failed local
-- groups are never inserted, and no partial program escapeth this function.
-- syntax recovery only retains complete declarations at safe boundaries.
recoverSnapshotHoles :: Map.Map String SourceProgram -> ModuleId -> SourceSnapshot -> Map.Map String SourceSnapshot -> [Hole]
recoverSnapshotHoles compiled owner source modules = sortOn (fmap spanStart . holeSpan) (reportHoles (recoverSnapshotReport compiled owner source modules))

-- the goals and resolved names of every declaration recovery can check.
recoverSnapshotReport :: Map.Map String SourceProgram -> ModuleId -> SourceSnapshot -> Map.Map String SourceSnapshot -> Report
recoverSnapshotReport compiled owner source modules =
  case Modules.recoverModule recoverDeclarations owner declarations reached of
    Nothing -> mempty
    Just (program, report) -> report <> yieldedReport program
  where
    (declarations, yielded, _) = recoverSnapshot source
    reached = reachable compiled modules declarations
    yieldedReport program@SourceProgram {..} = maybe mempty (snd . elaborateHolesReport program . inferExpression programEnvironment globalNames emptyScope) yielded

-- the imports a recovered source bringeth that compile, each on its own.
reachable :: Map.Map String SourceProgram -> Map.Map String SourceSnapshot -> [(a, Declaration)] -> Map.Map String SourceProgram
reachable compiled modules declarations = foldl load compiled [path | (_, ImportDeclaration path _) <- declarations]
  where
    load done path = fromRight done (compileImports done modules [path])

-- the names a source may write at its top level, without checking it: its own
-- declarations, then its imports' names, each marked when it nameth a
-- constructor. a failed import contributeth nothing.
snapshotVisible :: Map.Map String SourceProgram -> SourceSnapshot -> Map.Map String SourceSnapshot -> [(String, SymbolId, Bool)]
snapshotVisible compiled source modules = own ++ imported
  where
    (declarations, _, _) = recoverSnapshot source
    reached = reachable compiled modules declarations
    available = [entry | entry@(_, ImportDeclaration path _) <- declarations, Map.member path reached]
    own = [(name, SymbolId RootModule name, constructor) | (_, declaration) <- declarations, (name, constructor) <- defined (unshown declaration)]
    defined = \case
      Declaration {declarationName} -> [(declarationName, False)]
      HostDeclaration {hostName} -> [(hostName, False)]
      AssumptionDeclaration {assumptionName} -> [(assumptionName, False)]
      InductiveDeclaration {inductiveName, inductiveConstructors} -> (inductiveName, False) : [(constructorName constructor, True) | constructor <- inductiveConstructors]
      ClassDeclaration {classDeclarationName, classDeclarationMembers} -> (classDeclarationName, False) : [(member, False) | ClassMember member _ <- classDeclarationMembers]
      _ -> []
    imported = case Modules.moduleEnvironment available reached of
      Left _ -> []
      Right SourceProgram {globalNames, programEnvironment} ->
        [ (name, symbol, isConstructor (Map.lookup symbol (globals programEnvironment)))
        | (name, binding) <- Map.toList (nameTable globalNames),
          Just symbol <- [bindingSymbol binding]
        ]
    isConstructor = \case
      Just Definition {definitionBody = DataConstructor _ _} -> True
      _ -> False

inferSourceExpression :: SourceProgram -> String -> Either String K.Inferred
inferSourceExpression program source = parseExpression source >>= Error.toString . inferIn program

inferIn :: SourceProgram -> Expression -> Either SourceFailure K.Inferred
inferIn program = fmap fst . inferInHoles program

inferInHoles :: SourceProgram -> Expression -> Either SourceFailure (K.Inferred, [Hole])
inferInHoles program@SourceProgram {..} expression = do
  (result, holes, _) <- elaborateHoles program (inferExpression programEnvironment globalNames emptyScope expression)
  Error.fromString (K.validate programEnvironment result)
  pure (result, holes)

normaliseSourceExpression :: SourceProgram -> String -> Either String Term
normaliseSourceExpression program@SourceProgram {..} source = do
  result <- inferSourceExpression program source
  -- source inference rechecketh the generalised term before raw NBE can see it.
  N.normalise (globals programEnvironment) 0 (K.inferredTerm result)
