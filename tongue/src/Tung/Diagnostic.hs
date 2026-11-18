{-# LANGUAGE OverloadedStrings #-}

-- | what command-line and editor clients print: structured source
-- diagnostics, goals, and the proof report of an audit.
module Tung.Diagnostic
  ( Diagnostic (..),
    DiagnosticKind (..),
    failureDiagnostic,
    renderFileDiagnostic,
    goalMessage,
    goalDiagnostics,
    proofReport,
  )
where

import Data.Aeson (ToJSON (..), object, (.=))
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Tung.Source (CompileFailure (..), DependencyKind (..), FailureKind (..), Hole (..), ProofAudit, ProofDependency (..), auditDependencies, auditName, auditType)
import Tung.Token (SourceSpan (..), utf16Length, utf16Width)

data DiagnosticKind = ParseDiagnostic | TypeDiagnostic | GoalDiagnostic
  deriving (Eq, Show)

data Diagnostic = Diagnostic
  { diagnosticKind :: !DiagnosticKind,
    diagnosticPath :: Maybe FilePath,
    diagnosticSpan :: !SourceSpan,
    diagnosticMessage :: String
  }
  deriving (Eq, Show)

instance ToJSON Diagnostic where
  toJSON Diagnostic {diagnosticKind, diagnosticPath, diagnosticSpan = SourceSpan start end, diagnosticMessage} =
    object
      ( [ "kind" .= renderKind diagnosticKind,
          "start" .= start,
          "end" .= end,
          "message" .= diagnosticMessage
        ]
          ++ maybe [] (\path -> ["path" .= path]) diagnosticPath
      )

-- a compile failure, located in the module that raised it. an
-- unlocated infrastructure failure useth the start of that module's source.
failureDiagnostic :: String -> Map.Map String String -> CompileFailure -> Diagnostic
failureDiagnostic source imports CompileFailure {failureKind, failurePath, failureSpan, failureText} =
  let owner = maybe source (\path -> Map.findWithDefault source path imports) failurePath
      (kind, prefix) = case failureKind of
        ParseFailure -> (ParseDiagnostic, "parse error: ")
        CheckFailure -> (TypeDiagnostic, "type error: ")
   in Diagnostic kind failurePath (fromMaybe (SourceSpan 0 (min 1 (utf16Length owner))) failureSpan) (prefix ++ failureText)

renderFileDiagnostic :: FilePath -> String -> Diagnostic -> String
renderFileDiagnostic path source Diagnostic {diagnosticSpan = SourceSpan start end, diagnosticMessage} =
  intercalate ":" [path, show startLine, show startColumn, show endLine, show endColumn] ++ ": " ++ diagnosticMessage
  where
    (startLine, startColumn) = sourcePosition source start
    (endLine, endColumn) = sourcePosition source end

sourcePosition :: String -> Int -> (Int, Int)
sourcePosition source wanted = foldl' advance (1, 1) (map snd (takeWhile ((< wanted) . fst) (zip offsets source)))
  where
    offsets = scanl (+) 0 (map utf16Width source)
    advance (line, _) '\n' = (line + 1, 1)
    advance (line, column) character = (line, column + utf16Width character)

renderKind :: DiagnosticKind -> String
renderKind ParseDiagnostic = "parse"
renderKind TypeDiagnostic = "type"
renderKind GoalDiagnostic = "goal"

-- a goal line, then each named local of its context, outermost first.
goalMessage :: Hole -> String
goalMessage Hole {holeGoal, holeContext} =
  intercalate "\n" (("goal: " ++ holeGoal) : ["  " ++ name ++ ": " ++ ty | (name, ty) <- holeContext])

-- goals use the same structured locations as errors; messages remain prose.
goalDiagnostics :: [Hole] -> [Diagnostic]
goalDiagnostics holes =
  [Diagnostic GoalDiagnostic Nothing span (goalMessage hole) | hole@Hole {holeSpan = Just span} <- holes]

-- the cli and editor share the compiler's complete, deterministic report.
proofReport :: ProofAudit -> Either String () -> String
proofReport audit verified =
  unlines $
    ["name: " ++ auditName audit, "type: " ++ auditType audit]
      ++ (if null dependencies then ["dependencies: none"] else map dependencyReport dependencies)
      ++ [either ("name error: " ++) (const "name ok") verified]
  where
    dependencies = auditDependencies audit
    dependencyReport ProofDependency {dependencyName, dependencyType, dependencyKind} =
      case dependencyKind of
        SorryDependency -> "sorry: " ++ dependencyName ++ ": " ++ dependencyType
        AxiomDependency -> "axiom: " ++ dependencyName ++ ": " ++ dependencyType
        HostDependency key -> "host: " ++ dependencyName ++ " [" ++ key ++ "]: " ++ dependencyType
