module Main where

import Test.Class qualified as Class
import Test.Core qualified as Core
import Test.CoreInductive qualified as CoreInductive
import Test.Diagnostic qualified as Diagnostic
import Test.Effect qualified as Effect
import Test.Evaluate qualified as Evaluate
import Test.Field qualified as Field
import Test.Format qualified as Format
import Test.Harness (runGroups)
import Test.HarnessTests qualified as HarnessTests
import Test.Host qualified as Host
import Test.Inductive qualified as Inductive
import Test.Integration qualified as Integration
import Test.Layering qualified as Layering
import Test.Library qualified as Library
import Test.List qualified as List
import Test.Literal qualified as Literal
import Test.Match qualified as Match
import Test.Module qualified as Module
import Test.Name qualified as Name
import Test.Parse qualified as Parse
import Test.Program qualified as Program
import Test.Project qualified as Project
import Test.Recursion qualified as Recursion
import Test.Source qualified as Source
import Test.Standard qualified as Standard
import Test.Token qualified as Token
import Test.Type qualified as Type
import Test.Validate qualified as Validate

-- each group's name selecteth it in `TUNG_TEST_GROUP` and prefixeth its
-- failures. core groups check kernel terms directly; the groups after
-- them check source declarations through elaboration.
main :: IO ()
main =
  runGroups
    [ ("harness", HarnessTests.group),
      ("layering", Layering.group),
      ("token", Token.group),
      ("parse", Parse.group),
      ("format", Format.group),
      ("validate", Validate.group),
      ("project", Project.group),
      ("library", Library.group),
      ("type", Type.group),
      ("name", Name.group),
      ("evaluate", Evaluate.group),
      ("standard", Standard.group),
      ("program", Program.group),
      ("core", Core.group),
      ("core-inductive", CoreInductive.group),
      ("inductive", Inductive.group),
      ("effect", Effect.group),
      ("class", Class.group),
      ("host", Host.group),
      ("list", List.group),
      ("literal", Literal.group),
      ("match", Match.group),
      ("module", Module.group),
      ("field", Field.group),
      ("recursion", Recursion.group),
      ("source", Source.group),
      ("diagnostic", Diagnostic.group),
      ("integration", Integration.group)
    ]
