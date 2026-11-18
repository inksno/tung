-- lists at every universe use ordinary constructors and structural induction.
module Test.List (group) where

import Control.Monad (forM_)
import Data.Either (isLeft)
import Test.Harness (Test, expect, expectEq)
import Test.Support
import Tung.Core
import Tung.Source (SourceProgram, normaliseSourceExpression, sourceDefinitions, sourceEnvironment)

group :: IO [Test]
group = do
  source <- exampleSource "list_family.tung"
  pure (tests source)

tests :: String -> [Test]
tests source =
  [ checked "one list family storeth values, types, and type constructors" $
      "let values:nat list ≔ "
        ++ values
        ++ "\n"
        ++ "let types:* list ≔ "
        ++ types
        ++ "\n"
        ++ "let constructors:[*, *] list ≔ "
        ++ constructors
        ++ "\n",
    same "supplied and inferred implicit list elements agree" "" values "zero ‥ @nat ((zero next) ‥ @nat (∅ @nat))",
    expectEq "append computeth at value and type levels" (Right [True, True]) $
      traverse
        (uncurry (equalIn (extended "")))
        [ ("(>{‥, zero, ∅}) · (>{‥, zero next, ∅})", values),
          ("(>{‥, nat, ∅}) · (>{‥, bool, ∅})", types)
        ],
    same "map computeth from the ordinary list eliminator" "" (values ++ " map next") ">{‥, zero next, (zero next) next, ∅}",
    same "map can turn type constructors into types" "" (constructors ++ " map {F:[*, *] ^ nat F}") ">{‥, nat list, nat, ∅}",
    same "fold replaceth constructors by its supplied methods" "" (values ++ " gather zero {_, rest ^ rest next}") "(zero next) next",
    expectEq "open append retaineth an induction neutral and a checked type" (Right True) $ do
      program <- extended openAppend
      result <- normaliseSourceExpression program "append_empty"
      infer (sourceEnvironment program) result >>= validate (sourceEnvironment program)
      identity <- normaliseSourceExpression program "{xs:nat list ^ xs}"
      pure (eraseLevels result /= eraseLevels identity),
    same "open append computeth after its list is substituted" openAppend (values ++ " append_empty") values,
    checked "append and map aliases convert inside family indices" $
      indexed
        ++ "let appended ≔ (>{‥, nat, ∅}) · (>{‥, bool, ∅}) "
        ++ "let mapped ≔ row map {α:* ^ α} "
        ++ "let first:appended tag ≔ witness "
        ++ "let second:mapped tag ≔ witness ",
    rejected "list indices preserve element order" (indexed ++ "let bad:(>{‥, bool, nat, ∅}) tag ≔ witness "),
    rejected "list indices preserve duplicate elements" (indexed ++ "let bad:(>{‥, nat, nat, bool, ∅}) tag ≔ witness "),
    rejected "a list cannot mix incompatible element types" "let bad ≔ >{‥, zero, nat, ∅} ",
    rejected "a list cannot put its universe inside itself" "let bad ≔ (let U ≔ * yield U ‥ @U (∅ @U)) "
  ]
  where
    extended "" = compile (source ++ naturalSource)
    extended suffix = compile (source ++ naturalSource ++ suffix)
    checked label suffix = expectEq label (Right ()) $ do
      program <- extended suffix
      forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd)
    same label suffix actual expected = expectEq label (Right True) (equalIn (extended suffix) actual expected)
    rejected label suffix = expect label (isLeft (extended suffix))

naturalSource, openAppend, indexed, values, types, constructors :: String
naturalSource =
  """
  type nat:* { zero: nat, next:[nat, nat] }
  type bool:* { no: bool, yes: bool }

  """
openAppend = "let append_empty:[xs:nat list, nat list] ≔ xs · (∅ @nat) "
indexed =
  """
  let row:* list ≔ >{‥, nat, bool, ∅}
  type tag:[* list, *] { witness:row tag }

  """
values = ">{‥, zero, zero next, ∅}"
types = ">{‥, nat, bool, ∅}"
constructors = ">{‥, list, {α:* ^ α}, ∅ @([*, *])}"

compile :: String -> Either String SourceProgram
compile = compileAs "dependent_list.tung"

equalIn :: Either String SourceProgram -> String -> String -> Either String Bool
equalIn result actual expected = result >>= \program -> sameNormalIn program actual expected
