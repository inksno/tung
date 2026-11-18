-- named fields of a one-constructor type: generated accessors and projection.
module Test.Field (group) where

import Test.Harness (Test, expectEq)
import Test.Support

group :: IO [Test]
group = do
  example <- exampleSource "fields.tung"
  library <- loadLibrary ["type/one.tung", "is.tung"]
  pure (tests library example)

tests :: Library -> String -> [Test]
tests library example =
  [ computes "a projection selecteth its field" "someone.name" "'tung'",
    computes "a value built from old fields" "older.eld" "+2",
    computes "projections chain leftward" "entry.who.eld" "+2",
    computes "a parameterised type projecteth at its argument" "pair.other" "+2",
    computes "a dependent field retaineth earlier fields" "entry.sure" "(reflect: 'x' = 'x')",
    computesSource
      "constructor-local implicit fields retain their positions and types"
      """
      type packed: * { pack: [@α: *, @tag: ℤ, value: α, sure: value = value, packed] }
      let item: packed ≔ pack @ℤ @+7 +1 reflect
      let value: ℤ ≔ item.value
      let sure: +1 = +1 ≔ item.sure
      """
      [("value", "+1"), ("sure", "(reflect: +1 = +1)")],
    computesSource
      "an implicit family parameter retaineth its plicity"
      """
      type wrapped: [@α: *, *] { wrap: [value: α, wrapped @α] }
      let item: wrapped @ℤ ≔ +2 wrap @ℤ
      let value: ℤ ≔ item.value
      """
      [("value", "+2")],
    computesSource
      "field names cannot capture generated accessor binders"
      """
      type holder: [field·value: *, *] {
        hold: [field·0: field·value, sure: field·0 = field·0, field·value holder]
      }
      let item: ℤ holder ≔ +3 hold reflect
      let value: ℤ ≔ item.field·0
      let sure: +3 = +3 ≔ item.sure
      """
      [("value", "+3"), ("sure", "(reflect: +3 = +3)")],
    computesSource
      "a dependent field may share a constructor's name"
      """
      type flag: * { yes: flag }
      type sample: * { sample_of: [yes: ℤ, sure: yes = yes, sample] }
      let item: sample ≔ +4 sample_of reflect
      let value: ℤ ≔ item.yes
      let sure: +4 = +4 ≔ item.sure
      """
      [("value", "+4"), ("sure", "(reflect: +4 = +4)")],
    computesSource
      "nested constructor brackets retain names and ordinary shadowing"
      """
      type nested: * { nested_of: [value: ℤ, [value: string, sure: value = value, nested]] }
      let item: nested ≔ +1 nested_of 'last' reflect
      let value: string ≔ item.value
      let sure: 'last' = 'last' ≔ item.sure
      """
      [("value", "'last'"), ("sure", "(reflect: 'last' = 'last')")],
    rejectContaining "a missing field cannot be projected" "hath no field 'height'" $
      extended "let bad ≔ someone.height ",
    rejectContaining "a type of two constructors hath no fields" "hath no field 'x'" $
      extended "type either: * { left: [x: ℤ, either], right: [x: ℤ, either] } let bad ≔ (+1 left).x ",
    rejectContaining "an indexed type hath no fields" "hath no field 'n'" $
      extended "type by_manyhood: [ℤ, *] { by_manyhood_of: [n: ℤ, n by_manyhood] } let bad ≔ (+1 by_manyhood_of).n ",
    rejectContaining "an accessor's hidden name cannot be written" "hath no field 'name'" $
      extended "let bad ≔ someone wight.name ",
    expectEq "an importer projecteth a shown type's fields" (Right True) do
      let shown = withModules [("people.tung", "show type wight: * { wight_of: [name: string, eld: ℤ, wight] } ")] library
      program <- compileWith shown "importer.tung" "bring people.tung let someone: wight ≔ 'tung' wight_of +1 let name: string ≔ someone.name "
      sameNormalIn program "name" "'tung'",
    expectEq "the runner projecteth fields" (Right (Right 0, "tung")) $
      compileWith library "dependent_fields.tung" (example ++ "bring type/one.tung let write:[string, 𝟙 effect] ≔ 'write' foreign let main:𝟙 effect ≔ someone.name write ")
        >>= (`runSimulated` [])
  ]
  where
    extended = compiled . (example ++)
    compiled source = compileWith library "dependent_fields.tung" ("bring is.tung " ++ source)
    computes label expression expected = expectEq label (Right True) do
      program <- compiled example
      sameNormalIn program expression expected

    computesSource label source expressions = expectEq label (Right (replicate (length expressions) True)) do
      program <- compiled source
      traverse (uncurry (sameNormalIn program)) expressions
