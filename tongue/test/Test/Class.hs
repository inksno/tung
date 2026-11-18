-- classes are dictionary families; bizens are found by instance search.
module Test.Class (group) where

import Data.Map.Strict qualified as Map
import Test.Compile (compileProject)
import Test.Harness (Test, expectEq)
import Test.Support
import Tung.Core
import Tung.Source (SourceProgram, sorryAssumptions, typeOfName)

group :: IO [Test]
group = do
  example <- exampleSource "classes.tung"
  pure (tests example ++ selectionTests ++ constructionTests)

tests :: String -> [Test]
tests example =
  [ computes "a bizen supplieth a member" "yea ≍ nay" "nay",
    computes "a requirement passeth the caller's bizen" "yea ≭ nay" "yea",
    computes "a bizen solveth its own requirement" "(yea some) ≍ (nay some)" "nay",
    computes "nested requirements compute" "(yea some) ≍ (yea some)" "yea",
    computes "a direct bizen outranketh a parent path" "(yea some) map {x ^ x}" "yea some",
    normalisesTo "a parent cometh from a child requirement" (extended "let lifted:𝟚 optional ≔ yea lift {x ^ x} ") "lifted" "yea some",
    normalisesTo "a declaration may precede what it useth" (compiled ("let early:𝟚 ≔ yea ≭ nay " ++ example)) "early" "yea",
    normalisesTo
      "a call of an imported function that requireth a class waiteth for the module's bizen"
      ( compileProject
          (SourceModule "main.tung")
          "bring named.tung let early:box ≔ chosen type box:* { make:box } bizen:box named { let name ≔ make } "
          (Map.singleton "named.tung" "show class named:[α:*, *] { let name:α } show let chosen:[@α:*, @:α named, α] ≔ name ")
      )
      "early"
      "make",
    normalisesTo
      "a shown class, its laws and bizens cross modules"
      (compileProject (SourceModule "main.tung") "bring is.tung let proof:(nay ≍ nay) = yea ≔ nay ≍_reflect bring same.tung let hath_≍:𝟚 ≔ nay ≍ nay " (Map.fromList [("same.tung", "bring is.tung " ++ shown), ("is.tung", equalitySource)]))
      "hath_≍"
      "yea",
    normalisesTo
      "a rejected candidate doth not affect a later bizen"
      ( compiled
          """
          type box:[α:*, *] { box_value:[α, α box] }
          class provided:[α:*, *] { let get:α }
          bizen:(ℕ box) provided { let get ≔ 0 box_value }
          bizen:(string box) provided { let get ≔ 'ok' box_value }
          let answer:string box ≔ get
          """
      )
      "answer"
      "'ok' box_value",
    rejectContaining "a bizen needeth every member" "bizen is missing member 'two'" $
      extended (pair ++ "bizen:𝟚 pair { let one ≔ yea } "),
    rejectContaining "a bizen cannot add members" "'three' is not a member" $
      extended (pair ++ "bizen:𝟚 pair { let one ≔ yea let two ≔ yea let three ≔ yea } "),
    rejectContaining "a missing bizen is reported" "no bizen of class 'hath_≍'" $
      extended "type unit:* { only: unit } let bad:𝟚 ≔ only ≍ only ",
    rejectContaining "a second bizen of one type is rejected" "a bizen with the same type already exists" $
      extended "bizen:𝟚 hath_≍ { let ≍ ≔ {_, _ ^ yea} let ≍_reflect ≔ sorry } ",
    -- neither module seeth the other's bizen, so bring order must not choose.
    rejectContaining "bizens of one type from two imports are rejected" "bizens of class 'pointed' from" $
      compileProject
        (SourceModule "both.tung")
        "bring left.tung bring right.tung "
        ( Map.fromList
            [ ("pointed.tung", "show type two:* { yea:two, nay:two } show class pointed:[α:*, *] { let point:α } "),
              ("left.tung", "bring pointed.tung bizen:two pointed { let point ≔ yea } "),
              ("right.tung", "bring pointed.tung bizen:two pointed { let point ≔ nay } ")
            ]
        ),
    rejectContaining "a member must have its declared type" "in bizen of" $
      extended "bizen:(𝟚 optional) optional hath_≍ { let ≍ ≔ yea let ≍_reflect ≔ sorry } ",
    rejectContaining "a bizen defineth each law" "bizen is missing member '≍_reflect'" $
      extended "type unit:* { only: unit } bizen:unit hath_≍ { let ≍ ≔ {_, _ ^ yea} } ",
    rejectContaining "a law proof is checked against the bizen's members" "cannot unify nay with yea" $
      extended "type unit:* { only: unit } bizen:unit hath_≍ { let ≍ ≔ {_, _ ^ nay} let ≍_reflect ≔ {_ ^ reflect} } ",
    rejectContaining "an ascribed sorry law must still have its declared type" "cannot unify string with" $
      extended "type unit:* { only:unit } bizen:unit hath_≍ { let ≍ ≔ {_, _ ^ yea} let ≍_reflect:string ≔ sorry }",
    normalisesTo
      "a bizen may define a parent that hath no bizen"
      (extended "type _box:[α:*, *] { box:[α, α _box] } bizen:_box applicative { let map ≔ {a box, f ^ (a f) box} let pure ≔ {a ^ a box} } let boxed:𝟚 _box ≔ (yea box) map {x ^ x} ")
      "boxed"
      "yea box",
    accepts "a law proof may match in its proposition" $
      compiled
        """
        type box:[α:*, *] { wrap:[α, α box] }
        class reflexive:[α:*, *] {
          let rule:[left:α box, right:α box, match left, right { x wrap, y wrap ^ x = x }]
        }
        bizen:ℤ reflexive { let rule ≔ { x wrap, y wrap ^ reflect } }
        let proof:+1 = +1 ≔ (+1 wrap) rule (+2 wrap)
        """,
    rejectContaining "both law sides share one type" "cannot unify 𝟚 with" $
      extended "class bad:[α:*, *] { let f:[α, α] let rule:[x:α, (x f) = yea] } ",
    rejectContaining "requirements precede bare slots" "must precede bare slots" $
      extended "let bad:[𝟚, @:𝟚 hath_≍, 𝟚] ≔ {x ^ x} ",
    rejectContaining "an implicit class parameter is a requirement" "written @name:class" $
      extended "class bad:[@α:*, *] { let f:[α, α] } ",
    -- a named requirement is a parameter found where the class is applied, so
    -- a law about it meeteth the caller's own dictionary; a parent is a field
    -- of each dictionary, which a caller's dictionary is not.
    normalisesTo "a named requirement is shared with the caller" (compiled (sharing "@basis:α base")) "concrete" "reflect @unit @only",
    rejectContaining "a parent is not the caller's dictionary" "cannot unify" $
      compiled (sharing "@:α base")
  ]
  where
    extended = compiled . (example ++)
    pair = "class pair:[α:*, *] { let one:α let two:α } "
    sharing requirement =
      "type unit:* { only:unit } class base:[α:*, *] { let tag:α } class held:[α:*,"
        ++ requirement
        ++ ", *] { let kept:(tag:α) = tag } bizen:unit base { let tag ≔ only } bizen:unit held { let kept ≔ reflect } let shared:[@α:*, @:α base, @:α held, (tag:α) = tag] ≔ kept let concrete:(tag:unit) = only ≔ kept"
    shown =
      """
      show type 𝟚:* { yea: 𝟚, nay: 𝟚 }
      show class hath_≍:[α:*, *] { let ≍:[α, α, 𝟚] let ≍_reflect:[x:α, (x ≍ x) = yea] }
      bizen:𝟚 hath_≍ {
        let ≍ ≔ { yea, yea; nay, nay ^ yea, _, _ ^ nay }
        let ≍_reflect ≔ { yea; nay ^ reflect }
      }
      """
    computes label = normalisesTo label (compiled example)

selectionTests :: [Test]
selectionTests =
  [ -- a class with two parents of one class projecteth the one that fitteth,
    -- and either of two requirements reaching one parent serveth.
    accepts "a child's second parent of one class is projected" $
      compiled
        """
        class base:[α:*, *] { let tag:α }
        class pair:[α:*, β:*, @:α base, @:β base, *] {}
        let second_tag:[@α:*, @β:*, @:α pair β, β] ≔ tag
        let shared_tag:[@α:*, @β:*, @γ:*, @:α pair γ, @:β pair γ, γ] ≔ tag
        """,
    -- as in lean, the latest of equal-priority bizens is tried first.
    expectEq "the latest matching bizen is chosen" (Right [True, True]) $
      traverse (\(instances, expected) -> compiled (choice ++ instances) >>= \program -> sameNormalIn program "selected @ℤ @ℤ" expected) [(blanket ++ repeated, "+1"), (repeated ++ blanket, "+0")],
    normalisesTo "a written priority outranketh declaration order" (compiled (choice ++ "bizen 2000:[@α:*, α choice α] { let selected ≔ +1 } " ++ blanket)) "selected @ℤ @ℤ" "+1",
    normalisesTo "a fallback bizen fixeth a carrier that only it fiteth" (compiled (marker "bizen fallback")) "value" "+7",
    rejectContaining "without a fallback, a carrier that only one bizen fiteth stayeth unknown" "still unknown" $ compiled (marker "bizen"),
    -- `?g x = k x equal` waiteth on `equal`'s dictionary. its first-order split
    -- `?g = k x` is ill-typed, so it is undone, and the fallback's
    -- dictionary letteth `?g` be abstracted.
    accepts "an ill-typed approximation leaveth its equation to a fallback bizen" $
      compiled
        """
        let →:[α:*, β:*, *] ≔ [α, β]
        class marker:[φ:[*, *, *], *] { let same:[@α:*, α φ α] }
        bizen fallback:→ marker { let same: [a:] ≔ a }
        let pointwise:[@α:*, @β:*, x:α, @f:[α, β], @g:[α, β], each:[a:α, (a f) = (a g)], (x f) = (x g)] ≔ x each
        let probe:[x:ℤ, k:[ℤ, [ℤ, ℤ], ℤ], (x {p ^ p k same}) = (x {p ^ p k same})] ≔ x pointwise {p ^ reflect}
        """,
    normalisesTo
      "the innermost local dictionary outranketh a global instance"
      (compiled "class tag:[α:*, *] { let value:ℤ } bizen:ℤ tag { let value ≔ +0 } let choose:[outer:ℤ tag, inner:ℤ tag, ℤ] ≔ value @ℤ")
      "(+1 tag_make) choose (+2 tag_make)"
      "+2",
    normalisesAll
      "a dictionary's private identity cannot capture source names"
      ( compiled
          """
          class tag:[α:*, *] { let value:ℤ }
          let bizen_1 ≔ +10
          bizen:ℤ tag { let value ≔ +1 }
          let bizen_0 ≔ +20
          let answer:ℤ ≔ value @ℤ
          """
      )
      [("bizen_1", "+10"), ("bizen_0", "+20"), ("answer", "+1")],
    expectEq "a law assumed with sorry is reported, a proved one is not" (Right ["bizen unit second"]) $
      sorryAssumptions <$> compiled (lawClasses ++ firstInstance ++ "bizen:unit second { let right ≔ {_ ^ yea} let rule_right ≔ sorry }"),
    -- a law is an ordinary member, so its name is a top-level accessor.
    rejectContaining "two classes cannot share a law name" "top-level name repeateth 'rule'" $
      compiled (lawClasses ++ "class third:[α:*, *] { let rule:[x:α, x = x] }"),
    accepts "a law is projected like any other member" $ compiled (lawClasses ++ firstInstance ++ "let proof:[(only left) = yea] ≔ rule @unit only"),
    normalisesTo
      "an inline parent's law useth the projected dictionary and its arguments"
      ( compiled
          """
          type box:[α:*, *] { wrap:[α, α box] }
          class parent:[α:*, *] { let keep:[α, α] let rule:[x:α, (x keep) = x] }
          class child:[α:*, @:(α box) parent, *] { let tag:ℕ }
          bizen:[@α:*, α child] { let keep:[x:] ≔ x let rule ≔ {_ ^ reflect} let tag ≔ 0 }
          """
      )
      "(+1 wrap) keep"
      "+1 wrap",
    expectEq "generated dictionary binders cannot capture type parameters" (Right [True, True, True]) $
      traverse
        ( \parameter -> do
            program <- compiled ("class parent:[α:*, *] { let get:α } class tag:[" ++ parameter ++ ":*, @:" ++ parameter ++ " parent, *] { let value:" ++ parameter ++ " } bizen:ℤ parent { let get ≔ +1 } bizen:ℤ tag { let value ≔ +2 }")
            sameNormalIn program "value @ℤ" "+2"
        )
        ["dictionary", "parent_1", "field_value"],
    -- a member that nameth itself useth the class, as any visible name doth; as
    -- in lean, a recursive member is an ordinary recursive let.
    rejectContaining "a member naming itself refereth to the class" "no bizen of class 'count'" $
      compiled (countClass ++ "bizen:ℕ count { let length:[ℕ, ℕ] ≔ { 0 ^ 0, n next ^ (n length) next } }"),
    normalisesTo "a recursive member is a recursive let" (compiled (countClass ++ "let natural_length:[ℕ, ℕ] ≔ { 0 ^ 0, n next ^ (n natural_length) next } bizen:ℕ count { let length ≔ natural_length }")) "2 length" "2",
    -- `* out` letth search find a parameter, as lean's `outParam` doth; an
    -- unknown input parameter leaveth the goal waiting.
    expectEq "an output parameter is found by instance search" (Right "string") $
      compiled (converting " out") >>= (`typeOfName` "value"),
    rejectContaining "an unknown input parameter leaveth its goal unsolved" "still unknown" $ compiled (converting ""),
    normalisesTo "incomparable matching bizens follow declaration order" (compiled (choice ++ "bizen:[@α:*, ℤ choice α] { let selected ≔ +1 } bizen:[@α:*, α choice ℤ] { let selected ≔ +2 } let answer:ℤ ≔ selected @ℤ @ℤ")) "answer" "+2",
    accepts "a nested requirement left open faileth its candidate rather than waiting" $
      compiled
        """
        class named:[α:*, *] { let name:α }
        class base:[α:*, *] {}
        bizen:[@α:*, @:α base, α named] { let name ≔ sorry }
        class carrying:[ρ:*, μ:*, @:ρ base, @:μ named, *] {}
        let pick:[@ρ:*, @μ:*, @:ρ carrying μ, μ] ≔ name
        """,
    rejectContaining "a candidate cannot require its own goal" "cyclic instance search" $
      compiled
        """
        class loop:[α:*, *] { let value:α }
        bizen:[@α:*, @:α loop, α loop] { let value ≔ value }
        let answer:ℤ ≔ value
        """
  ]
  where
    lawClasses =
      """
      type truth:* { yea:truth, nay:truth }
      type unit:* { only:unit }
      class first:[α:*, *] { let left:[α, truth] let rule:[x:α, (x left) = yea] }
      class second:[α:*, *] { let right:[α, truth] let rule_right:[x:α, (x right) = yea] }

      """
    firstInstance = "bizen:unit first { let left ≔ {_ ^ yea} let rule ≔ {_ ^ reflect} }"
    countClass = "class count:[α:*, *] { let length:[α, ℕ] }"
    choice = "class choice:[α:*, β:*, *] { let selected:ℤ }"
    converting output = "class convert:[α:*, β:*" ++ output ++ ", *] { let into:[α, β] } bizen:ℤ convert string { let into: [_:] ≔ 'one' } let value ≔ +1 into"
    blanket = "bizen:[@α:*, @β:*, α choice β] { let selected ≔ +0 }"
    repeated = "bizen:[@α:*, α choice α] { let selected ≔ +1 }"
    marker kind = "let →:[α:*, β:*, *] ≔ [α, β] class marker:[φ:[*, *, *], *] { let mark:[@α:*, α φ α, ℤ] } " ++ kind ++ ":→ marker { let mark: [_:] ≔ +7 } let value:ℤ ≔ ({x ^ x}:[ℤ, ℤ]) mark"

constructionTests :: [Test]
constructionTests =
  [ normalisesTo
      "a bizen may reuse an ordinary dictionary defined before its class"
      (compiled "let dictionary ≔ 7 tag_make class tag:* { let value:ℕ } let read_value:[dictionary:tag, ℕ] ≔ value bizen:tag { let value ≔ dictionary read_value } let answer:ℕ ≔ value")
      "answer"
      "7",
    normalisesTo
      "named members supply an ordinary dictionary and its dependent law"
      (compiled "class stable:[α:*, *] { let keep:[α, α] let rule:[x:α, (x keep) = x] } bizen:[@α:*, α stable] { let keep:[x:] ≔ x let rule:[x:] ≔ reflect } let proof:3 = 3 ≔ 3 rule")
      "proof"
      "(reflect:3 = 3)",
    normalisesTo
      "dictionary fields may supply a type, its value, and a dependent proof"
      (compiled "class chosen:* { let carrier:* let item:carrier let rule:item = item } bizen:chosen { let rule ≔ reflect let item ≔ 3 let carrier ≔ ℕ } let proof:3 = 3 ≔ rule")
      "proof"
      "(reflect:3 = 3)"
  ]

compiled :: String -> Either String SourceProgram
compiled = compileWithEquality "dependent_classes.tung"
