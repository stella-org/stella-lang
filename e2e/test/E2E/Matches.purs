-- | A module written in source whose values match with `case`, compiled and
-- | loaded, and each value read as the machine holds it once the module is
-- | initialized: the front end's decision trees and join points, run.
-- |
-- | `rank` dispatches on a data type with an or-pattern; `second` on a nested
-- | constructor with a default; `classify` on two values, a literal among
-- | them, its second alternative taken by two leaves and so a join point
-- | binding `n`; `named` on an open domain of strings; and `flip` on a
-- | `Boolean` its alternatives exhaust. `guarded` binds a name in a guard block
-- | and falls through to the alternative after it where its guard fails, and
-- | `sizeOf` ends its block with `otherwise`; `layered` falls through two
-- | guard blocks in turn. `first` and `unwrap` match a parameter written as a
-- | pattern, `secondOf` a pattern a `let` binds, `split` one a guard block
-- | binds, and `rankOf` is a `case _ of`. `area` dispatches on the tags of a
-- | closed variant, `'Dot` carrying `()`, and `bump` hands on the variant its
-- | default holds whole, widened back by the tag it took; `temperature` writes no
-- | type, and its `case` closes the row of the variant it matches.
module Test.E2E.Matches (spec) where

import Prelude

import Prim as P

import Data.Map as Map
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import E2E.Build (Sources)
import Test.E2E.Running (running)

spec :: Sources -> Spec Unit
spec sources = describe "Steam, a `case` compiled from source" do
  it "tries a guard block's guards in order, falling through to the alternatives after it where every one fails" do
    running sources [ "matches" ] [ "guardZero", "guardFive", "guardNone", "sizeZero", "sizeTwo" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "guardZero" "100"
        , Tuple "guardFive" "5"
        , Tuple "guardNone" "7"
        , Tuple "sizeZero" "0"
        , Tuple "sizeTwo" "1"
        ]

  it "falls through two guard blocks in turn to the alternative after both" do
    running sources [ "matches" ] [ "layeredZero", "layeredOne", "layeredFive", "layeredNone" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "layeredZero" "0"
        , Tuple "layeredOne" "1"
        , Tuple "layeredFive" "2"
        , Tuple "layeredNone" "2"
        ]

  it "matches a pattern a parameter, a `let`, or a guard block's binding is written as, and a `case _ of` applied" do
    running sources [ "matches" ] [ "firstOf", "unwrapped", "secondOfPair", "splitZero", "splitOne", "rankOfRed", "rankOfBlue", "lambda" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "firstOf" "5"
        , Tuple "unwrapped" "7"
        , Tuple "secondOfPair" "8"
        , Tuple "splitZero" "9"
        , Tuple "splitOne" "1"
        , Tuple "rankOfRed" "10"
        , Tuple "rankOfBlue" "20"
        , Tuple "lambda" "4"
        ]

  it "takes the alternative its value matches, through an or-pattern, a nested constructor, a join point, and a literal" do
    running sources [ "matches" ] [ "rankRed", "rankBlue", "secondOfTwo", "secondOfOne", "redZero", "redFour", "blueFour", "greenNone", "two", "other", "flipped" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "rankRed" "1"
        , Tuple "rankBlue" "2"
        , Tuple "secondOfTwo" "Just(2)"
        , Tuple "secondOfOne" "Nothing"
        , Tuple "redZero" "0"
        , Tuple "redFour" "4"
        , Tuple "blueFour" "4"
        , Tuple "greenNone" "9"
        , Tuple "two" "2"
        , Tuple "other" "0"
        , Tuple "flipped" "false"
        ]

  it "injects a tag's payload, dispatches on the tag, and hands on the variant a default holds whole" do
    running sources [ "matches" ] [ "circle", "dot", "bumped", "kept" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "circle" "3"
        , Tuple "dot" "0"
        , Tuple "bumped" "'Up(0)"
        , Tuple "kept" "'Down(7)"
        ]

  it "dispatches on a variant whose row the match itself closes" do
    running sources [ "matches" ] [ "cold" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "cold" "2" ]
