-- | A module written in source that builds records and tuples and matches
-- | them, compiled and loaded, and each value read as the machine holds it
-- | once the module is initialized: the front end's `extend`, `select`,
-- | `update`, and `restrict`, and its record occurrences, run.
-- |
-- | `point` is a record literal and `pair` a tuple; `moved` replaces a field
-- | of a record spread and `labelled` extends one, both through functions open
-- | in the rest of the row; `retyped` replaces a field at a type of its own and
-- | `replacedTwice` two fields, and `ordered` writes extensions and replacements
-- | around each other. `firstOf` matches a tuple in a `case`, `swapped` one a
-- | parameter is written as, and `yOf` a record pattern a `let` binds;
-- | `rested` binds the rest of a record; `some` and `none` dispatch within a
-- | field; and `kept` and `replacedRest` pass a rest to the join point of an
-- | alternative several leaves take.
module Test.E2E.Records (spec) where

import Prelude

import Prim as P

import Data.Map as Map
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import E2E.Build (Sources)
import Test.E2E.Running (running)

spec :: Sources -> Spec Unit
spec sources = describe "Steam, records and tuples compiled from source" do
  it "builds, selects, replaces, and extends records, and builds tuples" do
    running sources [ "records" ] [ "point", "pair", "xOf", "moved", "labelled", "retyped", "replacedTwice", "ordered", "nested" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "point" "{x: 1, y: 2}"
        , Tuple "pair" "{0: 3, 1: true}"
        , Tuple "xOf" "1"
        , Tuple "moved" "{x: 5, y: 2}"
        , Tuple "labelled" "{name: 7, x: 1, y: 2}"
        , Tuple "retyped" "{x: 1, y: false}"
        , Tuple "replacedTwice" "{x: 10, y: false}"
        , Tuple "ordered" "{a: 1, b: 2, x: 10, y: 20}"
        , Tuple "nested" "2"
        ]

  it "matches records and tuples, binding their fields and the rest of a record" do
    running sources [ "records" ] [ "firstOf", "swapped", "yOf", "rested", "some", "none", "kept", "replacedRest" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "firstOf" "3"
        , Tuple "swapped" "{0: true, 1: 3}"
        , Tuple "yOf" "2"
        , Tuple "rested" "{z: 3}"
        , Tuple "some" "4"
        , Tuple "none" "0"
        , Tuple "kept" "{y: 2}"
        , Tuple "replacedRest" "{y: 0}"
        ]
