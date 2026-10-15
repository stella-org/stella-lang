-- | A module written in source that builds records and tuples, compiled and
-- | loaded, and each value read as the machine holds it once the module is
-- | initialized: the front end's `extend`, `select`, and `update`, run.
-- |
-- | `point` is a record literal and `pair` a tuple; `moved` replaces a field
-- | of a record spread and `labelled` extends one, both through functions open
-- | in the rest of the row; `retyped` replaces a field at a type of its own and
-- | `replacedTwice` two fields, and `ordered` writes extensions and replacements
-- | around each other.
module Test.Steam.Records (spec) where

import Prelude

import Prim as P

import Data.Map as Map
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Steam.Compiled (running)

source :: P.Array P.String
source =
  [ "module Main where"
  , "point = { x: 1, y: 2 }"
  , "pair = (3, true)"
  , "getX r = r.x"
  , "setX n r = { x = n, ...r }"
  , "label r = { name: 7, ...r }"
  , "xOf = getX point"
  , "moved = setX 5 point"
  , "labelled = label point"
  , "retyped = { y = false, ...point }"
  , "replacedTwice = { x = 10, y = false, ...point }"
  , "ordered = { a: 1, x = 10, b: 2, y = 20, ...point }"
  , "nested = { inner: point }.inner.y"
  ]

spec :: Spec Unit
spec = describe "Steam, records and tuples compiled from source" do
  it "builds, selects, replaces, and extends records, and builds tuples" do
    running source [ "point", "pair", "xOf", "moved", "labelled", "retyped", "replacedTwice", "ordered", "nested" ] \values ->
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
