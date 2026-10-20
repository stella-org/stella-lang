-- | A module written in source whose handling expressions declare cells,
-- | compiled and loaded, and each value read as the machine holds it once the
-- | module is initialized: the front end's regions, run.
-- |
-- | `counted` counts with a cell its `fast` clause reads and writes, and
-- | `stated` keeps a state in one; `shared` has two groups of one expression
-- | reach one cell. `copied` resumes twice a choice handled outside the region,
-- | each resumption on a copy of the cell, and `kept` the same choice handled
-- | inside it, both on the one cell: the resumption with `false`, an argument
-- | evaluated first, leaves the cell for the one with `true` to read. `apart` applies a function declaring a
-- | cell of its own as an item of an expression declaring one of the same name,
-- | neither reaching the other's; `reached` calls, in a clause of an inner
-- | expression whose cell hides the outer one's name, a function an outer
-- | clause made over the outer cell, which it reaches.
module Test.E2E.Cells (spec) where

import Prelude

import Prim as P

import Data.Map as Map
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import E2E.Build (Sources)
import Test.E2E.Running (running)

spec :: Sources -> Spec Unit
spec sources = describe "Stella source declaring cells, run on Steam" do
  it "reads and writes a cell from a clause, and keeps a state in one" do
    running sources [ "cells" ] [ "counted", "stated" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "counted" "Cons(Z, Cons(S(Z), Cons(S(S(Z)), Nil)))"
        , Tuple "stated" "S(S(Z))"
        ]

  it "shares a cell between the groups of one expression" do
    running sources [ "cells" ] [ "shared" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "shared" "Pair(S(S(Z)), S(S(Z)))" ]

  it "copies a cell for each resumption of a handler outside its region, and shares it with one inside" do
    running sources [ "cells" ] [ "copied", "kept" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "copied" "Cons(Z, Cons(Z, Nil))"
        , Tuple "kept" "Cons(S(Z), Cons(Z, Nil))"
        ]

  it "keeps the cells of a function applied as an item apart, and reaches an outer cell from an inner clause" do
    running sources [ "cells" ] [ "apart", "reached" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "apart" "Pair(Z, S(S(Z)))"
        , Tuple "reached" "S(Z)"
        ]
