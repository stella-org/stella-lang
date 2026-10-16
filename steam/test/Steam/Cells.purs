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
module Test.Steam.Cells (spec) where

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
  , "data Nat = Z | S Nat"
  , "data List a = Nil | Cons a (List a)"
  , "data Pair a b = Pair a b"
  , "effect Tick where"
  , "  tick :: Unit ->* Nat"
  , "effect Peek where"
  , "  peek :: Unit ->* Nat"
  , "effect Ask where"
  , "  ask :: Unit ->* Nat"
  , "effect State s where"
  , "  get :: Unit ->* s"
  , "  put :: s ->* Unit"
  , "effect Choose where"
  , "  choose :: Unit ->* Boolean"
  , "append :: forall a. List a -> List a -> List a"
  , "append xs ys = case xs of"
  , "  Nil -> ys"
  , "  Cons x rest -> Cons x (append rest ys)"
  , "counted :: List Nat"
  , "counted = handle (let a = tick () in let b = tick () in let c = tick () in Cons a (Cons b (Cons c Nil))) with"
  , "  var n := Z"
  , "  Tick fast | tick _ -> let v = n! in let _ = n := S v in v"
  , "stated :: Nat"
  , "stated = handle (let _ = put (S Z) in let x = get () in let _ = put (S x) in get ()) with"
  , "  var s := Z"
  , "  State fast | get _ -> s!"
  , "    | put v -> s := v"
  , "shared :: Pair Nat Nat"
  , "shared = handle (let _ = tick () in let _ = tick () in let a = peek () in let b = peek () in Pair a b) with"
  , "  var n := Z"
  , "  Tick fast | tick _ -> let v = n! in let _ = n := S v in v"
  , "  Peek fast | peek _ -> n!"
  , "withState :: forall a. (Unit -> a / {| State Nat, Choose |}) -> a / {| Choose |}"
  , "withState k = handle k () with"
  , "  var s := Z"
  , "  State fast | get _ -> s!"
  , "    | put v -> s := v"
  , "copied :: List Nat"
  , "copied = handle withState (\\_ -> let _ = choose () in let x = get () in let _ = put (S x) in Cons x Nil) with"
  , "  Choose | choose _ -> append (resume true) (resume false)"
  , "kept :: List Nat"
  , "kept = handle (let _ = choose () in let x = get () in let _ = put (S x) in Cons x Nil) with"
  , "  var s := Z"
  , "  State fast | get _ -> s!"
  , "    | put v -> s := v"
  , "  Choose | choose _ -> append (resume true) (resume false)"
  , "runCounter :: forall a e. (Unit -> a / {| Tick, ...e |}) -> a / {| ...e |}"
  , "runCounter k = handle k () with"
  , "  var n := Z"
  , "  Tick fast | tick _ -> let v = n! in let _ = n := S v in v"
  , "apart :: Pair Nat Nat"
  , "apart = handle (let a = tick () in let b = peek () in Pair a b) with"
  , "  var n := S (S Z)"
  , "  runCounter"
  , "  Peek fast | peek _ -> n!"
  , "reached :: Nat"
  , "reached = handle ask () with"
  , "  var c := S Z"
  , "  Ask fast | ask _ -> let outer = \\_ -> c! in handle ask () with"
  , "      var c := Z"
  , "      Ask fast | ask _ -> outer ()"
  ]

spec :: Spec Unit
spec = describe "Stella source declaring cells, run on Steam" do
  it "reads and writes a cell from a clause, and keeps a state in one" do
    running source [ "counted", "stated" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "counted" "Cons(Z, Cons(S(Z), Cons(S(S(Z)), Nil)))"
        , Tuple "stated" "S(S(Z))"
        ]

  it "shares a cell between the groups of one expression" do
    running source [ "shared" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "shared" "Pair(S(S(Z)), S(S(Z)))" ]

  it "copies a cell for each resumption of a handler outside its region, and shares it with one inside" do
    running source [ "copied", "kept" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "copied" "Cons(Z, Cons(Z, Nil))"
        , Tuple "kept" "Cons(S(Z), Cons(Z, Nil))"
        ]

  it "keeps the cells of a function applied as an item apart, and reaches an outer cell from an inner clause" do
    running source [ "apart", "reached" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "apart" "Pair(Z, S(S(Z)))"
        , Tuple "reached" "S(Z)"
        ]
