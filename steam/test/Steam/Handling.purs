-- | A module written in source whose values handle the operations they
-- | perform with handling expressions, compiled and loaded, and each value read
-- | as the machine holds it once the module is initialized: the front end's
-- | `handle`s, run.
-- |
-- | `asked` answers an operation with a `fast` clause, and `aborted` abandons
-- | the computation with a `full` one that never resumes. `choices` resumes
-- | twice and gathers the answers its return clause makes; `deep` performs
-- | again after resuming, under the same handler. `innerAbort` and
-- | `outerAbort` install the same two groups in either order, the first
-- | outermost. `viaItem` applies a handler written as a function to the thunk
-- | of the computation, `labelled` handles two instances of one effect, and
-- | `emitted` binds the arguments of an operation taking two. `ordered`
-- | performs an operation whose arguments perform, from the right.
module Test.Steam.Handling (spec) where

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
  , "data List a = Nil | Cons a (List a)"
  , "data Pair a b = Pair a b"
  , "effect Ask where"
  , "  ask :: Unit ->* Int"
  , "effect Abort where"
  , "  abort :: forall a. Unit ->* a"
  , "effect Choose where"
  , "  choose :: Unit ->* Boolean"
  , "effect State s where"
  , "  get :: Unit ->* s"
  , "  put :: s ->* Unit"
  , "effect Note where"
  , "  note :: Int ->* Int"
  , "effect Emit where"
  , "  emit :: Int -> Int ->* Unit"
  , "append :: forall a. List a -> List a -> List a"
  , "append xs ys = case xs of"
  , "  Nil -> ys"
  , "  Cons x rest -> Cons x (append rest ys)"
  , "asked :: Int"
  , "asked = handle ask () with"
  , "  Ask | fast ask _ -> 42"
  , "aborted :: List Int"
  , "aborted = handle Cons 1 (abort ()) with"
  , "  Abort | abort _ -> Nil"
  , "    | return xs -> Cons 0 xs"
  , "choices :: List Int"
  , "choices = handle (case choose () of"
  , "    true -> 1"
  , "    false -> 2) with"
  , "  Choose | choose _ -> append (resume true) (resume false)"
  , "    | return x -> Cons x Nil"
  , "deep :: List Int"
  , "deep = handle (case choose () of"
  , "    true -> case choose () of"
  , "      true -> 1"
  , "      false -> 2"
  , "    false -> 3) with"
  , "  Choose | choose _ -> append (resume true) (resume false)"
  , "    | return x -> Cons x Nil"
  , "innerAbort :: List Int"
  , "innerAbort = handle (case choose () of"
  , "    true -> ask ()"
  , "    false -> 0) with"
  , "  Choose | choose _ -> append (resume true) (resume false)"
  , "    | return x -> Cons x Nil"
  , "  Ask | ask _ -> 9"
  , "outerAbort :: List Int"
  , "outerAbort = handle (case choose () of"
  , "    true -> ask ()"
  , "    false -> 0) with"
  , "  Ask | ask _ -> Cons 9 Nil"
  , "  Choose | choose _ -> append (resume true) (resume false)"
  , "    | return x -> Cons x Nil"
  , "runAsk :: forall e. (Unit -> Int / {| Ask, ...e |}) -> Int / {| ...e |}"
  , "runAsk k = handle k () with"
  , "  Ask | fast ask _ -> 5"
  , "viaItem :: Int"
  , "viaItem = handle ask () with"
  , "  runAsk"
  , "labelled :: Pair Int Int"
  , "labelled = handle Pair (get@a ()) (get@b ()) with"
  , "  a fast | get _ -> 1"
  , "    | put _ -> ()"
  , "  b fast | get _ -> 2"
  , "    | put _ -> ()"
  , "emitted :: List Int"
  , "emitted = handle emit 1 2 with"
  , "  Emit | emit x y -> Cons x (Cons y Nil)"
  , "    | return _ -> Nil"
  , "ordered :: List Int"
  , "ordered = handle emit (note 1) (note 2) with"
  , "  Note | note n -> Cons n (resume n)"
  , "    | return _ -> Nil"
  , "  Emit | fast emit _ _ -> ()"
  ]

spec :: Spec Unit
spec = describe "Stella source handling what it performs, run on Steam" do
  it "answers an operation with a `fast` clause, and abandons the computation with a `full` one" do
    running source [ "asked", "aborted" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "asked" "42"
        , Tuple "aborted" "Nil"
        ]

  it "resumes more than once, and handles what the computation performs after resuming" do
    running source [ "choices", "deep" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "choices" "Cons(1, Cons(2, Nil))"
        , Tuple "deep" "Cons(1, Cons(2, Cons(3, Nil)))"
        ]

  it "installs its items from the top, the first outermost, a handler applied to the thunk of what is left" do
    running source [ "innerAbort", "outerAbort", "viaItem" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "innerAbort" "Cons(9, Cons(0, Nil))"
        , Tuple "outerAbort" "Cons(9, Nil)"
        , Tuple "viaItem" "5"
        ]

  it "handles the instance a label names, and binds an operation's arguments one by one" do
    running source [ "labelled", "emitted" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "labelled" "Pair(1, 2)"
        , Tuple "emitted" "Cons(1, Cons(2, Nil))"
        ]

  it "evaluates an operation's arguments from the right" do
    running source [ "ordered" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "ordered" "Cons(2, Cons(1, Nil))" ]
