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
module Test.E2E.Handling (spec) where

import Prelude

import Prim as P

import Data.Map as Map
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import E2E.Build (Sources)
import Test.E2E.Running (running)

spec :: Sources -> Spec Unit
spec sources = describe "Stella source handling what it performs, run on Steam" do
  it "answers an operation with a `fast` clause, and abandons the computation with a `full` one" do
    running sources [ "handling" ] [ "asked", "aborted" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "asked" "42"
        , Tuple "aborted" "Nil"
        ]

  it "resumes more than once, and handles what the computation performs after resuming" do
    running sources [ "handling" ] [ "choices", "deep" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "choices" "Cons(1, Cons(2, Nil))"
        , Tuple "deep" "Cons(1, Cons(2, Cons(3, Nil)))"
        ]

  it "installs its items from the top, the first outermost, a handler applied to the thunk of what is left" do
    running sources [ "handling" ] [ "innerAbort", "outerAbort", "viaItem" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "innerAbort" "Cons(9, Cons(0, Nil))"
        , Tuple "outerAbort" "Cons(9, Nil)"
        , Tuple "viaItem" "5"
        ]

  it "handles the instance a label names, and binds an operation's arguments one by one" do
    running sources [ "handling" ] [ "labelled", "emitted" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "labelled" "Pair(1, 2)"
        , Tuple "emitted" "Cons(1, Cons(2, Nil))"
        ]

  it "evaluates an operation's arguments from the right" do
    running sources [ "handling" ] [ "ordered" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "ordered" "Cons(2, Cons(1, Nil))" ]
