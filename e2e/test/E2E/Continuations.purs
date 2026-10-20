-- | A module written in source whose handling expressions reify the
-- | continuations they capture, compiled after `Base.Continuation`, which it
-- | imports, both loaded into one store, and each value read as the machine
-- | holds it once the module is initialized: the front end's `reifiable full`
-- | clauses, run.
-- |
-- | `chosen` resumes a choice twice with `resume`, and `reified` the same with
-- | `Continuation.continue` on the continuation it reifies. `generated` takes a
-- | continuation out of the handling expression as part of its answer and
-- | resumes it after the expression has given that answer, each resumption
-- | handled by the same handler again.
module Test.E2E.Continuations (spec) where

import Prelude

import Prim as P

import Data.Map as Map
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import E2E.Build (Sources)
import Test.E2E.Running (running)

spec :: Sources -> Spec Unit
spec sources = describe "Stella source reifying the continuations it captures, run on Steam" do
  it "resumes, with `Continuation.continue` in the clause, as a `full` clause resumes with `resume`" do
    running sources [ "continuations" ] [ "chosen", "reified" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "chosen" "Cons(1, Cons(2, Nil))"
        , Tuple "reified" "Cons(1, Cons(2, Nil))"
        ]

  it "resumes a continuation taken out of the handling expression after it has answered, under the same handler" do
    running sources [ "continuations" ] [ "generated" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "generated" "Cons(1, Cons(2, Cons(3, Nil)))" ]
