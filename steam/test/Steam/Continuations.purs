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
module Test.Steam.Continuations (spec) where

import Prelude

import Prim as P

import Data.Map as Map
import Data.Tuple (Tuple(..))
import Effect.Class (liftEffect)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Steam.Compiled (runningAfter)
import Test.Steam.Sources (continuationSource)

source :: P.Array P.String
source =
  [ "module Main where"
  , "import Base.Continuation as Continuation"
  , "data List a = Nil | Cons a (List a)"
  , "data Step = Done | Yielded Int (Continuation.Continuation Unit Step {||})"
  , "effect Choose where"
  , "  choose :: Unit ->* Boolean"
  , "effect Yield where"
  , "  yield :: Int ->* Unit"
  , "append :: forall a. List a -> List a -> List a"
  , "append xs ys = case xs of"
  , "  Nil -> ys"
  , "  Cons x rest -> Cons x (append rest ys)"
  , "chosen :: List Int"
  , "chosen = handle (case choose () of"
  , "    true -> 1"
  , "    false -> 2) with"
  , "  Choose | choose _ -> append (resume true) (resume false)"
  , "    | return x -> Cons x Nil"
  , "reified :: List Int"
  , "reified = handle (case choose () of"
  , "    true -> 1"
  , "    false -> 2) with"
  , "  Choose reifiable full | choose _ k -> append (Continuation.continue k true) (Continuation.continue k false)"
  , "    | return x -> Cons x Nil"
  , "generate :: Unit -> Step"
  , "generate _ = handle (let a = yield 1 in let b = yield 2 in yield 3) with"
  , "  Yield reifiable full | yield n k -> Yielded n k"
  , "    | return _ -> Done"
  , "collect :: Step -> List Int"
  , "collect s = case s of"
  , "  Done -> Nil"
  , "  Yielded n k -> Cons n (collect (Continuation.continue k ()))"
  , "generated :: List Int"
  , "generated = collect (generate ())"
  ]

spec :: Spec Unit
spec = describe "Stella source reifying the continuations it captures, run on Steam" do
  it "resumes, with `Continuation.continue` in the clause, as a `full` clause resumes with `resume`" do
    continuations <- liftEffect continuationSource
    runningAfter [ continuations ] source [ "chosen", "reified" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "chosen" "Cons(1, Cons(2, Nil))"
        , Tuple "reified" "Cons(1, Cons(2, Nil))"
        ]

  it "resumes a continuation taken out of the handling expression after it has answered, under the same handler" do
    continuations <- liftEffect continuationSource
    runningAfter [ continuations ] source [ "generated" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "generated" "Cons(1, Cons(2, Cons(3, Nil)))" ]
