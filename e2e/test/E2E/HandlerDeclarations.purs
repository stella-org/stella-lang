-- | A module written in source whose handlers are declared at the top level,
-- | compiled and loaded, and each value read as the machine holds it once the
-- | module is initialized: the front end's handler declarations, run.
-- |
-- | `countFrom` takes the value its cell starts at, and `collect` gathers what
-- | is emitted with a return clause and an answer type of its own. `counted`
-- | applies `countFrom` once; `separate` applies it twice in a row, and
-- | `nested` once inside the computation of another, each application on a
-- | cell of its own. `asItem` installs both handlers as items of a handling
-- | expression, the first outermost.
module Test.E2E.HandlerDeclarations (spec) where

import Prelude

import Prim as P

import Data.Map as Map
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import E2E.Build (Sources)
import Test.E2E.Running (running)

spec :: Sources -> Spec Unit
spec sources = describe "Stella source declaring handlers at the top level, run on Steam" do
  it "applies a handler taking a parameter, its cell starting at the parameter's value" do
    running sources [ "handler-declarations" ] [ "counted" ] \values ->
      values `shouldEqual` Map.fromFoldable [ Tuple "counted" "Cons(5, Cons(6, Nil))" ]

  it "gives each application of a handler a cell of its own, one after another or one inside another" do
    running sources [ "handler-declarations" ] [ "separate", "nested" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "separate" "Cons(1, Cons(0, Nil))"
        , Tuple "nested" "Cons(0, Cons(100, Cons(1, Nil)))"
        ]

  it "answers with what its return clause gives, and stands as an item of a handling expression" do
    running sources [ "handler-declarations" ] [ "emitted", "asItem" ] \values ->
      values `shouldEqual` Map.fromFoldable
        [ Tuple "emitted" "Cons(1, Cons(2, Nil))"
        , Tuple "asItem" "Cons(7, Cons(8, Nil))"
        ]
