-- | The tests over inputs as deep and as long as stack safety is tested at:
-- | each is the counterpart of one the usual suite runs at a size every
-- | change affords. The Stress workflow runs them on main, nightly, and by hand.
-- | Run with `spago test -p steam -m Test.Steam.Stress`.
module Test.Steam.Stress where

import Prelude

import Effect (Effect)
import Test.Spec (describe)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Steam.Fixtures as Fixtures
import Test.Steam.Wire as Wire

main :: Effect Unit
main = do
  fixtures <- Fixtures.fixtureNames
  runSpecAndExitProcess [ consoleReporter ] do
    Fixtures.deepSpec fixtures
    describe "Steam.CLI.Wire" do
      Wire.longListCarried "carries a list as long as a frame allows" 100000
