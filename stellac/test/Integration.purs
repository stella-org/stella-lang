-- | The tests over a child process: `stellac build` run as a command. CI runs
-- | them with every change. Run with `spago test -p stellac -m Test.Stellac.Integration`.
module Test.Stellac.Integration where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Stellac.Separate as Separate

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  Separate.spec
