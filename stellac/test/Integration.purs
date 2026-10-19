-- | The tests over a child process: `stellac build` run as a command, and the
-- | programs it builds run by `steam run`, which needs `steam` built. CI runs
-- | them with every change. Run with `spago test -p stellac -m Test.Stellac.Integration`.
module Test.Stellac.Integration where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Stellac.Abi as Abi
import Test.Stellac.Base as Base
import Test.Stellac.Run as Run
import Test.Stellac.Separate as Separate

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  Separate.spec
  Run.spec
  Abi.spec
  Base.spec
