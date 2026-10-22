-- | The tests every change runs: `stellac compile` over files held in memory,
-- | and the dependencies `stella.json` lists. Those that write packages to disk
-- | and run `stellac compile` or `stellac graph` are the end-to-end suite's. Run
-- | with `spago test -p stellac`.
module Test.Stella where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Stellac.Compile as Compile
import Test.Stellac.Dependencies as Dependencies

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  Compile.spec
  Dependencies.spec
