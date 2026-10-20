-- | The tests every change runs: builds over files held in memory, and the
-- | dependency maps they read. Those that write packages to disk and run
-- | `stellac build` are the end-to-end suite's. Run with `spago test -p stellac`.
module Test.Stella where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Stellac.Build as Build
import Test.Stellac.Dependencies as Dependencies

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  Build.spec
  Dependencies.spec
