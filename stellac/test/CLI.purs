module Test.Stella where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Stellac.Build as Build

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  Build.spec
