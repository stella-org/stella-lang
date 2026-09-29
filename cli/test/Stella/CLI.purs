module Test.Stella.CLI where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Stella.CLI.Session as Session

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  Session.spec
