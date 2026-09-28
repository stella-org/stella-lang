module Test.Stella.Backend where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Stella.Backend.JavaScript as JavaScript

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  JavaScript.spec
