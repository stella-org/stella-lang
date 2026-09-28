module Test.Steam where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Steam.Arrays as Arrays
import Test.Steam.Calls as Calls
import Test.Steam.Command as Command
import Test.Steam.Drive as Drive
import Test.Steam.Eval as Eval
import Test.Steam.Fixtures as Fixtures
import Test.Steam.Foreign as Foreign
import Test.Steam.Handlers as Handlers
import Test.Steam.Load as Load
import Test.Steam.Marshal as Marshal
import Test.Steam.Structural as Structural
import Test.Steam.Ops as Ops
import Test.Steam.Value as Value

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  Value.spec
  Eval.spec
  Calls.spec
  Ops.spec
  Load.spec
  Arrays.spec
  Foreign.spec
  Handlers.spec
  Fixtures.spec
  Drive.spec
  Marshal.spec
  Command.spec
  Structural.spec
