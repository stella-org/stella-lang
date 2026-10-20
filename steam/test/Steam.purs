-- | The tests every change runs. Those over a child process or a session's
-- | protocol, over programs built from source, are the end-to-end suite's, and
-- | those over inputs as deep and as long as stack safety is tested at are
-- | `Test.Steam.Stress`'s. Run with `spago test -p steam`.
module Test.Steam where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Steam.Calls as Calls
import Test.Steam.Drive as Drive
import Test.Steam.Eval as Eval
import Test.Steam.Facade as Facade
import Test.Steam.Fixtures as Fixtures
import Test.Steam.Foreign as Foreign
import Test.Steam.Handlers as Handlers
import Test.Steam.Marshal as Marshal
import Test.Steam.Structural as Structural
import Test.Steam.Ops as Ops
import Test.Steam.Root as Root
import Test.Steam.Value as Value
import Test.Steam.Wire as Wire

main :: Effect Unit
main = do
  fixtures <- Fixtures.fixtureNames
  runSpecAndExitProcess [ consoleReporter ] do
    Value.spec
    Eval.spec
    Calls.spec
    Ops.spec
    Foreign.spec
    Handlers.spec
    Root.spec
    Fixtures.spec fixtures
    Drive.spec
    Marshal.spec
    Structural.spec
    Facade.spec
    Wire.spec
