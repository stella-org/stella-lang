module Test.Steam where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Steam.Arrays as Arrays
import Test.Steam.Calls as Calls
import Test.Steam.Command as Command
import Test.Steam.Drive as Drive
import Test.Steam.Equivalence as Equivalence
import Test.Steam.Eval as Eval
import Test.Steam.Facade as Facade
import Test.Steam.Fixtures as Fixtures
import Test.Steam.Foreign as Foreign
import Test.Steam.Handlers as Handlers
import Test.Steam.Load as Load
import Test.Steam.Marshal as Marshal
import Test.Steam.Session as Session
import Test.Steam.SessionKernel as SessionKernel
import Test.Steam.SessionGuest as SessionGuest
import Test.Steam.Structural as Structural
import Test.Steam.Ops as Ops
import Test.Steam.Reference as Reference
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
    Load.spec
    Arrays.spec
    Foreign.spec
    Handlers.spec
    Root.spec
    Fixtures.spec fixtures
    Drive.spec
    Marshal.spec
    Command.spec
    Structural.spec
    Session.spec
    SessionGuest.spec
    SessionKernel.spec
    Facade.spec
    Reference.spec
    Equivalence.spec
    Wire.spec

