-- | The tests over a child process or a session's protocol: the `steam`
-- | command, and sessions in and out of process. CI runs them with every change.
-- | Run with `spago test -p steam -m Test.Steam.Integration`.
module Test.Steam.Integration where

import Prelude

import Effect (Effect)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Steam.Equivalence as Equivalence
import Test.Steam.Isolation as Isolation
import Test.Steam.Lists as Lists
import Test.Steam.Parse as Parse
import Test.Steam.Reference as Reference
import Test.Steam.SessionGuest as SessionGuest
import Test.Steam.SessionKernel as SessionKernel

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  SessionGuest.spec
  SessionKernel.spec
  Parse.spec
  Lists.spec
  Reference.spec
  Equivalence.spec
  Isolation.spec
