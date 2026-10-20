-- | The end-to-end tests over a child process or a session's protocol: the
-- | `steam` command run on programs built from source, and sessions. CI runs them
-- | with every change. Run with `spago test -p e2e -m Test.E2E.Integration`.
module Test.E2E.Integration where

import Prelude

import Data.Either (Either(..))
import E2E.Build (readSources)
import Effect (Effect)
import Effect.Exception (throw)
import Test.E2E.Command as Command
import Test.E2E.Lists as Lists
import Test.E2E.Parse as Parse
import Test.E2E.Session as Session
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

-- | The sources are read, and what every build of them shares made, once.
main :: Effect Unit
main = readSources >>= case _ of
  Left err -> throw err
  Right sources -> runSpecAndExitProcess [ consoleReporter ] do
    Command.spec sources
    Session.spec
    Lists.spec sources
    Parse.spec sources
