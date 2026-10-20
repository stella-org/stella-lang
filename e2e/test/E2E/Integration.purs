-- | The end-to-end tests over a child process or a session's protocol: the
-- | `steam` command run on programs built from source, sessions, and `stellac build`
-- | of packages written to disk, with the programs it builds run. CI runs them with
-- | every change. Run with `spago test -p e2e -m Test.E2E.Integration`.
module Test.E2E.Integration where

import Prelude

import Data.Either (Either(..))
import E2E.Build (readSources)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Milliseconds(..))
import Effect.Exception (throw)
import Test.E2E.Abi as Abi
import Test.E2E.Apart as Apart
import Test.E2E.Base as Base
import Test.E2E.BasePackage as BasePackage
import Test.E2E.Command as Command
import Test.E2E.CompilerLib as CompilerLib
import Test.E2E.Equivalence as Equivalence
import Test.E2E.Isolation as Isolation
import Test.E2E.Lists as Lists
import Test.E2E.Parse as Parse
import Test.E2E.Reference as Reference
import Test.E2E.Run as Run
import Test.E2E.Separate as Separate
import Test.E2E.Session as Session
import Test.E2E.SessionGuest as SessionGuest
import Test.E2E.SessionKernel as SessionKernel
import Test.E2E.Synthesis as Synthesis
import Test.E2E.Toolchain as Toolchain
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Config

-- | The sources are read, and what every build of them shares made, once. A
-- | test may take a minute: a build runs its parsers and synthesizers on a
-- | session of its own.
main :: Effect Unit
main = readSources >>= case _ of
  Left err -> throw err
  Right sources -> runSpecAndExitProcess' { defaultConfig: Config.defaultConfig { timeout = Just (Milliseconds 60_000.0) }, parseCLIOptions: true } [ consoleReporter ] do
    Command.spec sources
    Session.spec
    SessionGuest.spec sources
    SessionKernel.spec sources
    Lists.spec sources
    Parse.spec sources
    Reference.spec sources
    Equivalence.spec sources
    Isolation.spec sources
    Synthesis.spec
    Toolchain.spec
    Apart.spec
    Separate.spec
    Run.spec
    Abi.spec
    Base.spec
    BasePackage.spec
    CompilerLib.spec
