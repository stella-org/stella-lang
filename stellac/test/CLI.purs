module Test.Stella where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Milliseconds(..))
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Config
import Test.Stellac.Apart as Apart
import Test.Stellac.Build as Build
import Test.Stellac.Dependencies as Dependencies
import Test.Stellac.Synthesis as Synthesis
import Test.Stellac.Toolchain as Toolchain

-- | Each case may take a minute: a synthesizer that never returns runs until
-- | its budget is used up, which on the machine takes seconds.
main :: Effect Unit
main = runSpecAndExitProcess' { defaultConfig: Config.defaultConfig { timeout = Just (Milliseconds 60_000.0) }, parseCLIOptions: true } [ consoleReporter ] do
  Build.spec
  Dependencies.spec
  Synthesis.spec
  Toolchain.spec
  Apart.spec
