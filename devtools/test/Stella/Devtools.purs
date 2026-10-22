-- | The tests of `stella-devtools`: a seed build on the host it shares with
-- | `stellac compile`, and `build-seeds` run as a command. Both start processes,
-- | `steam` by its development entry point and `stella-devtools` by
-- | `devtools/index.js`, both of which need the workspace built.
module Test.Stella.Devtools where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Milliseconds(..))
import Test.Stella.Devtools.BuildSeeds as BuildSeeds
import Test.Stella.Devtools.SeedBuild as SeedBuild
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Config

main :: Effect Unit
main = runSpecAndExitProcess' { defaultConfig: Config.defaultConfig { timeout = Just (Milliseconds 60_000.0) }, parseCLIOptions: true } [ consoleReporter ] do
  SeedBuild.spec
  BuildSeeds.spec
