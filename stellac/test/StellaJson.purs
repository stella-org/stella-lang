-- | `stella.json` as the tests write it, by `Stellac.Config.encode`: every field
-- | given, the options set to what a test asks and to the defaults below
-- | otherwise.
module Test.Stellac.StellaJson
  ( Settings
  , Entry
  , settings
  , stellaJson
  ) where

import Prelude

import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.Compiler.TypedCore (ModuleName(..))
import Stellac.Config as Config

-- | A module built elsewhere, by its name and its two files.
type Entry = { module :: String, interface :: String, object :: String }

type Settings =
  { output :: String
  , emitCore :: Boolean
  , traceOptimizer :: Array String
  , steamCmd :: String
  , logLevel :: LogLevel
  , monochrome :: Boolean
  , modules :: Array { module :: String, path :: String }
  , dependencies :: Array Entry
  }

-- | The modules given, each by its name and its file, and nothing else: output
-- | to `output`, nothing traced, Steam as `steam`, messages from `info` and
-- | without colour.
settings :: Array { module :: String, path :: String } -> Settings
settings modules =
  { output: "output"
  , emitCore: false
  , traceOptimizer: []
  , steamCmd: "steam"
  , logLevel: Info
  , monochrome: true
  , modules
  , dependencies: []
  }

stellaJson :: Settings -> String
stellaJson s = Config.encode
  { options:
      { output: s.output
      , emitCore: s.emitCore
      , traceOptimizer: map ModuleName s.traceOptimizer
      , steamCmd: s.steamCmd
      , logLevel: s.logLevel
      , monochrome: s.monochrome
      }
  , modules: map (\m -> { module: ModuleName m.module, path: m.path, written: m.path }) s.modules
  , dependencies: map (\d -> d { module = ModuleName d.module }) s.dependencies
  }
