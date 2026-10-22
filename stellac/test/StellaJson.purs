-- | `stella.json` as the tests write it: every field given, the options set to
-- | what a test asks and to the defaults below otherwise.
module Test.Stellac.StellaJson
  ( Settings
  , Entry
  , settings
  , stellaJson
  ) where

import Prelude

import Data.Argonaut.Core (Json, fromArray, fromBoolean, fromNumber, fromObject, fromString, stringifyWithIndent)
import Data.Tuple (Tuple(..))
import Foreign.Object as Object

-- | A module built elsewhere, by its name and its two files.
type Entry = { module :: String, interface :: String, object :: String }

type Settings =
  { output :: String
  , emitCore :: Boolean
  , traceOptimizer :: Array String
  , steamCmd :: String
  , logLevel :: String
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
  , logLevel: "info"
  , monochrome: true
  , modules
  , dependencies: []
  }

stellaJson :: Settings -> String
stellaJson s = stringifyWithIndent 2 do
  object
    [ Tuple "formatVersion" (fromNumber 0.0)
    , Tuple "options" do
        object
          [ Tuple "output" (fromString s.output)
          , Tuple "emitCore" (fromBoolean s.emitCore)
          , Tuple "traceOptimizer" (fromArray (map fromString s.traceOptimizer))
          , Tuple "steamCmd" (fromString s.steamCmd)
          , Tuple "logLevel" (fromString s.logLevel)
          , Tuple "monochrome" (fromBoolean s.monochrome)
          ]
    , Tuple "modules" (fromArray (map (\m -> object [ Tuple "module" (fromString m.module), Tuple "path" (fromString m.path) ]) s.modules))
    , Tuple "dependencies" (listing s.dependencies)
    ]

-- | Modules built elsewhere, as `dependencies` lists them.
listing :: Array Entry -> Json
listing entries = fromArray (map (\e -> object [ Tuple "module" (fromString e.module), Tuple "interface" (fromString e.interface), Tuple "object" (fromString e.object) ]) entries)

object :: Array (Tuple String Json) -> Json
object = fromObject <<< Object.fromFoldable

