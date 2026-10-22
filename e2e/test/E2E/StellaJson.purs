-- | `stella.json` as the tests write it, by `Stellac.Config.encode`: every field
-- | given, the options set to what a test asks and to the defaults below
-- | otherwise.
module Test.E2E.StellaJson
  ( Settings
  , Entry
  , settings
  , stellaJson
  , listedAt
  , compileAt
  , entriesIn
  ) where

import Prelude

import Data.Argonaut.Core (toArray, toObject, toString)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either, note)
import Data.Traversable (traverse)
import Data.Maybe (fromMaybe)
import Data.String (Pattern(..), Replacement(..), replaceAll, stripPrefix, stripSuffix)
import Foreign.Object as Object
import Run (AFF, EFFECT, Run)
import Run.Except (EXCEPT)
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.Log (LOG, LogLevel(..))
import Stella.CLI.Effect.Process (PROCESS)
import Stella.Compiler.TypedCore (ModuleName(..))
import Stellac.Config as Config
import Stellac.Options (Command(..))
import Stellac.Program (loaded, program)
import Type.Row (type (+))

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

-- | The file of the path given, from its package's root, listed as the module
-- | its path from `src` names.
listedAt :: String -> { module :: String, path :: String }
listedAt path = { module: replaceAll (Pattern "/") (Replacement ".") (dropping "src/" stripPrefix (dropping ".stel" stripSuffix path)), path }
  where
  dropping s strip p = fromMaybe p (strip (Pattern s) p)

-- | `stellac compile` given the `stella.json` at the path given, as the command
-- | runs it: the file loaded, then the modules it lists compiled.
compileAt :: String -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF + ()) Unit
compileAt file = loaded file >>= program (Compile file)

-- | The entries of a JSON list of them, as `dependencies` lists them.
entriesIn :: String -> Either String (Array Entry)
entriesIn text = jsonParser text >>= \json -> note "not a list of entries" do
  items <- toArray json
  traverse entry items
  where
  entry item = do
    o <- toObject item
    m <- Object.lookup "module" o >>= toString
    interface <- Object.lookup "interface" o >>= toString
    obj <- Object.lookup "object" o >>= toString
    pure { module: m, interface, object: obj }
