-- | `stella.json` as the tests write it: every field given, the options set to
-- | what a test asks and to the defaults below otherwise.
module Test.E2E.StellaJson
  ( Settings
  , Entry
  , settings
  , stellaJson
  , listing
  , listedAt
  , compileAt
  , entriesIn
  ) where

import Prelude

import Data.Argonaut.Core (Json, fromArray, fromBoolean, fromNumber, fromObject, fromString, stringifyWithIndent, toArray, toObject, toString)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either, note)
import Data.Traversable (traverse)
import Data.Maybe (fromMaybe)
import Data.String (Pattern(..), Replacement(..), replaceAll, stripPrefix, stripSuffix)
import Data.Tuple (Tuple(..))
import Foreign.Object as Object
import Run (AFF, EFFECT, Run)
import Run.Except (EXCEPT)
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Process (PROCESS)
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
