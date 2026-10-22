-- | `stellac graph <stella.json>`: prints, as JSON, the modules `stella.json`
-- | lists and the modules each imports, for whatever drives the compiler to
-- | plan builds with.
-- |
-- | ```json
-- | { "formatVersion": 0,
-- |   "modules": [
-- |     { "module": "A.Main", "path": "src/A/Main.stel",
-- |       "imports": [ { "module": "B.Api", "start": { "line": 3, "column": 8 }, "end": { "line": 3, "column": 13 } } ] } ] }
-- | ```
-- |
-- | It reads only the headers of the files in `modules`, as a build does
-- | before compiling anything: no macro runs and nothing is elaborated, so an
-- | error past a header goes unreported. It reads no file in `dependencies` and
-- | skips the rules of the build environment, so the seed modules' own sources
-- | may be listed.
-- |
-- | Modules come in order of their names, each with its path as `stella.json`
-- | writes it and the imports of its header in the order written. Each import
-- | carries the line and the columns of its name, the end just past it, as
-- | messages count them. `import Prim` is left out. An import of a module the
-- | file does not list is reported like any other, and modules importing one
-- | another are not refused.
-- |
-- | The errors are those a build reports of files and headers.
module Stellac.Graph (cmd, formatVersion) where

import Prelude

import Data.Argonaut.Core (Json, fromArray, fromNumber, fromObject, fromString, stringifyWithIndent)
import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Int (toNumber)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Tuple (Tuple(..))
import Effect.Console as Console
import Foreign.Object as Object
import Run (EFFECT, Run, liftEffect)
import Run.Except (EXCEPT, throw)
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Log as Log
import Stella.Compiler.Build (Header, buildMessages, printBuildMessage, readHeaders)
import Stella.Compiler.CST.Types (SourcePos)
import Stella.Compiler.TypedCore (ModuleName(..))
import Stellac.Config (Config)
import Type.Row (type (+))

-- | The version of what this command prints.
formatVersion :: Int
formatVersion = 0

cmd :: forall r. Config -> Run (FS + LOG + EXCEPT String + EFFECT + r) Unit
cmd config = do
  readHeaders FS.readText (map (\m -> { path: m.path, name: m.module }) config.modules) >>= case _ of
    Left err -> do
      for_ (NonEmptyArray.toArray (buildMessages err)) (Log.error <<< printBuildMessage)
      throw "The module graph could not be read"
    Right headers -> do
      -- each file's path as `stella.json` writes it
      let written = Map.fromFoldable (map (\m -> Tuple m.path m.written) config.modules)
      liftEffect (Console.log (stringifyWithIndent 2 (graphJson (\p -> fromMaybe p (Map.lookup p written)) headers)))

graphJson :: (String -> String) -> Array Header -> Json
graphJson pathOf headers = fromObject
  ( Object.fromFoldable
      [ Tuple "formatVersion" (fromNumber (toNumber formatVersion))
      , Tuple "modules" (fromArray (map moduleJson (Array.sortWith _.name headers)))
      ]
  )
  where
  moduleJson h = fromObject
    ( Object.fromFoldable
        [ Tuple "module" (fromString (moduleText h.name))
        , Tuple "path" (fromString (pathOf h.path))
        , Tuple "imports" (fromArray (map importJson h.imports))
        ]
    )

  importJson i = fromObject
    ( Object.fromFoldable
        [ Tuple "module" (fromString (moduleText i.module))
        , Tuple "start" (position i.at.start)
        , Tuple "end" (position i.at.end)
        ]
    )

  position :: SourcePos -> Json
  position p = fromObject (Object.fromFoldable [ Tuple "line" (fromNumber (toNumber p.line)), Tuple "column" (fromNumber (toNumber p.column)) ])

  moduleText (ModuleName m) = m
