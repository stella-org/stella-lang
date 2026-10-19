-- | `stellac graph`: the modules of the source files given and the modules each
-- | imports, printed as JSON for whatever drives the compiler to plan a build
-- | with.
-- |
-- | ```json
-- | { "formatVersion": 0,
-- |   "modules": [
-- |     { "module": "A.Main", "path": "src/A/Main.stel",
-- |       "imports": [ { "module": "B.Api", "start": { "line": 3, "column": 8 }, "end": { "line": 3, "column": 13 } } ] } ] }
-- | ```
-- |
-- | **It reads the headers of the files `--workdir` and `--src` name, as a
-- | build does before it compiles anything, and nothing past them**: no macro
-- | is expanded, no synthesizer run, and nothing elaborated, so an error past a
-- | header is not reported. The modules are in order of their names, each with
-- | its file's path from the directory `--workdir` names. Its imports are the
-- | modules its header imports, which are its dependencies in source, in the
-- | order written, each with where its name is written: a line and the columns
-- | its name covers, the end just past it, as messages count them. An
-- | `import Prim` is no dependency and is left out. A module no file given
-- | holds is reported as any other, and modules importing one another are not
-- | refused.
-- |
-- | The errors are those a build reports of directories, files, and headers.
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
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Effect.Console as Console
import Foreign.Object as Object
import Run (EFFECT, Run, liftEffect)
import Run.Except (EXCEPT, throw)
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Log as Log
import Stella.Compiler.Build (Header, buildMessages, defaultSourceRoots, printBuildMessage, readHeaders)
import Stella.Compiler.CST.Types (SourcePos)
import Stella.Compiler.TypedCore (ModuleName(..))
import Stellac.Options (GraphOptions)
import Stellac.Sources (sourceFiles)
import Type.Row (type (+))

-- | The version of what this command prints.
formatVersion :: Int
formatVersion = 0

cmd :: forall r. GraphOptions -> Run (FS + LOG + EXCEPT String + EFFECT + r) Unit
cmd opts = do
  files <- sourceFiles opts.workdir opts.src
  readHeaders FS.readText defaultSourceRoots files >>= case _ of
    Left err -> do
      for_ (NonEmptyArray.toArray (buildMessages err)) (Log.error <<< printBuildMessage)
      throw "The module graph could not be read"
    Right headers -> do
      -- each file's path from the directory `--workdir` names
      let within = Map.fromFoldable (map (\f -> Tuple f.path (joinWith "/" f.within)) files)
      liftEffect (Console.log (stringifyWithIndent 2 (graphJson (\p -> fromMaybe p (Map.lookup p within)) headers)))

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
