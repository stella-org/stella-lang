module Stellac.Options where

import Prelude

import ArgParse.Basic (ArgParser)
import ArgParse.Basic as ArgParser
import Data.Array as Array
import Data.Either (Either, note)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Stella.CLI.Effect.FS (FilePath)
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.CLI.Options (loglevel, moduleName)
import Stella.Compiler.TypedCore (ModuleName(..))

data BuildTarget = JS | Wasm

instance Show BuildTarget where
  show = case _ of
    JS -> "JS"
    Wasm -> "Wasm"

buildTarget :: ArgParser String -> ArgParser BuildTarget
buildTarget = ArgParser.unformat "TARGET" parseBuildTarget
  where
  parseBuildTarget = note "Invaid build target. Acceptable: js | wasm"
    <<< case _ of
      "js" -> Just JS
      "wasm" -> Just Wasm
      _ -> Nothing

type BuildOptions =
  { output :: FilePath
  , main :: ModuleName
  , inputs :: Array FilePath
  , target :: Maybe BuildTarget
  , traceOpt :: Maybe ModuleName
  }

data Command = Build BuildOptions

derive instance Generic Command _
instance Show Command where
  show = genericShow

type Options =
  { logLevel :: LogLevel
  , monochrome :: Boolean
  , command :: Command
  }

options :: ArgParser Options
options =
  ArgParser.fromRecord
    { logLevel:
        ArgParser.argument [ "--log-level" ]
          "Suppress log messages of level lower than"
          # loglevel
          # ArgParser.default Info
    , monochrome:
        ArgParser.flag [ "--monochrome" ]
          "Disable coloring log messages"
          # ArgParser.boolean
    , command:
        ArgParser.choose "command"
          [ ArgParser.command [ "build" ]
              "Build all modules in given filepaths.\n\
              \Note: glob patterns is not supported yet."
              ((Build <$> buildOptions) <* ArgParser.flagHelp)
          ]
    }
    <* ArgParser.flagHelp
  where
  buildOptions = ArgParser.fromRecord
    { output:
        ArgParser.argument [ "-o", "--output" ]
          "Path to output directory in which all module artifacts placed\n\
          \Defaults to `output` in current directory"
          # ArgParser.default "output"
    , inputs:
        ArgParser.anyNotFlag "path/to/MODULE.stel"
          "Absolute path to all module file (with `.stel` extension)"
          # ArgParser.many
          # map Array.fromFoldable
    , main:
        ArgParser.argument [ "-m", "--main" ]
          "Entrypoint module which exports value with `entrypoint` attribute"
          # moduleName
          # ArgParser.default (ModuleName "Main")
    , traceOpt:
        ArgParser.argument [ "--trace-opt" ]
          "Emit optimizer trace of specified module.\n\
          \Useful to inspect how module is simplified through optimizaion."
          # moduleName
          # ArgParser.optional
    , target:
        ArgParser.argument [ "-t", "--target" ]
          "Build target. Acceptable value: `js` | `wasm`\n\
          \If not specified, build finishes after emitting bytecode object file."
          # buildTarget
          # ArgParser.optional
    }

parse :: Array String -> Either ArgParser.ArgError Options
parse = ArgParser.parseArgs "stellac" "The Stella Compiler" options
