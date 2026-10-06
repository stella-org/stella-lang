module Stellac.Options where

import Prelude

import ArgParse.Basic (ArgParser)
import ArgParse.Basic as ArgParser
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Stella.CLI.Effect.FS (FilePath)
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.CLI.Options (loglevel, moduleName)
import Stella.Compiler.TypedCore (ModuleName)

type BuildOptions =
  { output :: FilePath
  , workdir :: FilePath
  , src :: Array String
  , traceOpt :: Maybe ModuleName
  , emitCore :: Boolean
  , steamCmd :: String
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
              "Build the modules of a package"
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
    , workdir:
        ArgParser.argument [ "--workdir" ]
          "Working directory for the build process.\n\
          \Defaults to the current directory"
          # ArgParser.default "."
    , src:
        ArgParser.argument [ "--src" ]
          "Glob pattern, from the package root, of the source files to build.\n\
          \May be given more than once. Defaults to `src/**/*.stel`"
          # ArgParser.unfolded
    , emitCore:
        ArgParser.flag [ "--emit-core" ]
          "Emit the Typed Core of each module as `<MODULE>.core.json`"
          # ArgParser.boolean
    , steamCmd:
        ArgParser.argument [ "--steam-cmd" ]
          "The Steam executable, which runs macros at compile time.\n\
          \Defaults to `steam`"
          # ArgParser.default "steam"
    , traceOpt:
        ArgParser.argument [ "--trace-opt" ]
          "Emit optimizer trace of specified module.\n\
          \Useful to inspect how module is simplified through optimizaion."
          # moduleName
          # ArgParser.optional
    }

parse :: Array String -> Either ArgParser.ArgError Options
parse = ArgParser.parseArgs "stellac" "The Stella Compiler" options
