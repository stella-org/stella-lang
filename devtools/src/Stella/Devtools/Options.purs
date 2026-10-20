module Stella.Devtools.Options where

import Prelude

import ArgParse.Basic (ArgParser)
import ArgParse.Basic as ArgParser
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Stella.CLI.Effect.FS (FilePath)
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.CLI.Options (loglevel)

type BuildSeedsOptions =
  { output :: FilePath
  , steamCmd :: String
  }

data Command = BuildSeeds BuildSeedsOptions

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
          [ ArgParser.command [ "build-seeds" ]
              "Build the seed modules which are loaded during\
              \ bootstrapping the compiler."
              ((BuildSeeds <$> buildSeedsOptions) <* ArgParser.flagHelp)
          ]
    }
    <* ArgParser.flagHelp
  where
  buildSeedsOptions = ArgParser.fromRecord
    { output:
        ArgParser.argument [ "-o", "--output" ]
          "The directory each module's interface and bytecode are written to"
    , steamCmd:
        ArgParser.argument [ "--steam-cmd" ]
          "The Steam executable, which runs macros at compile time.\n\
          \Defaults to `steam`"
          # ArgParser.default "steam"
    }

parse :: Array String -> Either ArgParser.ArgError Options
parse = ArgParser.parseArgs
  "stella-devtools"
  "The Stella compiler developers' toolkit"
  options
