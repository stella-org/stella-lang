module Steam.CLI.Options where

import Prelude

import ArgParse.Basic (ArgParser)
import ArgParse.Basic as ArgParser
import Data.Maybe (Maybe)
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.CLI.Options (loglevel)

type RunOptions = { program :: String }

-- | What `session` is given: where the implementations of the foreigns the
-- | modules it will load declare are. **Absent is not an error**: a module over `Base`
-- | alone declares nothing for one to say.
type SessionOptions = { manifest :: Maybe String }

data Command
  = Session SessionOptions
  | Run RunOptions

derive instance Eq Command
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
          [ ArgParser.command [ "run" ]
              "Load whole program and execute main once."
              ((Run <$> runOptions) <* ArgParser.flagHelp)
          , ArgParser.command [ "session" ]
              "Serve a compiler over descriptor 3 until it closes the session."
              ((Session <$> sessionOptions) <* ArgParser.flagHelp)
          ]
    }
    <* ArgParser.flagHelp
  where
  sessionOptions = ArgParser.fromRecord
    { manifest:
        ArgParser.argument [ "--manifest" ]
          "Path to the foreign-manifest.json"
          # ArgParser.optional
    }

  runOptions = ArgParser.fromRecord
    { program:
        ArgParser.anyNotFlag "PROGRAM.json" "The program descriptor"
    }

parse :: Array String -> Either ArgParser.ArgError Options
parse = ArgParser.parseArgs
  "steam"
  "The Stella Abstract Machine"
  options