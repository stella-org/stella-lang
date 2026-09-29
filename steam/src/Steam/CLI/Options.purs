module Steam.CLI.Options where

import Prelude

import ArgParse.Basic (ArgParser)
import ArgParse.Basic as ArgParser
import Data.Array as Array
import Data.Maybe (Maybe)
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.CLI.Options (loglevel, moduleName)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..))

-- | What `run` is given: the modules, and where the entry point is.
-- |
-- | **The two halves of the entry point are two options.** A module name has dots
-- | in it, so one option carrying both would leave `A.B` reading as the module
-- | `A.B` and as the global `B` of the module `A`, with nothing in the spelling to
-- | separate them. Deciding by which modules were loaded is the answer to avoid:
-- | the same command line would mean different things for different sets of files.
type RunOptions =
  { entry :: ModuleName
  -- | The manifest saying where the implementations of the foreigns this program
  -- | declares are. **Absent is not an error**: a program over `Base` alone declares
  -- | nothing for one to say.
  , manifest :: Maybe String
  , entryGlobal :: Ident
  -- | The `.dmo` files, in dependency order. **Nothing here is sorted**: they are
  -- | loaded left to right, and a module whose imports are not already loaded is
  -- | refused. No path is searched and no name resolved to a file.
  , modules :: Array String
  }

-- | What `session` is given: where the implementations of the foreigns the
-- | modules it will load declare are. **Absent is not an error**, as for `run`: a
-- | module over `Base` alone declares nothing for one to say.
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
    { entry:
        ArgParser.argument [ "--entry", "-e" ]
          "Module holding the entry point"
          # moduleName
          # ArgParser.default (ModuleName "Main")
    , entryGlobal:
        ArgParser.argument [ "--entry-global" ]
          "Name of the entry point within that module"
          # map Ident
          # ArgParser.default (Ident "main")
    , manifest:
        ArgParser.argument [ "--manifest" ]
          "Where the foreign manifest is"
          # ArgParser.optional
    , modules:
        ArgParser.anyNotFlag "MODULE.dmo" "Bytecode files, in dependency order"
          # ArgParser.many
          # map Array.fromFoldable
    }

parse :: Array String -> Either ArgParser.ArgError Options
parse = ArgParser.parseArgs
  "steam"
  "The Stella Abstract Machine"
  options