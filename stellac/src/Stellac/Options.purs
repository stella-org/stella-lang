-- | The command line of `stellac`: the command, and the `stella.json` it is
-- | given ([Config](Config.purs)), which holds whatever else a run is to do.
module Stellac.Options where

import Prelude

import ArgParse.Basic (ArgParser)
import ArgParse.Basic as ArgParser
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Stella.CLI.Effect.FS (FilePath)

data Command
  = Compile FilePath
  | Graph FilePath

derive instance Generic Command _
instance Show Command where
  show = genericShow

-- | The `stella.json` a command reads.
configOf :: Command -> FilePath
configOf = case _ of
  Compile path -> path
  Graph path -> path

options :: ArgParser Command
options =
  ArgParser.choose "command"
    [ ArgParser.command [ "compile" ]
        "Compile the modules a stella.json lists, in the order it lists them"
        ((Compile <$> config) <* ArgParser.flagHelp)
    , ArgParser.command [ "graph" ]
        "Print, as JSON, the modules a stella.json lists and the modules each\n\
        \imports, read from their headers alone"
        ((Graph <$> config) <* ArgParser.flagHelp)
    ]
    <* ArgParser.flagHelp
  where
  config = ArgParser.anyNotFlag "STELLA_JSON" "The stella.json to read"

parse :: Array String -> Either ArgParser.ArgError Command
parse = ArgParser.parseArgs "stellac" "The Stella Compiler" options
