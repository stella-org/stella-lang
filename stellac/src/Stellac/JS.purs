module Stellac.JS where

import Prelude

import ArgParse.Basic (ArgError(..), ArgErrorMsg(..))
import ArgParse.Basic as ArgParser
import Data.Array as Array
import Data.Either (Either(..))
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Console as Console
import Node.Process as Process
import Run (AFF, EFFECT, Run, runBaseAff')
import Run.Except (EXCEPT)
import Run.Except as Except
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Log as Log
import Stella.CLI.Runner.Node as Node
import Stellac.Options as Options
import Stellac.Program (program)
import Type.Row (type (+))

type ErrorType = String

runNode
  :: forall a
   . Log.LoggerConfig
  -> Run (LOG + FS + EXCEPT ErrorType + AFF + EFFECT + ()) a
  -> Aff (Either ErrorType a)
runNode loggerConfig m = m
  # Log.interpret (Node.jsConsoleHandler loggerConfig)
  # FS.interpret Node.nodeFsHandler
  # Except.runExcept
  # runBaseAff'

main :: Effect Unit
main = do
  args <- Array.drop 2 <$> Process.argv
  case Options.parse args of
    -- Asking for help is not a failure, and a shell that checks the exit
    -- status should not be told it was one.
    Left err@(ArgError _ ShowHelp) -> asked err
    Left err@(ArgError _ (ShowInfo _)) -> asked err
    Left err -> do
      Console.error (ArgParser.printArgError err)
      Process.exit' 1
    Right opts -> launchAff_ (run opts)
  where
  asked err = Console.log (ArgParser.printArgError err)

  run opts =
    let
      loggerConfig = Log.defaultLoggerConfig
        { minLevel = opts.logLevel
        , color = not opts.monochrome
        }
    in
      runNode loggerConfig (program opts) >>= case _ of
        Right _ -> pure unit
        Left err -> liftEffect do
          Console.error (err)