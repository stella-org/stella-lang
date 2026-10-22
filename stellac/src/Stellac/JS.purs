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
import Stella.CLI.Effect.Process (PROCESS)
import Stella.CLI.Effect.Process as ProcessEffect
import Stella.CLI.Runner.Node as Node
import Stellac.Options (configOf)
import Stellac.Options as Options
import Stellac.Program (loaded, program)
import Type.Row (type (+))

type ErrorType = String

runNode
  :: forall a
   . Log.LoggerConfig
  -> Run (LOG + FS + PROCESS + EXCEPT ErrorType + AFF + EFFECT + ()) a
  -> Aff (Either ErrorType a)
runNode loggerConfig m = m
  # Log.interpret (Node.jsConsoleHandler loggerConfig)
  # FS.interpret Node.nodeFsHandler
  # ProcessEffect.interpret Node.nodeProcessHandler
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
    Right command -> launchAff_ (run command)
  where
  asked err = Console.log (ArgParser.printArgError err)

  failed err = liftEffect do
    Console.error err
    Process.exit' 1

  -- the file read first, and what it says of messages taken for the run
  run command = runNode Log.defaultLoggerConfig (loaded (configOf command)) >>= case _ of
    Left err -> failed err
    Right config ->
      let
        loggerConfig = Log.defaultLoggerConfig
          { minLevel = config.options.logLevel
          , color = not config.options.monochrome
          }
      in
        runNode loggerConfig (program command config) >>= case _ of
          Right _ -> pure unit
          Left err -> failed err
