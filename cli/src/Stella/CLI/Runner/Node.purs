module Stella.CLI.Runner.Node where

import Prelude

import Data.Either (Either(..))
import Dodo as Dodo
import Dodo.Ansi (foreground)
import Dodo.Ansi as Ansi
import Effect.Aff (attempt)
import Effect.Class.Console as Console
import Effect.Exception (message)
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Run (AFF, EFFECT, Run, liftEffect)
import Run as Run
import Stella.CLI.Effect.FS (FileSystem(..))
import Stella.CLI.Effect.Log (Log(..), LogLevel(..), LoggerConfig)
import Type.Row (type (+))

jsConsoleHandler :: forall r. LoggerConfig -> Log ~> Run (EFFECT + r)
jsConsoleHandler conf = case _ of
  Log level msg next -> do
    when (level >= conf.minLevel) do
      let
        -- a colour-coded level tag, then a space, then the (uncoloured) message.
        doc =
          if conf.minLevel > Debug then msg
          else case level of
            Debug -> foreground Ansi.Blue (Dodo.text "[DEBUG]") <> Dodo.space <> msg
            Info -> foreground Ansi.Green (Dodo.text "[INFO]") <> Dodo.space <> msg
            Warn -> foreground Ansi.Yellow (Dodo.text "[WARN]") <> Dodo.space <> msg
            Error -> foreground Ansi.Red (Dodo.text "[ERROR]") <> Dodo.space <> msg
        printed =
          if conf.color then Dodo.print Ansi.ansiGraphics Dodo.twoSpaces doc
          else Dodo.print Dodo.plainText Dodo.twoSpaces doc
        -- Error always to stderr; Warn to stderr only under `--strict`; the rest to stdout.
        emit = case level of
          Error -> Console.error
          Warn | conf.strict -> Console.error
          _ -> Console.log
      liftEffect $ emit printed
    pure next

-- | The handler for a command running on Node.
-- |
-- | **A host buffer is turned into `Bytes` here and nowhere above.** That is what
-- | keeps the representation Node chose from reaching the logic.
nodeFsHandler :: forall r. FileSystem ~> Run (AFF + EFFECT + r)
nodeFsHandler = case _ of
  ReadBytes path reply -> do
    read <- Run.liftAff (attempt (FS.readFile path))
    case read of
      Left err -> pure (reply (Left (message err)))
      Right buffer -> do
        bytes <- Run.liftEffect (Buffer.toArray buffer)
        pure (reply (Right bytes))
