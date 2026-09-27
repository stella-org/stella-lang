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
import Data.Bifunctor (lmap)
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Run (AFF, EFFECT, Run, liftEffect)
import Run as Run
import Control.Promise (Promise, toAffE)
import Data.Argonaut.Core (caseJsonObject, toString)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Foreign.Object (Object)
import Foreign.Object as Object
import Stella.CLI.Effect.FS (FileSystem(..))
import Stella.CLI.Effect.Foreigns (Foreigns(..), HostExport)
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
  ReadText path reply -> do
    read <- Run.liftAff (attempt (FS.readTextFile UTF8 path))
    pure (reply (lmap message read))

-- | Reaching a manifest entry on this host is importing the module its `specifier`
-- | names, and reading the exports off it.
-- |
-- | **This is the only place that knows what a JavaScript payload is.** The field is
-- | read here, resolved here, and imported here; nothing above this handler names a
-- | specifier at all.
-- |
-- | **A module reached stays reached**, the host's own module cache being what makes
-- | that true, so a session paying per arrival pays once per host module.
nodeForeignsHandler :: forall r. Foreigns ~> Run (AFF + EFFECT + r)
nodeForeignsHandler = case _ of
  Reach { base, entry } reply -> do
    case specifierOf entry.payload of
      Nothing -> pure (reply (Left "the entry has no `specifier`"))
      Just specifier -> do
        imported <- Run.liftAff (attempt (toAffE (importModuleImpl specifier base)))
        pure case imported of
          Left err -> reply (Left (message err))
          Right exports -> reply (Right (Map.fromFoldable (Object.toUnfoldable exports :: Array _)))
  where
  specifierOf =
    caseJsonObject Nothing (\fields -> toString =<< Object.lookup "specifier" fields)

foreign import importModuleImpl :: String -> String -> Effect (Promise (Object HostExport))
