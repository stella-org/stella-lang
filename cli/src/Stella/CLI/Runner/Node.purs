module Stella.CLI.Runner.Node where

import Prelude

import Data.Either (Either(..))
import Dodo as Dodo
import Dodo.Ansi (foreground)
import Dodo.Ansi as Ansi
import Effect.Aff (attempt, makeAff, nonCanceler)
import Effect.Class.Console as Console
import Effect.Exception (message)
import Node.Buffer as Buffer
import Data.Array as Array
import Data.String (Pattern(..), Replacement(..))
import Data.String as String
import Data.Bifunctor (bimap, lmap)
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Node.FS.Perms as Perms
import Node.Glob.Basic (expandGlobs)
import Node.Path as Path
import Run (AFF, EFFECT, Run, liftEffect)
import Run as Run
import Control.Promise (Promise, toAffE)
import Data.Argonaut.Core (caseJsonObject, toString)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Data.Nullable (Nullable, toMaybe, toNullable)
import Stella.CLI.Effect.Process (Output(..), Process(..))
import Stella.CLI.Effect.Transport (Channel, ChannelEvent(..), Transport(..))
import Stella.Compiler.Bytecode.Bytes (Bytes)
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
  WriteBytes path bytes reply -> do
    buffer <- Run.liftEffect (Buffer.fromArray bytes)
    written <- Run.liftAff (attempt (FS.writeFile path buffer))
    pure (reply (lmap message written))
  WriteText path text reply -> do
    written <- Run.liftAff (attempt (FS.writeTextFile UTF8 path text))
    pure (reply (lmap message written))
  MakeDirectory path reply -> do
    made <- Run.liftAff (attempt (FS.mkdir' path { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }))
    pure (reply (lmap message made))
  IsAbsolute path reply -> pure (reply (Path.isAbsolute path))
  Glob root patterns reply -> do
    found <- Run.liftAff (attempt (expandGlobs root patterns))
    pure (reply (bimap message (Array.sort <<< map (slashed <<< Path.relative root) <<< Array.fromFoldable) found))
  where
  -- a path the effect hands out has `/` between its segments, whatever the host
  -- separates them with
  slashed path = if Path.sep == "/" then path else String.replaceAll (Pattern Path.sep) (Replacement "/") path

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

-- | A session channel on this host is a socket: descriptor 3 of this process, or
-- | the pipe a child was started with.
-- |
-- | **This is the only place that knows the channel is a socket.** What crosses up is
-- | a `Channel` over `Bytes` and `Aff`, so the session logic above names no host.
nodeTransportHandler :: forall r. Transport ~> Run (EFFECT + r)
nodeTransportHandler = case _ of
  OwnChannel reply -> do
    opened <- Run.liftEffect (ownChannelImpl Left Right)
    pure (reply (map channelFrom opened))

-- | Starting a session process on this host is spawning it with descriptor 3 as a
-- | bidirectional pipe.
nodeProcessHandler :: forall r. Process ~> Run (EFFECT + r)
nodeProcessHandler = case _ of
  SpawnSession launch reply -> do
    raw <- Run.liftEffect $ spawnSessionImpl launch.command launch.args case launch.output of
      Inherit -> toNullable Nothing
      Drain handlers -> toNullable (Just handlers)
    pure $ reply
      { channel: map channelFrom (toMaybe raw.channel)
      , exit: makeAff \done -> do
          raw.onExit \e -> done
            (Right { code: toMaybe e.code, signal: toMaybe e.signal, error: toMaybe e.error })
          pure nonCanceler
      , kill: raw.kill
      }

channelFrom :: RawChannel -> Channel
channelFrom raw =
  { send: sendImpl raw
  , receive: makeAff \done -> do
      receiveImpl raw Received Ended Failed (done <<< Right)
      pure nonCanceler
  , end: makeAff \done -> do
      endImpl raw (done (Right unit))
      pure nonCanceler
  , destroy: destroyImpl raw
  }

foreign import data RawChannel :: Type

foreign import sendImpl :: RawChannel -> Bytes -> Effect Unit
foreign import receiveImpl
  :: RawChannel
  -> (Bytes -> ChannelEvent)
  -> ChannelEvent
  -> (String -> ChannelEvent)
  -> (ChannelEvent -> Effect Unit)
  -> Effect Unit

foreign import endImpl :: RawChannel -> Effect Unit -> Effect Unit
foreign import destroyImpl :: RawChannel -> Effect Unit
foreign import ownChannelImpl
  :: (String -> Either String RawChannel)
  -> (RawChannel -> Either String RawChannel)
  -> Effect (Either String RawChannel)

type RawExit = { code :: Nullable Int, signal :: Nullable String, error :: Nullable String }

foreign import spawnSessionImpl
  :: String
  -> Array String
  -> Nullable { stdout :: String -> Effect Unit, stderr :: String -> Effect Unit }
  -> Effect
       { channel :: Nullable RawChannel
       , onExit :: (RawExit -> Effect Unit) -> Effect Unit
       , kill :: Effect Unit
       }
