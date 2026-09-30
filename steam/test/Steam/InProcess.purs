-- | `steam session` run in this process: the command itself, over a channel held in
-- | memory, with the interpreter tuned as a test asks.
-- |
-- | The session is the one the command serves — the same program, handlers, and
-- | queue — with two things handed in instead of taken from the host: the channel,
-- | which the client's side of an in-memory pair answers, and the stretch of steps a
-- | guest takes between two looks at the loop. The client starts it through its own
-- | `PROCESS` effect, so nothing on the client's side knows it is not a process.
module Test.Steam.InProcess
  ( openInProcess
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, Milliseconds(..), delay, forkAff, makeAff, nonCanceler, runAff_)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (Run, liftAff, runBaseAff')
import Run.Except as Except
import Steam.CLI.Effect.Tuning as Tuning
import Steam.CLI.Error (exitStatus)
import Steam.CLI.Options (Command(..))
import Steam.CLI.Program (program)
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Foreigns as Foreigns
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.CLI.Effect.Log as Log
import Stella.CLI.Effect.Process (Exit, Output(..), Process(..))
import Stella.CLI.Effect.Process as Process
import Stella.CLI.Effect.Transport (Channel, ChannelEvent(..), Transport(..))
import Stella.CLI.Effect.Transport as Transport
import Stella.CLI.Runner.Node as Node
import Stella.CLI.Session.Client (OpenFailure, Session)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.Protocol (Hello)
import Stella.Compiler.Bytecode.Bytes (Bytes)

-- | A session served in this process with the stretch given, opened with the
-- | handshake given.
openInProcess :: Int -> Hello -> Aff (Either OpenFailure Session)
openInProcess quantum hello = runBaseAff' (Process.interpret spawning (Client.open launch))
  where
  launch = { command: "steam session, in process", args: [], output: Inherit, hello }

  spawning :: Process ~> Run _
  spawning (SpawnSession _ reply) = liftAff do
    pair <- liftEffect memoryPair
    ended <- AVar.empty
    _ <- forkAff do
      outcome <- serving pair.right
      AVar.put outcome ended
    pure (reply { channel: Just pair.left, exit: AVar.read ended, kill: pair.left.destroy })

  serving :: Channel -> Aff Exit
  serving channel = program { logLevel: Error, monochrome: true, command: Session { manifest: Nothing } }
    # Log.interpret (Node.jsConsoleHandler (Log.defaultLoggerConfig { minLevel = Error, color = false }))
    # FS.interpret Node.nodeFsHandler
    # Foreigns.interpret Node.nodeForeignsHandler
    # Transport.interpret (\(OwnChannel reply) -> pure (reply (Right channel)))
    # Tuning.interpret (Tuning.tuningConfigHandler { quantum })
    # Except.runExcept
    # runBaseAff'
    <#> case _ of
      Right _ -> exitWith 0
      Left err -> exitWith (exitStatus err)

  exitWith code = { code: Just code, signal: Nothing, error: Nothing }

-- Two channels joined in memory ----------------------------------------------------------------

type Inbox =
  { queued :: Ref (Array ChannelEvent)
  , waiters :: Ref (Array (ChannelEvent -> Effect Unit))
  , last :: Ref (Maybe ChannelEvent)
  , ended :: Ref Boolean
  }

-- | Two channels joined to each other: what one side sends, the other receives on a
-- | later turn, in the order it was sent.
memoryPair :: Effect { left :: Channel, right :: Channel }
memoryPair = do
  a <- inbox
  b <- inbox
  pure { left: side a b, right: side b a }
  where
  inbox = { queued: _, waiters: _, last: _, ended: _ }
    <$> Ref.new []
    <*> Ref.new []
    <*> Ref.new Nothing
    <*> Ref.new false

  later action = runAff_ (\_ -> pure unit) (delay (Milliseconds 0.0) *> liftEffect action)

  push to event = Ref.read to.last >>= case _ of
    Just _ -> pure unit
    Nothing -> do
      case event of
        Received _ -> pure unit
        _ -> Ref.write (Just event) to.last
      waiting <- Ref.read to.waiters
      case Array.uncons waiting of
        Just { head, tail } -> do
          Ref.write tail to.waiters
          head event
        Nothing -> Ref.modify_ (_ <> [ event ]) to.queued

  side self other =
    { send: \(bytes :: Bytes) -> do
        done <- Ref.read self.ended
        unless done $ for_ [ bytes ] \piece -> later (push other (Received piece))
    , receive: makeAff \k -> do
        queued <- Ref.read self.queued
        case Array.uncons queued of
          Just { head, tail } -> do
            Ref.write tail self.queued
            k (Right head)
          Nothing -> Ref.read self.last >>= case _ of
            Just event -> k (Right event)
            Nothing -> Ref.modify_ (_ <> [ k <<< Right ]) self.waiters
        pure nonCanceler
    , end: makeAff \k -> do
        finish self other
        later (k (Right unit))
        pure nonCanceler
    , destroy: do
        finish self other
        push self Ended
    }

  finish self other = do
    done <- Ref.read self.ended
    unless done do
      Ref.write true self.ended
      later (push other Ended)
