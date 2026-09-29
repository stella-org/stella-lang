-- | Two channels joined to each other in memory, for tests.
-- |
-- | What one side sends the other receives on a later turn, cut into the pieces a
-- | function gives, so a test can hand a frame over in pieces or several at once.
-- | Nothing here reaches a host: it is `Channel` as the session logic sees it.
module Test.Stella.CLI.Session.Memory (memoryPair) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Milliseconds(..), delay, makeAff, nonCanceler, runAff_)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Stella.CLI.Effect.Transport (Channel, ChannelEvent(..))
import Stella.Compiler.Bytecode.Bytes (Bytes)

type Inbox =
  { queued :: Ref (Array ChannelEvent)
  , waiters :: Ref (Array (ChannelEvent -> Effect Unit))
  , last :: Ref (Maybe ChannelEvent)
  , ended :: Ref Boolean
  }

memoryPair :: (Bytes -> Array Bytes) -> Effect { left :: Channel, right :: Channel }
memoryPair cuts = do
  a <- inbox
  b <- inbox
  pure { left: side a b, right: side b a }
  where
  inbox = { queued: _, waiters: _, last: _, ended: _ }
    <$> Ref.new []
    <*> Ref.new []
    <*> Ref.new Nothing
    <*> Ref.new false

  -- a later turn, in the order things were sent
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
    { send: \bytes -> do
        done <- Ref.read self.ended
        unless done $ for_ (cuts bytes) \piece -> later (push other (Received piece))
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
