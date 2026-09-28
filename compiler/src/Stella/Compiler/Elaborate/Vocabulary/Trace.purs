-- | A record of what a synthesizer asked of a session, and what it was
-- | answered.
-- |
-- | **A trace is the conversation as the host saw it**: every attempt opened, and
-- | every command it handled with the envelope it came in and the reply it was
-- | given, in order. It is what a runner in the host and a guest on Steam are
-- | compared by, and not a log of the scheduler: only a synthesis attempt,
-- | driven by commands, is traced, and an equality job, which has none, is not.
-- |
-- | **A trace is only appended to.** It is kept where no rollback reaches, so a
-- | command a rollback undid stays in it, and what became of each event — kept,
-- | rolled back, not yet decided — is computed from the order of the events by
-- | `fates` rather than written into them.
-- |
-- | Recording is chosen per session: a compilation traces nothing, and a test,
-- | a comparison of runners, or a debugger turns it on.
module Stella.Compiler.Elaborate.Vocabulary.Trace
  ( Tracing(..)
  , TraceEvent(..)
  , TraceReply(..)
  , Fate(..)
  , fates
  , commandsOf
  , canonicalCommands
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Vocabulary.Outcome (Attempt(..))
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic)
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle(..))
import Stella.Compiler.Elaborate.Mechanism.Pending (PendingId)
import Stella.Compiler.Elaborate.Vocabulary.Envelope (ConversationId, Envelope, TransactionToken)
import Stella.Compiler.Elaborate.Vocabulary.Request (Command, CommandAnswer(..), traverseCommandHandles)
import Data.Array as Array
import Data.Foldable (foldl)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..), fst, snd)

-- | Whether a session records its trace.
data Tracing
  = TraceDisabled
  | TraceEnabled

data TraceEvent
  -- | A synthesis attempt opened as the conversation named, its goal given the
  -- | handle named.
  = AttemptOpened
      { conversation :: ConversationId
      , pending :: PendingId
      , goal :: Maybe Handle
      }
  -- | An attempt that stopped before it opened. No conversation is named: one
  -- | that ran out of identifiers was never given one.
  | AttemptNotOpened
      { pending :: PendingId
      , outcome :: Attempt
      }
  -- | A command the conversation named handled, with the envelope it came in.
  | CommandHandled
      { conversation :: ConversationId
      , pending :: PendingId
      , envelope :: Envelope
      , command :: Command
      , reply :: TraceReply
      }
  -- | An attempt the host ended at its own fault rather than in reply to a
  -- | command.
  | AttemptAbandoned
      { conversation :: ConversationId
      , pending :: PendingId
      , outcome :: Attempt
      }

-- | What a command was answered.
data TraceReply
  = Replied CommandAnswer
  -- | A failure inside the transaction named, which was rolled back and closed.
  | FailedCandidate TransactionToken Diagnostic
  -- | The attempt ended.
  | Ended Attempt

-- | What became of an event.
data Fate
  -- | What it did is part of what the attempt committed.
  = Kept
  -- | What it did was rolled back: by a failure in its transaction or in one
  -- | around it, or by the attempt ending without a result.
  | RolledBack
  -- | Not yet decided: the conversation had not ended where the trace ends.
  | Pending
  -- | Nothing was run: an attempt that did not open.
  | NotRun

-- An open transaction of a conversation, or its attempt, with the events that
-- happened inside it and are decided with it. `token` is `Nothing` for the
-- attempt.
type Frame = { token :: Maybe TransactionToken, events :: P.Array P.Int }

-- | The fate of each event, in the order of the trace.
-- |
-- | An event is decided with the innermost transaction open around it: a
-- | failure answered in that transaction rolls it back, and a commit hands it to
-- | the transaction around, so that one committed inside a transaction later
-- | rolled back is rolled back too. The attempt decides what is left: all of it
-- | kept where the attempt commits, and rolled back otherwise.
fates :: P.Array TraceEvent -> P.Array Fate
fates events = Array.mapWithIndex (\i _ -> fromMaybe Pending (Map.lookup i final.decided)) events
  where
  final = foldlWithIndex step { open: Map.empty, decided: Map.empty } events

  step i acc = case _ of
    AttemptNotOpened _ -> acc { decided = Map.insert i NotRun acc.decided }
    AttemptOpened e -> acc { open = Map.insert e.conversation [ { token: Nothing, events: [ i ] } ] acc.open }
    AttemptAbandoned e -> case Map.lookup e.conversation acc.open of
      Nothing -> acc { decided = Map.insert i NotRun acc.decided }
      Just frames -> ended e.conversation e.outcome frames
    CommandHandled e -> case Map.lookup e.conversation acc.open of
      Nothing -> acc { decided = Map.insert i NotRun acc.decided }
      Just frames -> case e.reply of
        Replied (TransactionBegun token) ->
          acc { open = Map.insert e.conversation (Array.cons { token: Just token, events: [ i ] } frames) acc.open }
        Replied TransactionCommitted -> case Array.uncons (within i frames) of
          Just { head: closed, tail: rest } -> case Array.uncons rest of
            Just { head: around, tail: outer } ->
              acc { open = Map.insert e.conversation (Array.cons (around { events = around.events <> closed.events }) outer) acc.open }
            Nothing -> acc { open = Map.insert e.conversation [ closed ] acc.open }
          Nothing -> acc
        Replied _ -> acc { open = Map.insert e.conversation (within i frames) acc.open }
        FailedCandidate _ _ -> case Array.uncons (within i frames) of
          Just { head: closed, tail: rest } ->
            acc { open = Map.insert e.conversation rest acc.open, decided = decide RolledBack closed.events acc.decided }
          Nothing -> acc
        Ended attempt -> ended e.conversation attempt frames
    where
    ended conversation attempt frames =
      let
        fate = if attempt == Committed then Kept else RolledBack
      in
        acc
          { open = Map.delete conversation acc.open
          , decided = decide fate (Array.concatMap _.events (within i frames)) acc.decided
          }

  within :: P.Int -> P.Array Frame -> P.Array Frame
  within i frames = case Array.uncons frames of
    Just { head: top, tail: rest } -> Array.cons (top { events = Array.snoc top.events i }) rest
    Nothing -> [ { token: Nothing, events: [ i ] } ]

  decide :: Fate -> P.Array P.Int -> Map P.Int Fate -> Map P.Int Fate
  decide fate indices decided = foldl (\m i -> Map.insert i fate m) decided indices

-- | The commands the conversation named handled, in order.
commandsOf :: ConversationId -> P.Array TraceEvent -> P.Array Command
commandsOf conversation = Array.mapMaybe case _ of
  CommandHandled e | e.conversation == conversation -> Just e.command
  _ -> Nothing

-- | The commands with each handle renamed by the order it first appears in.
-- |
-- | Two attempts of one goal issue their handles in the same order where they
-- | make the same requests, but not with the same generations, which a session
-- | never issues twice; renamed, the commands two such attempts send are equal
-- | exactly where they ask the same of the same objects.
canonicalCommands :: P.Array Command -> P.Array Command
canonicalCommands commands = map (snd <<< traverseCommandHandles (\h -> Tuple unit (renamed h))) commands
  where
  seen = Array.nub (Array.concatMap (fst <<< traverseCommandHandles (\h -> Tuple [ h ] h)) commands)
  order = Map.fromFoldable (Array.mapWithIndex (\i h -> Tuple h i) seen)
  renamed h@(Handle fields) = case Map.lookup h order of
    Just i -> Handle (fields { slot = i, generation = i })
    Nothing -> h

derive instance Eq Tracing
derive instance Generic Tracing _

instance Show Tracing where
  show x = genericShow x

derive instance Eq TraceEvent
derive instance Generic TraceEvent _

instance Show TraceEvent where
  show x = genericShow x

derive instance Eq TraceReply
derive instance Generic TraceReply _

instance Show TraceReply where
  show x = genericShow x

derive instance Eq Fate
derive instance Ord Fate
derive instance Generic Fate _

instance Show Fate where
  show x = genericShow x
