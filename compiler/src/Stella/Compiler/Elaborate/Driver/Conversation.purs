-- | Driving a synthesis attempt as a conversation: commands answered one at a
-- | time, and a host script run as the commands it makes.
-- |
-- | **Every command passes through `command`**, whoever sends it: a script is
-- | run by sending the commands a guest on Steam would send, so the two are
-- | driven, answered, and traced by the one dispatcher. A session that traces
-- | records each attempt opened and each command handled there, as it is
-- | handled.
module Stella.Compiler.Elaborate.Driver.Conversation
  ( openConversation
  , command
  , runSynthesizer
  , runSynthesizerWith
  , abandoned
  , cancelled
  ) where

import Prelude

import Stella.Compiler.Elaborate.Kernel.Accept (acceptResult)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic)
import Stella.Compiler.Elaborate.Kernel.Elab (SessionEnv, SolverState)
import Stella.Compiler.Elaborate.Protocol.Facade (Synthesizer)
import Stella.Compiler.Elaborate.Protocol.Facade.Internal (Facade(..))
import Stella.Compiler.Elaborate.Protocol.Interpret (interpret)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), PendingId, SynthRef, goalOf)
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle)
import Stella.Compiler.Elaborate.Vocabulary.Envelope (Envelope, TransactionToken)
import Stella.Compiler.Elaborate.Vocabulary.Request (Command(..), CommandAnswer(..))
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt, Conversation, OpenResult(..), Response(..), Step(..), abandon, beginTransaction, commitTransaction, envelopeOf, finishAttempt, openAttempt, request)
import Stella.Compiler.Elaborate.Vocabulary.Trace (TraceEvent(..), TraceReply(..), Tracing(..))
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- | Open an attempt of the job named, as `openAttempt` does, and record where it
-- | opened or why it did not.
openConversation :: SessionEnv -> PendingId -> SolverState -> OpenResult
openConversation session id s0 = case openAttempt session id s0 of
  Opened c ->
    Opened (c { state = traced session (AttemptOpened { conversation: c.id, pending: id, goal: c.goal }) c.state })
  OpenStopped attempt s ->
    OpenStopped attempt (traced session (AttemptNotOpened { pending: id, outcome: attempt }) s)

-- | Answer one command where the conversation stands, as the envelope says it
-- | does, and record it with its reply.
command :: Envelope -> Command -> Conversation -> Step CommandAnswer
command envelope sent c = recorded case sent of
  Kernel kernelRequest -> answered KernelAnswered (request envelope (interpret kernelRequest) c)
  BeginTransaction -> answered TransactionBegun (beginTransaction envelope c)
  CommitTransaction -> answered (const TransactionCommitted) (commitTransaction envelope c)
  Finish result -> case finishAttempt envelope (acceptResult result) c of
    Tuple attempt s -> Finished attempt s
  where
  answered :: forall a. (a -> CommandAnswer) -> Step a -> Step CommandAnswer
  answered f = case _ of
    Answered (Returned a) c' -> Answered (Returned (f a)) c'
    Answered (CandidateFailed token diagnostic) c' -> Answered (CandidateFailed token diagnostic) c'
    Finished attempt s -> Finished attempt s

  recorded = case _ of
    Answered (Returned a) c' -> Answered (Returned a) (c' { state = record (Replied a) c'.state })
    Answered (CandidateFailed token diagnostic) c' ->
      Answered (CandidateFailed token diagnostic) (c' { state = record (FailedCandidate token diagnostic) c'.state })
    Finished attempt s -> Finished attempt (record (Ended attempt) s)

  record reply = traced c.session
    (CommandHandled { conversation: c.id, pending: c.pending.id, envelope, command: sent, reply })

-- | `runSynthesizerWith` with the synthesizer given, which is run whatever
-- | synthesizer the goal names.
runSynthesizer :: SessionEnv -> Synthesizer -> PendingId -> SolverState -> Tuple Attempt SolverState
runSynthesizer session synthesizer = runSynthesizerWith session (const (Just synthesizer))

-- | Attempt the synthesis job named: the attempt opened, the synthesizer its
-- | goal names resolved, given the goal and run as the commands it makes, and
-- | the Expr it ends in sent to finish the attempt with.
-- |
-- | **The name is resolved after the attempt opens and its target is checked**,
-- | so a job whose target is malformed is reported as that first. Where the
-- | lookup finds no synthesizer, the session was set up without it: that is a
-- | defect, and the attempt is abandoned before any command is sent. A job with
-- | no goal has nothing to give a synthesizer, and is a defect of whoever asked
-- | for one to be run.
runSynthesizerWith :: SessionEnv -> (SynthRef -> Maybe Synthesizer) -> PendingId -> SolverState -> Tuple Attempt SolverState
runSynthesizerWith session resolve id s0 = case openConversation session id s0 of
  OpenStopped attempt s -> Tuple attempt s
  Opened conversation -> case conversation.pending.job, conversation.goal of
    JobSynthesis record, Just goal ->
      let
        named = (goalOf record).synthesizer
      in
        case resolve named of
          Nothing -> abandoned conversation (SynthesizerUnavailable named)
          Just synthesizer -> driven conversation (synthesizer goal)
    _, _ -> abandoned conversation NoGoal

-- Run the script given in the conversation, and finish the attempt with the
-- Expr it ends in.
driven :: Conversation -> Facade Handle -> Tuple Attempt SolverState
driven conversation script = case run conversation script of
  Completed result c -> case command (envelopeOf c) (Finish result) c of
    Finished attempt s -> Tuple attempt s
    Answered (Returned answer) c' -> abandoned c' (CommandAnswerMismatch (Finish result) answer)
    Answered (CandidateFailed token _) c' -> abandoned c' (UnmatchedCandidateFailure token)
  Aborted token _ c -> abandoned c (UnmatchedCandidateFailure token)
  Stopped attempt s -> Tuple attempt s

-- Where running a script leaves the conversation.
data Run a
  -- | The script ended in the value given.
  = Completed a Conversation
  -- | A failure was answered inside the transaction named, now closed.
  | Aborted TransactionToken Diagnostic Conversation
  -- | The attempt ended.
  | Stopped Attempt SolverState

-- Run the script given as commands, each sent where the conversation stands.
--
-- A `Transact` sends `BeginTransaction`, runs its body, and sends
-- `CommitTransaction` where the body ends. **A failure answered inside it is
-- matched by the transaction's token**: the body's own resumes the script after
-- the `Transact`, and one naming another transaction is passed on to the
-- `Transact` that opened it. A command answered in another shape than it is
-- answered in is a defect of the host.
run :: forall a. Conversation -> Facade a -> Run a
run conversation = case _ of
  Pure a -> Completed a conversation
  Ask kernelRequest next ->
    case command (envelopeOf conversation) (Kernel kernelRequest) conversation of
      Answered (Returned (KernelAnswered answer)) c -> case next answer of
        Just script -> run c script
        Nothing -> ended (abandoned c (AnswerShapeMismatch kernelRequest answer))
      Answered (Returned other) c -> ended (abandoned c (CommandAnswerMismatch (Kernel kernelRequest) other))
      Answered (CandidateFailed token diagnostic) c -> Aborted token diagnostic c
      Finished attempt s -> Stopped attempt s
  Transact body onFailure ->
    case command (envelopeOf conversation) BeginTransaction conversation of
      Answered (Returned (TransactionBegun token)) c1 -> case run c1 body of
        Completed after c2 -> case command (envelopeOf c2) CommitTransaction c2 of
          Answered (Returned TransactionCommitted) c3 -> run c3 after
          Answered (Returned other) c3 -> ended (abandoned c3 (CommandAnswerMismatch CommitTransaction other))
          Answered (CandidateFailed failed diagnostic) c3 -> Aborted failed diagnostic c3
          Finished attempt s -> Stopped attempt s
        Aborted failed diagnostic c2
          | failed == token -> run c2 (onFailure diagnostic)
          | otherwise -> Aborted failed diagnostic c2
        Stopped attempt s -> Stopped attempt s
      Answered (Returned other) c1 -> ended (abandoned c1 (CommandAnswerMismatch BeginTransaction other))
      Answered (CandidateFailed failed diagnostic) c1 -> Aborted failed diagnostic c1
      Finished attempt s -> Stopped attempt s
  where
  ended (Tuple attempt s) = Stopped attempt s

-- | End the attempt with the defect given, where the host finds itself at fault
-- | rather than answering a command, and record that it ended. **A driver ending
-- | an attempt goes through this** rather than `abandon`, which records nothing.
abandoned :: Conversation -> Defect -> Tuple Attempt SolverState
abandoned c defect = case abandon c defect of
  Tuple attempt s ->
    Tuple attempt (traced c.session (AttemptAbandoned { conversation: c.id, pending: c.pending.id, outcome: attempt }) s)

-- | The state an attempt cancelled from outside leaves: rolled back to where it
-- | opened, what is retained kept, and the cancellation recorded.
-- |
-- | **It is the last state of a compilation called off, and nothing resumes from
-- | it.** The job the attempt ran stays as it was taken, pending and on neither
-- | the ready queue nor the blocked table, so a loop handed this state again
-- | would find a job no assignment can reach. What is kept is what no rollback
-- | restores — the identifiers issued — so nothing issued in the attempt is
-- | issued again.
cancelled :: Conversation -> SolverState
cancelled c = traced c.session
  (AttemptCancelled { conversation: c.id, pending: c.pending.id })
  { tentative: c.root, retained: c.state.retained }

traced :: SessionEnv -> TraceEvent -> SolverState -> SolverState
traced session event s = case session.tracing of
  TraceDisabled -> s
  TraceEnabled -> s { retained { trace = Array.snoc s.retained.trace event } }
