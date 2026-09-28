-- | Driving a synthesis attempt as a conversation: a host script run against
-- | it, or commands answered one at a time.
-- |
-- | Both drive the same conversation with the same operations, and a guest on
-- | Steam is answered by `command`.
module Stella.Compiler.Elaborate.Drive
  ( runSynthesizer
  , command
  ) where

import Prelude

import Stella.Compiler.Elaborate.Accept (acceptResult)
import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic)
import Stella.Compiler.Elaborate.Elab (SessionEnv, SolverState)
import Stella.Compiler.Elaborate.Facade (Synthesizer)
import Stella.Compiler.Elaborate.Facade.Internal (Facade(..))
import Stella.Compiler.Elaborate.Interpret (interpret)
import Stella.Compiler.Elaborate.Pending (PendingId)
import Stella.Compiler.Elaborate.Protocol (TransactionToken)
import Stella.Compiler.Elaborate.Request (Command(..), CommandAnswer(..))
import Stella.Compiler.Elaborate.Run (Attempt, Conversation, Envelope, OpenResult(..), Response(..), Step(..), abandon, beginTransaction, commitTransaction, envelopeOf, finishAttempt, openAttempt, request)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), uncurry)

-- | Attempt the synthesis job named with the synthesizer given: the attempt
-- | opened, the synthesizer given its goal and run request by request, and the
-- | Expr it ends in accepted as the goal's solution.
-- |
-- | A job with no goal has nothing to give a synthesizer, and is a defect of
-- | whoever asked for one to be run.
runSynthesizer :: SessionEnv -> Synthesizer -> PendingId -> SolverState -> Tuple Attempt SolverState
runSynthesizer session synthesizer id s0 = case openAttempt session id s0 of
  OpenStopped attempt s -> Tuple attempt s
  Opened conversation -> case conversation.goal of
    Nothing -> abandon conversation NoGoal
    Just goal -> case run conversation (synthesizer goal) of
      Completed result c -> finishAttempt (envelopeOf c) (acceptResult result) c
      Aborted token _ c -> abandon c (UnmatchedCandidateFailure token)
      Ended attempt s -> Tuple attempt s

-- Where running a script leaves the conversation.
data Run a
  -- | The script ended in the value given.
  = Completed a Conversation
  -- | A failure was answered inside the transaction named, now closed.
  | Aborted TransactionToken Diagnostic Conversation
  -- | The attempt ended.
  | Ended Attempt SolverState

-- Run the script given, each request made where the conversation stands.
--
-- A `Transact` opens a transaction and runs its body. **A failure answered
-- inside it is matched by the transaction's token**: the body's own resumes the
-- script after the `Transact`, and one naming another transaction is passed on
-- to the `Transact` that opened it.
run :: forall a. Conversation -> Facade a -> Run a
run conversation = case _ of
  Pure a -> Completed a conversation
  Ask kernelRequest next ->
    case request (envelopeOf conversation) (interpret kernelRequest) conversation of
      Answered (Returned answer) c -> case next answer of
        Just script -> run c script
        Nothing -> uncurry Ended (abandon c (AnswerShapeMismatch kernelRequest answer))
      Answered (CandidateFailed token diagnostic) c -> Aborted token diagnostic c
      Finished attempt s -> Ended attempt s
  Transact body onFailure ->
    case beginTransaction (envelopeOf conversation) conversation of
      Answered (Returned token) c1 -> case run c1 body of
        Completed after c2 -> case commitTransaction (envelopeOf c2) c2 of
          Answered (Returned _) c3 -> run c3 after
          Answered (CandidateFailed failed diagnostic) c3 -> Aborted failed diagnostic c3
          Finished attempt s -> Ended attempt s
        Aborted failed diagnostic c2
          | failed == token -> run c2 (onFailure diagnostic)
          | otherwise -> Aborted failed diagnostic c2
        Ended attempt s -> Ended attempt s
      Answered (CandidateFailed failed diagnostic) c1 -> Aborted failed diagnostic c1
      Finished attempt s -> Ended attempt s

-- | Answer one command where the conversation stands, as the envelope says it
-- | does.
command :: Envelope -> Command -> Conversation -> Step CommandAnswer
command envelope = case _ of
  Kernel kernelRequest -> \c -> answered KernelAnswered (request envelope (interpret kernelRequest) c)
  BeginTransaction -> \c -> answered TransactionBegun (beginTransaction envelope c)
  CommitTransaction -> \c -> answered (const TransactionCommitted) (commitTransaction envelope c)
  Finish result -> \c -> uncurry Finished (finishAttempt envelope (acceptResult result) c)
  where
  answered :: forall a. (a -> CommandAnswer) -> Step a -> Step CommandAnswer
  answered f = case _ of
    Answered (Returned a) c -> Answered (Returned (f a)) c
    Answered (CandidateFailed token diagnostic) c -> Answered (CandidateFailed token diagnostic) c
    Finished attempt s -> Finished attempt s
