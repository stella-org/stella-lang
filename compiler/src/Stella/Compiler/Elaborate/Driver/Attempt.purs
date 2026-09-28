-- | Running `Elab` from outside: one attempt of a pending job, held open across
-- | a synthesizer's requests where it has several, and the admission of what a
-- | postponed attempt waits on (D40).
-- |
-- | An attempt is a boundary and not a combinator of `Elab`. What it reaches is
-- | handed back as the `Outcome` it is, so a defect is never a value some later
-- | step could go on from.
module Stella.Compiler.Elaborate.Driver.Attempt
  ( module Exports
  , Runner
  , runAttempt
  , admit
  , hostRunner
  , attemptPending
  , attemptPendingWith
  , Conversation
  , OpenResult(..)
  , Response(..)
  , Step(..)
  , envelopeOf
  , innermost
  , openAttempt
  , request
  , beginTransaction
  , commitTransaction
  , finishAttempt
  , abandon
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic, Inadmissible(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle, HandleObject(..), emptyArena)
import Stella.Compiler.Elaborate.Kernel.Elab (Cause(..), Elab, Frame, Outcome(..), SessionEnv, SolverState, Tentative, break, checkSynthesisTarget, issue, requireClosed, runElabIn, unify, withFrame)
import Stella.Compiler.Elaborate.Vocabulary.Outcome (Attempt(..))
import Stella.Compiler.Elaborate.Vocabulary.Outcome (Attempt(..)) as Exports
import Stella.Compiler.Elaborate.Vocabulary.Envelope (Envelope) as Exports
import Stella.Compiler.Elaborate.Vocabulary.Envelope (Envelope, ConversationId(..), TransactionToken(..))
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Pending, PendingId, goalOf)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (complete, lookupPending, reblock, unwakeable)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), MetaContext, lookupMeta)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..), uncurry)

-- | One attempt: a transaction over what it owns.
-- |
-- | **The write set is emptied before the checkpoint is taken.** The checkpoint
-- | is what a rollback restores, so a set emptied afterwards would be put back —
-- | with the previous job's assignments in it — by this attempt's own rollback,
-- | at the moment a postponement is about to read it. An abandoned attempt
-- | therefore needs no emptying of its own, and a committed one is emptied again
-- | so that nothing it wrote reaches the next job's dependencies.
-- |
-- | **The arena is emptied at the same two points, for the same reason.** A
-- | handle lives for the attempt that issued it: what a synthesizer returns is
-- | resolved before the attempt commits, and one that postpones or fails leaves
-- | the checkpoint's empty arena behind.
-- |
-- | **An action ending in success with a binder still open is a defect**, and
-- | rolls back as one. What was built under the binder would otherwise commit
-- | without the type that carries it, so every attempt is held to this here,
-- | whoever runs it.
-- |
-- | Every outcome but `Done` rolls back, what is retained being kept. The action
-- | reads the session given and no frame; `attemptPendingWith` is what runs one
-- | under a job's frame.
runAttempt :: forall a. SessionEnv -> Elab a -> SolverState -> Tuple (Outcome a) SolverState
runAttempt session action s0 =
  case runElabIn session checkpoint (action <* requireClosed) of
    Tuple (Done a) s ->
      Tuple (Done a) (s { tentative { written = Set.empty, arena = emptyArena } })
    Tuple outcome s ->
      Tuple outcome { tentative: checkpoint.tentative, retained: s.retained }
  where
  checkpoint = s0 { tentative { written = Set.empty, arena = emptyArena } }

-- | The metavariables a postponement may be registered under, read against `Ψ`
-- | as the rollback left it.
-- |
-- | A metavariable the rollback left unsolved is one that existed before the
-- | attempt and that an assignment can still reach; one the attempt created is
-- | gone, and one already solved has had its assignment.
-- |
-- | **A postponement raised above the mechanism is admitted as it stands**: every
-- | metavariable it names must be one of those, and the set may not be empty. A
-- | name that fails is a defect in whoever postponed, and dropping it instead
-- | would hide the reading that produced it.
-- |
-- | **One the mechanism raised has its dependencies extracted.** A fresh row tail
-- | can be the only thing an equation is stuck on, and it is gone after the
-- | rollback; what would change the re-run is a solution for one of the
-- | metavariables whose refinement produced it, which the attempt's write set
-- | names. So the dependencies are what survives of the two sets together, and
-- | only where nothing survives is the postponement a defect.
admit :: MetaContext -> Cause -> Either Inadmissible (Set MetaVar)
admit metas = case _ of
  ExplicitPostponement ms
    | Set.isEmpty ms -> Left AwaitsNothing
    | otherwise ->
        case Array.head (Array.mapMaybe unwakeable (Set.toUnfoldable ms)) of
          Just reason -> Left reason
          Nothing -> Right ms

  SolverStuck { blockedOn, written } ->
    let
      durable = Set.filter unsolved (Set.union blockedOn written)
    in
      if Set.isEmpty durable then Left NothingDurable else Right durable

  where
  unwakeable m = case lookupMeta metas m of
    Just (Unsolved _) -> Nothing
    Just (Assigned _) -> Just (AwaitsSolved m)
    Nothing -> Just (AwaitsAbsent m)

  unsolved m = case lookupMeta metas m of
    Just (Unsolved _) -> true
    _ -> false

-- | What carries a job out inside an attempt.
-- |
-- | The attempt, the rollback, and the admission are the same whoever runs the
-- | job, so a host implementation and a guest one running on Steam are two
-- | runners handed to the one boundary.
type Runner = Pending -> Elab Unit

-- | The host's runner, for the jobs the mechanism itself carries out. It holds
-- | no synthesizer, so a synthesis job is one it cannot run.
hostRunner :: Runner
hostRunner p = case p.job of
  JobUnify goal -> unify p.site goal
  JobSynthesis goal -> break (SynthesizerUnavailable (goalOf goal).synthesizer)

-- | `attemptPendingWith hostRunner`.
attemptPending :: SessionEnv -> PendingId -> SolverState -> Tuple Attempt SolverState
attemptPending session = attemptPendingWith session hostRunner

-- | Attempt the pending job named with the runner given, and act on the outcome:
-- | a conversation opened, the runner's action asked as its one request, and
-- | the attempt finished, so that a runner written as one action and one
-- | answering a synthesizer request by request reach the same place.
attemptPendingWith :: SessionEnv -> Runner -> PendingId -> SolverState -> Tuple Attempt SolverState
attemptPendingWith session runner id s0 = case openAttempt session id s0 of
  OpenStopped attempt s -> Tuple attempt s
  Opened conversation -> case request (envelopeOf conversation) (runner conversation.pending) conversation of
    Finished attempt s -> Tuple attempt s
    Answered _ answered -> finishAttempt (envelopeOf answered) (pure unit) answered

-- | An attempt held open across the requests a synthesizer makes, one at a
-- | time.
-- |
-- | **It attempts a job already taken, and nothing else.** Which job is attempted,
-- | and the fuel a retry spends, are the scheduler's and the loop's; a
-- | conversation is given a job just created or just taken from the ready
-- | queue, and holds the checkpoint of its attempt, the frame it runs under, and
-- | the transactions open inside it. Those are the host's to control and none of
-- | them is rolled back: the checkpoints hold what a rollback restores. The
-- | transactions stand innermost first. A synthesis job's goal is issued a Goal
-- | handle as the attempt opens, which the synthesizer is given.
type Conversation =
  { id :: ConversationId
  , session :: SessionEnv
  , pending :: Pending
  , frame :: Frame
  , root :: Tentative
  , state :: SolverState
  , goal :: Maybe Handle
  , transactions :: P.Array { token :: TransactionToken, checkpoint :: Tentative }
  , nextSerial :: P.Int
  }

-- | Opening an attempt: a conversation, or where the attempt stopped before any
-- | request, with the state as it left it.
data OpenResult
  = Opened Conversation
  | OpenStopped Attempt SolverState

-- | What a request that leaves the attempt going answers.
data Response a
  -- | What it asked for.
  = Returned a
  -- | It failed inside the transaction named, which the host has rolled back
  -- | and closed. The synthesizer goes on outside it, as `transact` returning
  -- | the diagnostic.
  | CandidateFailed TransactionToken Diagnostic

-- | Where a request leaves the conversation.
data Step a
  = Answered (Response a) Conversation
  -- | The attempt ended: a failure outside every transaction, a postponement,
  -- | or a defect, the scheduler acted on as `attemptPendingWith` acts.
  | Finished Attempt SolverState

-- | The envelope a request standing where the conversation stands carries.
envelopeOf :: Conversation -> Envelope
envelopeOf conversation = { conversation: conversation.id, transaction: innermost conversation }

-- | The transaction the conversation stands in, innermost.
innermost :: Conversation -> Maybe TransactionToken
innermost conversation = map _.token (Array.head conversation.transactions)

-- | Open an attempt of the job named, which must be one no queue holds.
-- |
-- | The conversation is identified afresh, the checkpoint taken with the write
-- | set and the arena emptied, and a synthesis job's target checked before
-- | anything is asked. An identifier is never issued twice, so where none is
-- | left the session stops, the state unchanged.
openAttempt :: SessionEnv -> PendingId -> SolverState -> OpenResult
openAttempt session id s0 = case lookupPending s0.tentative.scheduler id of
  Nothing ->
    OpenStopped (Halted (PendingAbsent id)) s0
  Just p
    | s0.retained.nextConversation >= top ->
        OpenStopped (Halted ConversationsExhausted) s0
    | not (Array.elem id (unwakeable s0.tentative.scheduler)) ->
        OpenStopped (Halted (PendingStillScheduled id)) s0
    | otherwise ->
        let
          root = s0.tentative { written = Set.empty, arena = emptyArena }
          conversation =
            { id: ConversationId s0.retained.nextConversation
            , session
            , pending: p
            , frame: frameOf p
            , goal: Nothing
            , root
            , state: s0 { tentative = root, retained { nextConversation = s0.retained.nextConversation + 1 } }
            , transactions: []
            , nextSerial: 0
            }
        in
          case request (envelopeOf conversation) (checked p) conversation of
            Answered (Returned goal) opened -> Opened (opened { goal = goal })
            Answered (CandidateFailed token _) opened -> uncurry OpenStopped (abandon opened (UnmatchedCandidateFailure token))
            Finished attempt s -> OpenStopped attempt s
  where
  -- A synthesis job's target is checked inside the attempt and before any
  -- request, so a job that fails it runs no synthesizer and is rolled back. The
  -- goal is then issued its handle.
  checked p = case p.job of
    JobSynthesis goal -> checkSynthesisTarget p.id p.site goal *> (Just <$> issue (GoalObject { id: p.id, goal }))
    JobUnify _ -> pure Nothing

  -- The site the job was created at, and its goal where it has one. Nothing
  -- inside the attempt changes either.
  frameOf p =
    { site: p.site
    , goal: case p.job of
        JobSynthesis goal -> Just { id: p.id, goal }
        JobUnify _ -> Nothing
    }

-- | Ask what the action given does, under the conversation's frame.
-- |
-- | **A failure inside a transaction is answered, not raised.** The host rolls
-- | back to the innermost transaction's checkpoint, closes it, and answers the
-- | request with the failure, so the synthesizer learns that this candidate did
-- | not hold while it still has control; it sends no request to abandon the
-- | candidate. A failure outside every transaction ends the attempt, and a
-- | postponement or a defect ends it wherever it is raised, rolled back past
-- | every transaction to the attempt's checkpoint.
-- |
-- | **The envelope must name where the conversation stands.** A request from
-- | another conversation, or one naming another innermost transaction than the
-- | host holds, is a defect of the synthesizer, and ends the attempt.
request :: forall a. Envelope -> Elab a -> Conversation -> Step a
request envelope action conversation = case mismatch envelope conversation of
  Just defect -> finished conversation (Broke defect) conversation.state
  Nothing -> case runElabIn conversation.session conversation.state (withFrame conversation.frame action) of
    Tuple (Done a) s ->
      Answered (Returned a) (conversation { state = s })
    Tuple (Failed diagnostic) s -> case Array.uncons conversation.transactions of
      Just { head: top, tail: rest } ->
        Answered (CandidateFailed top.token diagnostic)
          (conversation { state = s { tentative = top.checkpoint }, transactions = rest })
      Nothing -> finished conversation (Failed diagnostic) s
    Tuple (Postponed cause) s -> finished conversation (Postponed cause) s
    Tuple (Broke defect) s -> finished conversation (Broke defect) s

-- | Open a transaction inside the one the conversation stands in: a checkpoint
-- | of the state as it is, under a token never issued before. Where none is
-- | left the attempt stops rather than wrap around to one a late request may
-- | still carry.
beginTransaction :: Envelope -> Conversation -> Step TransactionToken
beginTransaction envelope conversation = case mismatch envelope conversation of
  Just defect -> finished conversation (Broke defect) conversation.state
  Nothing
    | conversation.nextSerial >= top ->
        finished conversation (Broke TransactionsExhausted) conversation.state
    | otherwise ->
        let
          token = TransactionToken { conversation: conversation.id, serial: conversation.nextSerial }
        in
          Answered (Returned token)
            ( conversation
                { transactions = Array.cons { token, checkpoint: conversation.state.tentative } conversation.transactions
                , nextSerial = conversation.nextSerial + 1
                }
            )

-- | Close the innermost transaction, keeping what was done inside it. The
-- | envelope names it, so a transaction closes only where it is innermost. A
-- | commit with none open is a defect.
commitTransaction :: Envelope -> Conversation -> Step Unit
commitTransaction envelope conversation = case mismatch envelope conversation, Array.uncons conversation.transactions of
  Just defect, _ -> finished conversation (Broke defect) conversation.state
  Nothing, Just { tail: rest } -> Answered (Returned unit) (conversation { transactions = rest })
  Nothing, Nothing ->
    finished conversation (Broke NoTransactionToCommit) conversation.state

-- | Finish the attempt, running the action given to accept what the synthesizer
-- | returned.
-- |
-- | **Acceptance runs inside the attempt, before it commits**: after checking
-- | that no transaction and no binder is open, and rolled back with the
-- | attempt where it fails, postpones, or breaks. Nothing commits that the
-- | acceptance has not passed.
finishAttempt :: Envelope -> Elab Unit -> Conversation -> Tuple Attempt SolverState
finishAttempt envelope accept conversation = case mismatch envelope conversation of
  Just defect -> ended conversation (Broke defect) conversation.state
  Nothing
    | not (Array.null conversation.transactions) ->
        ended conversation (Broke (TransactionsLeftOpen (map _.token conversation.transactions))) conversation.state
    | otherwise ->
        case runElabIn conversation.session conversation.state (withFrame conversation.frame (requireClosed *> accept)) of
          Tuple outcome s -> ended conversation outcome s

-- Where the envelope disagrees with the conversation.
mismatch :: Envelope -> Conversation -> Maybe Defect
mismatch envelope conversation
  | envelope.conversation /= conversation.id =
      Just (ConversationMismatch { holding: conversation.id, named: envelope.conversation })
  | envelope.transaction /= innermost conversation =
      Just (TransactionMismatch { holding: innermost conversation, named: envelope.transaction })
  | otherwise = Nothing

-- | End the attempt with the defect given, rolled back to its checkpoint: where
-- | whoever drives the conversation finds the host at fault.
abandon :: Conversation -> Defect -> Tuple Attempt SolverState
abandon conversation defect = ended conversation (Broke defect) conversation.state

finished :: forall a. Conversation -> Outcome Unit -> SolverState -> Step a
finished conversation outcome s = case ended conversation outcome s of
  Tuple attempt s' -> Finished attempt s'

-- How an attempt ends, the scheduler acted on.
--
-- Every outcome but `Done` rolls back to the attempt's checkpoint, what is
-- retained being kept. A postponement is admitted in the same step, against
-- the `Ψ` that rollback left, so no postponement reaches the scheduler
-- unchecked. A solved or failed job is removed from every table, and a defect
-- leaves the state as the rollback left it.
ended :: Conversation -> Outcome Unit -> SolverState -> Tuple Attempt SolverState
ended conversation outcome s = case outcome of
  Done _ ->
    Tuple Committed (complete' (s { tentative { written = Set.empty, arena = emptyArena } }))
  Failed diagnostic ->
    Tuple (Rejected diagnostic) (complete' rolled)
  Broke defect ->
    Tuple (Halted defect) rolled
  Postponed cause -> case admit rolled.tentative.metas cause of
    Left reason ->
      Tuple (Halted (PostponementInadmissible { origin: p.site.origin, job: p.job, reason })) rolled
    Right ms ->
      Tuple (Registered ms) (rolled { tentative { scheduler = reblock p ms rolled.tentative.scheduler } })
  where
  p = conversation.pending
  rolled = { tentative: conversation.root, retained: s.retained }
  complete' st = st { tentative { scheduler = complete p.id st.tentative.scheduler } }
