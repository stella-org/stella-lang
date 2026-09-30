-- | What a run of a guest comes to: an attempt ended, or a compilation called off,
-- | and whether the session that ran it goes on being used.
-- |
-- | **A fault, and a budget used up, are no statement about the program being
-- | compiled.** A synthesizer that faulted went wrong whatever the goal, and one
-- | that ran out of steps reached no conclusion under this bound; neither says the
-- | goal has no solution, so neither is rejected as the program's. The attempt is
-- | halted as a defect of what ran it, named by the synthesizer. The one way a
-- | guest rejects a goal is its own `throw`, which the attempt has already ended
-- | on.
-- |
-- | **A session is replaced where it was lost, or where it answered something about
-- | its own control that the host has no ground for** — that the host ended an
-- | attempt it did not end, or that one no one cancelled was cancelled — the two
-- | sides then disagreeing about what runs. One that refused a request, or answered
-- | that an invocation failed, answered, and goes on; whatever the defect, the
-- | process is still to be used.
module Stella.CLI.Session.Broker.Settle
  ( Settled(..)
  , settle
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Stella.CLI.Effect.Process (Exit)
import Stella.CLI.Session.Broker (Brokered(Ended, InvocationFailed, RequestRejected, SessionLost), SessionHealth(..))
import Stella.CLI.Session.Broker as Broker
import Stella.CLI.Session.Client (ClientFailure(..))
import Stella.CLI.Session.Guest (InvocationReason(Abandoned, BudgetExhausted, CommandNotEncodable, Fault, NotAToken), ValueClass)
import Stella.CLI.Session.Guest as Guest
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt, Conversation)
import Stella.Compiler.Elaborate.Driver.Conversation (abandoned)
import Stella.Compiler.Elaborate.Kernel.Elab (SolverState)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), goalOf)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..))
import Stella.Compiler.TypedCore (Ident, Qualified)

-- | What a run came to.
data Settled
  = Settled Attempt SolverState SessionHealth
  -- | The compilation was called off: the state is its last, and nothing
  -- | resumes from it.
  | Cancelled SolverState SessionHealth

-- | Settle a run of the guest given the budget given. An attempt left open is
-- | ended here, as the defect its failure is, traced as the host ending it.
settle :: { budget :: Int } -> Brokered -> Settled
settle invocation = case _ of
  Ended attempt s -> Settled attempt s Reusable
  Broker.Cancelled s health -> Cancelled s health
  InvocationFailed failure c -> case failure.reason of
    -- a session answering that the host ended or cancelled an attempt the host
    -- did neither is one not to be trusted with the next
    Abandoned -> halted c Replace (GuestSessionBroke "the session said the host ended an attempt it did not")
    Guest.Cancelled -> halted c Replace (GuestSessionBroke "the session said it cancelled an attempt no one cancelled")
    reason -> halted c Reusable case synthesizerOf c of
      Just synthesizer -> defectOf synthesizer reason failure.detail
      -- a run is begun only on a synthesis job, whose goal names its synthesizer
      Nothing -> NoGoal
  RequestRejected refusal c ->
    halted c Reusable (GuestRequestRejected (refusal.code <> ": " <> refusal.detail))
  SessionLost failure c -> case exitOf failure of
    Just exit | exit.code == Just 3 -> halted c Replace (InterpreterDefect (describe failure))
    _ -> halted c Replace (GuestSessionBroke (describe failure))
  where
  halted c health defect = case abandoned c defect of
    Tuple attempt s -> Settled attempt s health

  defectOf synthesizer reason detail = case reason of
    Fault -> SynthesizerFaulted synthesizer detail
    BudgetExhausted -> SynthesizerExhausted synthesizer invocation.budget
    NotAToken class' -> GuestValueOutsideContract synthesizer ("it returned " <> classText class' <> ", which is no handle")
    CommandNotEncodable class' -> GuestValueOutsideContract synthesizer ("it asked with " <> classText class' <> ", which the wire has no form for")
    other -> GuestSessionUnprepared synthesizer (show other <> ": " <> detail)

synthesizerOf :: Conversation -> Maybe (Qualified Ident)
synthesizerOf c = case c.pending.job of
  JobSynthesis record -> Just (goalOf record).synthesizer
  _ -> Nothing

classText :: ValueClass -> String
classText = show

exitOf :: ClientFailure -> Maybe Exit
exitOf = case _ of
  ChannelLost _ exit -> Just exit
  ExitedUnannounced exit -> Just exit
  ExitedAfterClosed exit -> Just exit
  _ -> Nothing

describe :: ClientFailure -> String
describe = show
