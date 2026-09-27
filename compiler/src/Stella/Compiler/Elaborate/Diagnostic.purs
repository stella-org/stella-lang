-- | What a failure reports, in the two kinds there are.
-- |
-- | A **diagnostic** is a statement about the program being compiled. It is what
-- | `throw` carries and what a `Failed` attempt holds, and it is one of the three
-- | outcomes a goal has: one says the goal cannot be decided yet, this one that
-- | it cannot be decided at all.
-- |
-- | A **defect** is a statement about the mechanism, or about what drove it, and
-- | it is no outcome of a goal. The two are kept apart because what may be caught
-- | differs: a search tries a candidate and reads a failure as "not this one",
-- | which is right for a diagnostic and hides a defect.
module Stella.Compiler.Elaborate.Diagnostic
  ( Diagnostic(..)
  , Defect(..)
  , Inadmissible(..)
  , MalformedGoal(..)
  , BuildError(..)
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Context (Origin)
import Stella.Compiler.Elaborate.Handle (Handle, HandleError, ScopeId)
import Stella.Compiler.Elaborate.Kinding (KindingFault)
import Stella.Compiler.Elaborate.Obligation (Basis, Breach)
import Stella.Compiler.Elaborate.Pending (Job, PendingId, SynthRef)
import Stella.Compiler.Elaborate.Scheduler (Invariant)
import Stella.Compiler.Elaborate.TermMeta (TermError)
import Stella.Compiler.Elaborate.Term (TermMetaVar)
import Stella.Compiler.Elaborate.Type (MetaVar, XType)
import Stella.Compiler.Elaborate.Row (XRowError)
import Stella.Compiler.Elaborate.Unify (UnifyError)
import Stella.Compiler.TypedCore (Ident, Qualified, RowKey, TyVar)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Generic.Rep (class Generic)
import Data.Set (Set)
import Data.Show.Generic (genericShow)

data Diagnostic
  -- | An equation no substitution satisfies, reported at the site it stands at.
  = EquationFailed Origin UnifyError
  -- | An assignment that broke a row constraint.
  -- |
  -- | **Two places are named because two are involved.** `equation` is where the
  -- | assignment was made, and `obligation` is the site the constraint came
  -- | from, whose facts are what decided it; the two are one site only by
  -- | coincidence. `basis` says which of the two it was — an assumption the
  -- | assignment made unsatisfiable, or a requirement it left unproved.
  | ObligationBroken
      { equation :: Origin
      , obligation :: Origin
      , basis :: Basis
      , breach :: Breach
      }
  -- | A row constraint that does not hold where it is introduced: an assumption
  -- | already unsatisfiable, or a requirement its site does not prove. No
  -- | equation is involved, so the one place named is the site the constraint
  -- | came from.
  | ObligationRejected
      { obligation :: Origin
      , basis :: Basis
      , breach :: Breach
      }
  -- | A term metavariable's solution that mentions what its scope excludes, or
  -- | would contain the metavariable itself, reported at the site assigning it.
  | TermAssignmentFailed Origin TermError

-- | Something the mechanism, or whoever drove it, got wrong.
-- |
-- | **Nothing catches one, and that is the whole of why it is not a diagnostic.**
-- | A checkpoint is for trying a candidate that may not work out, and what says a
-- | candidate did not is a diagnostic; a defect says the solver was driven
-- | against its contract or has broken an invariant of its own. Caught as a
-- | failure, it would send a search on to the next candidate with the defect
-- | reported nowhere — or reported to the author as a type error, about a program
-- | nothing is wrong with.
data Defect
  -- | What a unification reports about **its caller**: a metavariable `Ψ` does
  -- | not hold or holds solved already, a kind metavariable it does not hold, or
  -- | a journal of assignments nobody has acted on. Another candidate repairs
  -- | none of them.
  = UnifierMisuse Origin UnifyError
  -- | The subject of a row constraint zonked to something with no row normal
  -- | form. Only a row metavariable is named by a row constraint, so this is an
  -- | invariant of the solver rather than a property of the program. The origin
  -- | is the site the obligation came from, that being where the constraint was
  -- | taken on.
  | ObligationSubjectNotARow Origin XRowError
  -- | A term metavariable assigned that `Ψ` does not hold or holds solved
  -- | already. Another candidate repairs neither.
  | TermMisuse Origin TermError
  -- | A postponement no assignment could ever wake, naming the job that raised
  -- | it and the site that job stands at. What is wrong is whoever postponed —
  -- | a synthesizer that read a type it did not zonk, or held a metavariable
  -- | across an attempt — and not the program.
  | PostponementInadmissible
      { origin :: Origin
      , job :: Job
      , reason :: Inadmissible
      }
  -- | A handle that names no object of the class it was presented as. What
  -- | presented it is at fault: a synthesizer holding a handle across an
  -- | attempt, or a transport that altered one.
  | InvalidHandle Handle HandleError
  -- | A session that has issued every generation it can. A generation is never
  -- | issued twice, which is what an old handle failing to match rests on.
  | GenerationsExhausted
  -- | A builder asked for what cannot be built: a synthesizer's misuse of the
  -- | kernel, not a candidate that does not fit, which is what `unify` inside a
  -- | `transact` decides.
  | BuildRejected BuildError
  -- | An attempt ending in success with binders still open, named by the scopes
  -- | their bodies are built in. What was built under one — an obligation proved
  -- | from its assumption, a job, a metavariable — would commit without the
  -- | type that carries it.
  | BindersLeftOpen (Set ScopeId)
  -- | A kernel operation that reads where it stands, run with no frame: outside
  -- | any attempt. The host called it where it had no site to give.
  | NoFrame
  -- | A goal observed where the frame holds none: an equality job's attempt, or
  -- | none at all.
  | NoGoal
  -- | A goal handle presented for one goal while the frame runs another. The
  -- | scope a goal's type is read under is the running goal's site.
  | GoalNotCurrent PendingId PendingId
  -- | A type the read-only kinding judgement refused, or one whose kind it could
  -- | not settle. What reaches a synthesizer is well-kinded and settled, whoever
  -- | built it, so meeting another is the host's fault.
  | KindingFailed KindingFault
  -- | A row observation asked of a type that stands at no row kind, or of a row
  -- | with no normal form.
  | NotARowType Handle
  -- | A synthesis goal whose synthesizer the session has no implementation for.
  -- | Name resolution resolved the name where the goal was written, so the name
  -- | exists; a session unable to run it was set up without it.
  | SynthesizerUnavailable SynthRef
  -- | A synthesis job whose target is not what the one operation that creates
  -- | the two would have made. Nothing the author wrote produces one.
  | MalformedSynthesisJob PendingId MalformedGoal
  -- | A job attempted under an identifier `pending` does not hold.
  | PendingAbsent PendingId
  -- | A job attempted while the scheduler still holds it: on the ready queue, or
  -- | awaiting a metavariable. Attempting it would leave it to run again, or
  -- | register it a second time.
  | PendingStillScheduled PendingId
  -- | Jobs left at quiescence that no assignment can reach: `pending` holds
  -- | them, they await nothing, and the ready queue is empty. The loop has
  -- | lost them, which says nothing about the program. In identifier order.
  | UnreachablePending (NonEmptyArray PendingId)
  -- | The scheduler's tables disagree at quiescence, in the order `invariants`
  -- | lists them. A job registered under a metavariable its `awaiting` does not
  -- | name, or awaiting one it is not registered under, is one no assignment
  -- | wakes, so reporting it as waiting would blame the program for the loop.
  | SchedulerBroken (NonEmptyArray Invariant)

-- | How a synthesis job's target disagrees with its goal, read against `Ψ` as
-- | it stands where the job is about to be attempted.
data MalformedGoal
  -- | A target `Ψ` does not hold.
  = TargetAbsent TermMetaVar
  -- | A target solved already. The runner assigns it and completes the job in
  -- | one attempt, so a job still pending has an unsolved one.
  | TargetSolved TermMetaVar
  -- | A target at a type other than the goal's, compared once both are zonked.
  | TargetTypeDiffers XType XType
  -- | A target whose scope admits what the site's context does not bind. A scope
  -- | narrower than the site's is admitted: a target standing in another
  -- | solution is narrowed with it.
  | TargetScopeWider TermMetaVar

-- | Why a builder refused.
data BuildError
  -- | A type built in a scope that is neither the one given nor one of its
  -- | ancestors, or observed where no builder may use it: under a binder, or in a
  -- | catalog scheme not yet instantiated.
  = ScopeViolation Handle
  -- | What was asked for is not well-kinded.
  | IllKinded KindingFault
  -- | `instantiateForall` given a type that is not a `forall`.
  | NotAForall Handle
  -- | A binder closed in a scope other than the one it was opened in, or by the
  -- | operation that closes another sort of binder.
  | BinderMisuse Handle
  -- | A binder closed a second time.
  | BinderClosed Handle
  -- | A binder closed while one opened inside its body is still open.
  | EnclosesOpenBinder Handle
  -- | A row element whose payload is not of the sort its key admits.
  | EntryMismatch RowKey
  -- | A region element. Only the handler owning a region introduces or removes
  -- | one.
  | RegionEntryForbidden
  -- | `KindAnyRow` given where a kind is asked for. It is evidence a row may
  -- | carry, and no kind.
  | AnyRowAsKind
  -- | A type variable the scope does not bind.
  | UnboundTypeVariable TyVar
  -- | A name the catalog does not hold.
  | UnknownScheme (Qualified Ident)
  -- | A scheme instantiated with another number of kinds than it binds.
  | SchemeArity (Qualified Ident) P.Int P.Int

-- | Why a postponement cannot be admitted, read against `Ψ` as the rollback
-- | leaves it.
data Inadmissible
  -- | A postponement naming no metavariable at all.
  = AwaitsNothing
  -- | A metavariable `Ψ` does not hold. After the rollback this is also what a
  -- | metavariable the attempt itself created is.
  | AwaitsAbsent MetaVar
  -- | A metavariable `Ψ` holds solved already, whose assignment has happened.
  | AwaitsSolved MetaVar
  -- | A postponement the mechanism raised, none of whose dependencies survived
  -- | the rollback unsolved.
  | NothingDurable

derive instance Eq Diagnostic
derive instance Generic Diagnostic _

instance Show Diagnostic where
  show x = genericShow x

derive instance Eq Defect
derive instance Generic Defect _

instance Show Defect where
  show x = genericShow x

derive instance Eq BuildError
derive instance Generic BuildError _

instance Show BuildError where
  show x = genericShow x

derive instance Eq MalformedGoal
derive instance Generic MalformedGoal _

instance Show MalformedGoal where
  show x = genericShow x

derive instance Eq Inadmissible
derive instance Generic Inadmissible _

instance Show Inadmissible where
  show x = genericShow x
