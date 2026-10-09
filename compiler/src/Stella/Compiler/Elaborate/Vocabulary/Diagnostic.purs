-- | What a failure reports, in the two kinds there are.
-- |
-- | A **diagnostic** is a statement about the program being compiled. It is what
-- | a `Failed` attempt holds: the mechanism raises one it has built, by
-- | `raiseDiagnostic`, and a synthesizer's `throw` carries a message the host
-- | makes one of. It is one of the three outcomes a goal has: one says the goal
-- | cannot be decided yet, this one that it cannot be decided at all.
-- |
-- | A **defect** is a statement about the mechanism, or about what drove it, and
-- | it is no outcome of a goal. The two are kept apart because what may be caught
-- | differs: a search tries a candidate and reads a failure as "not this one",
-- | which is right for a diagnostic and hides a defect.
module Stella.Compiler.Elaborate.Vocabulary.Diagnostic
  ( Diagnostic(..)
  , Defect(..)
  , Inadmissible(..)
  , MalformedGoal(..)
  , BuildError(..)
  , Warning
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin)
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle, HandleError, ScopeId)
import Stella.Compiler.Elaborate.Vocabulary.Message (FrozenMessagePart, GoalSummary)
import Stella.Compiler.Elaborate.Vocabulary.Envelope (ConversationId, TransactionToken)
import Stella.Compiler.Elaborate.Vocabulary.Request (Command, CommandAnswer, KernelAnswer, KernelRequest)
import Stella.Compiler.Elaborate.Mechanism.Kinding (KindingFault)
import Stella.Compiler.Elaborate.Mechanism.Obligation (Basis, Breach)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job, PendingId, SynthRef)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (Invariant)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (TermError)
import Stella.Compiler.Elaborate.CorePlus.Term (FitId, TermMetaVar)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XType)
import Stella.Compiler.Elaborate.CorePlus.Row (XRowError, XRowNormalForm)
import Stella.Compiler.Elaborate.Mechanism.Unify (UnifyError)
import Stella.Compiler.TypedCore (EffName, Ident, JoinName, OpName, Qualified, RegionName, RowKey, TyName, TyVar)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
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
  -- | A synthesizer's `throw`: the goal it was running, and the message it
  -- | built, frozen where it was thrown.
  | SynthesisFailed { goal :: GoalSummary, message :: P.Array FrozenMessagePart }
  -- | A fit whose source performs what its target cannot hold, reported where
  -- | the fit was placed: what is left of each row once what the two share has
  -- | cancelled.
  | RowNotContained Origin { source :: XRowNormalForm, target :: XRowNormalForm }
  -- | A checking boundary whose body performs what the row expected of it cannot
  -- | hold, which only an implicit handler could take it to: what is left of
  -- | each once what the two share has cancelled.
  | BoundaryNotContained Origin { source :: XRowNormalForm, target :: XRowNormalForm }

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
  -- | A request over types asked for what it cannot do — a builder for what
  -- | cannot be built, an equation or a goal over types no build scope admits or
  -- | at kinds that cannot meet: a synthesizer's misuse of the kernel, not a
  -- | candidate that does not fit, which is what `unify` inside a `transact`
  -- | decides.
  | BuildRejected BuildError
  -- | A metavariable handle naming what `Ψ` does not hold. A handle is issued for
  -- | a metavariable `Ψ` holds and is invalidated by the rollback that could
  -- | remove it, so this is an invariant of the host broken.
  | MetaAbsent MetaVar
  -- | An attempt ending in success with binders still open, named by the scopes
  -- | their bodies are built in. What was built under one — an obligation proved
  -- | from its assumption, a job, a metavariable — would commit without the
  -- | type that carries it.
  | BindersLeftOpen (Set ScopeId)
  -- | A request naming a conversation other than the one the runner holds: one
  -- | arriving from an attempt that has ended, or not addressed to this one.
  | ConversationMismatch { holding :: ConversationId, named :: ConversationId }
  -- | A request naming another transaction as its innermost than the one the
  -- | conversation holds: the synthesizer went on inside a transaction a failure
  -- | has closed, or outside one still open.
  | TransactionMismatch { holding :: Maybe TransactionToken, named :: Maybe TransactionToken }
  -- | An attempt finished with transactions still open, innermost first.
  | TransactionsLeftOpen (P.Array TransactionToken)
  -- | A commit with no transaction open.
  | NoTransactionToCommit
  -- | A session that has identified every conversation it can. An identifier
  -- | is never issued twice, which is what a late request failing to match
  -- | rests on.
  | ConversationsExhausted
  -- | A conversation that has issued every transaction token it can, for the
  -- | reason `ConversationsExhausted` gives.
  | TransactionsExhausted
  -- | A candidate failure answered in a transaction the script driving the
  -- | conversation has not opened: the driver and the conversation disagree on
  -- | which transactions are open, an invariant of the host broken.
  | UnmatchedCandidateFailure TransactionToken
  -- | A kernel request answered in another shape than the request is answered
  -- | in: a defect of whoever answered it.
  | AnswerShapeMismatch KernelRequest KernelAnswer
  -- | A command answered in another shape than the command is answered in: a
  -- | defect of whoever answered it.
  | CommandAnswerMismatch Command CommandAnswer
  -- | A synthesizer's result not built in the root scope of its goal. Only
  -- | there does what the result may mention agree with where the goal stands.
  | ResultNotAtRoot Handle
  -- | A term issued in a scope whose join points do not include one it jumps to.
  -- | Every builder checks what it is given against the scope, so this is an
  -- | invariant of the host broken.
  | JoinsOutOfScope (Set JoinName)
  -- | A name the catalog calls a constructor and the constructor table does not
  -- | hold. The two are assembled from one signature, so this is an invariant of
  -- | the host broken.
  | ConstructorTableMismatch (Qualified Ident)
  -- | An effect the kinding environment declares and the effect table does not
  -- | hold. The two are assembled from one signature.
  | EffectTableMismatch (Qualified EffName)
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
  -- | A command a guest synthesizer sent, a canonical value that does not read as
  -- | one, as where and why. A typed guest builds none: the value came from a
  -- | module no compiler produced, or a transport that altered it.
  | GuestCommandUnreadable P.String
  -- | What a guest synthesizer returned, which does not read as a handle, as why.
  -- | The guest has finished, so the attempt ends here rather than answering it.
  | GuestResultUnreadable P.String
  -- | An answer the host built for a guest synthesizer that has no form a guest
  -- | reads, as why: host text holding an unpaired surrogate, which nothing the
  -- | compiler produces holds.
  | GuestAnswerUnwritable P.String
  -- | A guest synthesizer that faulted as it ran, as the synthesizer and what the
  -- | interpreter said. A fault is no statement about the program being compiled:
  -- | the synthesizer's code went wrong, whatever the goal.
  | SynthesizerFaulted SynthRef P.String
  -- | A guest synthesizer that used up the steps its invocation was allowed, as
  -- | the synthesizer and the budget. This policy under this bound reached no
  -- | conclusion, which says nothing about whether the goal has one.
  | SynthesizerExhausted SynthRef P.Int
  -- | A guest synthesizer that broke the runtime contract a well-typed guest keeps
  -- | where its implementations keep to their declared types: it returned what is
  -- | no handle, or asked with a value the wire has no form for. Code no compiler
  -- | produced does, and so does a foreign implementation breaking its declaration.
  | GuestValueOutsideContract SynthRef P.String
  -- | A session not set up to run the synthesizer: its module or global missing,
  -- | not a function, or the kernel callback not in force.
  | GuestSessionUnprepared SynthRef P.String
  -- | A request the session refused, as its code and detail. The session goes on.
  | GuestRequestRejected P.String
  -- | A session lost or broken while it ran a guest, as how.
  | GuestSessionBroke P.String
  -- | The interpreter running a guest reached a defect of its own, as what was
  -- | reported.
  | InterpreterDefect P.String
  -- | A session that has named every attempt it can: an attempt, once named, is
  -- | never named again, so the session is replaced rather than asked for more.
  | GuestAttemptsExhausted
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
  -- | A fit attempted, or read, under an identifier `Ψ` does not hold.
  | FitAbsent FitId
  -- | A side of a fit with no row normal form. Both sides are rows of
  -- | `Row Effect` by the premise of whoever placed the fit.
  | FitSideNotARow Origin XRowError
  -- | A flexible tail of a fit's side that `Ψ` does not hold. A tail two sides
  -- | share would otherwise cancel into an equality, and one on a side alone be
  -- | waited on by a job no assignment wakes.
  | FitTailUnbound Origin MetaVar
  -- | A fit still undecided where its term is made Core, every fit being
  -- | decided or reported before that.
  | FitLeftUndecided FitId
  -- | A checking boundary whose ambient row `Ψ` does not hold unsolved: only the
  -- | boundary assigns it.
  | BoundaryRowAbsent MetaVar
  -- | A metavariable two owners of the resolution of fits share, which keeps
  -- | their components from being resolved apart.
  | OwnersShareMetavariable MetaVar
  -- | A postponement met by the resolution of fits, which runs outside every
  -- | attempt and has nothing to postpone.
  | ResolutionPostponed

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

-- | Why a request over types refused.
data BuildError
  -- | A type built in a scope that is neither the one given nor one of its
  -- | ancestors, or observed where no builder may use it: under a binder, or in a
  -- | catalog scheme not yet instantiated.
  = ScopeViolation Handle
  -- | What was asked for is not well-kinded.
  | IllKinded KindingFault
  -- | `instantiateForall` given a type that is not a `forall`, or `typeApply` a
  -- | term claimed at one.
  | NotAForall Handle
  -- | `termApply` given a term claimed at a type that is not a function.
  | NotAFunction Handle
  -- | `constraintApply` given a term claimed at a type that is not constrained.
  | NotConstrained Handle
  -- | A lambda closed with an effect row that is not a row of effects.
  | NotAnEffectRow Handle
  -- | A `letrec` closed with another number of right-hand sides than it binds.
  | LetRecArity Handle P.Int P.Int
  -- | A join point used where it is not in scope, or a term mentioning one used
  -- | where that join point is not: outside the `letjoin` that binds it, or
  -- | under an abstraction, whose body jumps to no join point outside it.
  | JoinOutOfScope Handle
  -- | A jump with another number of arguments than its join point takes.
  | JumpArity Handle P.Int P.Int
  -- | A tree node asked for in a scope that stands in no decision tree.
  | NotATreeScope Handle
  -- | An occurrence read in the tree of another `case`.
  | OccurrenceOfAnotherCase Handle
  -- | A tree used in the tree of another `case`.
  | TreeOfAnotherCase Handle
  -- | A name the constructor table does not hold, and the catalog does not call a
  -- | constructor.
  | UnknownConstructor (Qualified Ident)
  -- | A switch over constructors of more than one data type, or of another data
  -- | type than its occurrence is claimed at.
  | NotAConstructorOf (Qualified TyName) (Qualified Ident)
  -- | An occurrence switched on by constructor whose type no solution makes the
  -- | data type they build.
  | NotOfDataType Handle
  -- | An occurrence a field is read from whose type no solution makes a record.
  | NotARecord Handle
  -- | An occurrence switched on by key whose type no solution makes a variant.
  | NotAVariant Handle
  -- | A key the occurrence's row does not carry and no solution can add.
  | FieldAbsent Handle RowKey
  -- | A key the occurrence's row carries with a payload that is not a type.
  | PayloadNotAType Handle RowKey
  -- | A switch with one constructor, literal, or key twice.
  | DuplicateBranch Handle
  -- | A switch closed with another number of branches than it was opened with.
  | BranchCount Handle P.Int P.Int
  -- | A switch closed with a default it was not opened with, or without one it
  -- | was.
  | DefaultMismatch Handle
  -- | A `case` closed with no result type over a tree that reaches no leaf.
  | NoLeaf Handle
  -- | An operation the effect does not declare.
  | UnknownOperation (Qualified EffName) OpName
  -- | An operation given another number of type arguments than it binds.
  | OperationArity OpName P.Int P.Int
  -- | A handler given a clause for one operation twice, or none for one of its
  -- | effect's operations.
  | DuplicateClause OpName
  | MissingClause OpName
  -- | A handler closed with another number of clause bodies than it was opened
  -- | with, or a `region` with another number of initial values than it has
  -- | cells.
  | ClauseCount Handle P.Int P.Int
  | InitialValueCount Handle P.Int P.Int
  -- | A layout giving one key twice.
  | DuplicateCell RowKey
  -- | A cell read or written in a scope the region does not stand around, or one
  -- | the region does not hold.
  | NoRegion Handle
  | CellAbsent RowKey
  -- | A `region` whose body is claimed at a type mentioning the region, which
  -- | would let a reference into the region outlive it.
  | RegionEscapes RegionName
  -- | A binder closed in a scope other than the one it was opened in, or by the
  -- | operation that closes another sort of binder.
  | BinderMisuse Handle
  -- | A binder closed a second time.
  | BinderClosed Handle
  -- | A binder closed while one opened inside its body is still open.
  | EnclosesOpenBinder Handle
  -- | A row element whose payload is not of the sort its key admits.
  | EntryMismatch RowKey
  -- | A region element where an effect's is wanted: a `perform` and a handler
  -- | name an effect, and a region is none.
  | RegionEntryForbidden
  -- | `KindAnyRow` given where a kind is asked for. It is evidence a row may
  -- | carry, and no kind.
  | AnyRowAsKind
  -- | A type variable the scope does not bind.
  | UnboundTypeVariable TyVar
  -- | A value variable the scope does not bind.
  | UnboundVariable Ident
  -- | A name the catalog does not hold.
  | UnknownScheme (Qualified Ident)
  -- | A scheme instantiated with another number of kinds than it binds.
  | SchemeArity (Qualified Ident) P.Int P.Int
  -- | An equation between types whose kind evidence cannot meet: two exact kinds
  -- | that differ, or a row against something that is not one. Every kind a
  -- | handle holds is settled, so this is known before anything is unified.
  | KindsDiffer Handle Handle
  -- | A type that a goal is asked at which does not stand at `Type`.
  | NotAType Handle

-- | A synthesizer's `warn`: the goal it was running, and the message it built,
-- | frozen where it was said. A warning does not end the attempt, and is kept
-- | only where the attempt commits.
type Warning = { goal :: GoalSummary, message :: P.Array FrozenMessagePart }

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
