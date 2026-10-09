-- | A pending job: the envelope every postponable thing shares, and the job
-- | inside it.
-- |
-- | Scheduling, the site, the dependency set, and the transaction are the same
-- | machinery whichever job is inside, which is why the envelope is one record
-- | and the job is a sum.
module Stella.Compiler.Elaborate.Mechanism.Pending
  ( PendingId(..)
  , Site
  , EqualityGoal
  , SynthRef
  , GoalRecord
  , newGoal
  , goalOf
  , HandlerGoal
  , Job(..)
  , Pending
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin, XContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind)
import Stella.Compiler.Elaborate.CorePlus.Term (FitId, TermMetaVar)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (freshTermMeta, termScopeOf)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaContext)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XType)
import Stella.Compiler.TypedCore (Ident, Qualified)

import Data.Generic.Rep (class Generic)
import Data.Set (Set)
import Data.Tuple (Tuple(..))
import Data.Show.Generic (genericShow)

-- | What the blocked table registers.
-- |
-- | Registering the identifier rather than the job is what lets a wake remove
-- | every entry one job has: two entries holding the job itself would have to be
-- | recognized as one.
newtype PendingId = PendingId P.Int

-- | What a job is decided against, which the kinds of job take different things
-- | from.
-- |
-- | **What an equality takes is the kind variables in scope where it was written**
-- | — a kind metavariable created while solving it may mention those and no
-- | others — and the place a failure is reported. One woken far from where it was
-- | written, creating a kind metavariable under whatever elaboration has since
-- | reached, would admit a kind variable that is out of scope at the equation or
-- | refuse one that is in it.
-- |
-- | **What a substitution must preserve is decided elsewhere.** The row
-- | constraints naming a metavariable are obligations, each holding on the
-- | assumptions of the site **it** came from — several different sites, in
-- | general, and not necessarily the one the equation stands at
-- | ([Obligation](Obligation.purs)).
type Site =
  { context :: XContext
  , origin :: Origin
  }

-- | `Γ ; κ ⊢ τ1 ≡ τ2` postponed, with the kind both sides stand at.
-- |
-- | A row equality is one of these at a row kind, its payload equations being
-- | discharged by type unification. A kind equality is never one: kind equality
-- | is syntactic (D2), so it is decided where it is met and has nothing to wait
-- | for.
type EqualityGoal =
  { kind :: XKind
  , left :: XType
  , right :: XType
  }

-- | A synthesizer, as name resolution settled it: a fully qualified global name
-- | rather than a host function, so one Core⁺ term means one thing however it
-- | travels.
type SynthRef = Qualified Ident

-- | `Synth ?m τ f`: what is particular to one synthesis goal.
-- |
-- | Where it stands is the envelope's `Site`, which the record does not repeat.
-- | `expectedType` stands at `Type`.
-- |
-- | Its constructor is not exported. **A synthesis goal's target and job are
-- | installed in one state transition, with the `Ψ` holding the target**:
-- | `createSynthesis` queues the job, from inside an attempt, and
-- | `submitSynthesis` attempts it at once, from outside every attempt. The runner
-- | checks the target against the current `Ψ` and the job's site before running
-- | a synthesizer.
newtype GoalRecord = GoalRecord
  { target :: TermMetaVar
  , expectedType :: XType
  , synthesizer :: SynthRef
  }

-- | A goal, and the term metavariable its result is assigned to, created
-- | together at `expectedType` under the site's context. The regions that
-- | context binds are the ones a result may read and write the cells of.
-- |
-- | A trusted helper of `createSynthesis` and `submitSynthesis`, each of which
-- | installs the context returned and creates the job in the same state
-- | transition. Used on its own it is outside the contract: a record paired with any other `Ψ` names a target that `Ψ` may not
-- | hold, which the runner reports as a defect.
newGoal :: Site -> XType -> SynthRef -> MetaContext -> Tuple GoalRecord MetaContext
newGoal site expectedType synthesizer ctx =
  Tuple (GoalRecord { target, expectedType, synthesizer }) ctx'
  where
  Tuple target ctx' = freshTermMeta { ty: expectedType, scope: termScopeOf site.context } ctx

goalOf :: GoalRecord -> { target :: TermMetaVar, expectedType :: XType, synthesizer :: SynthRef }
goalOf (GoalRecord goal) = goal

data Job
  = JobUnify EqualityGoal
  -- | A fit waiting on the flexible tails its decision depends on, whose record
  -- | `Ψ` holds.
  | JobEffectFit FitId
  | JobSynthesis GoalRecord
  -- | A checking boundary, decided once its body is built.
  | JobImplicitHandler HandlerGoal

-- | A checking boundary: the ambient row `?σ` its body was built under, and the
-- | row expected of it.
type HandlerGoal =
  { boundary :: MetaVar
  , expected :: XType
  }

-- | `awaiting` is the metavariables the job last postponed on.
-- |
-- | It is assigned and never accumulated: a second postponement names whatever
-- | set it names then, which need not contain what the job waited on before.
-- | Waking reads it to remove the job from every metavariable it was registered
-- | under, then empties it, so that a report at quiescence names what is still
-- | being waited on.
type Pending =
  { id :: PendingId
  , site :: Site
  , awaiting :: Set MetaVar
  , job :: Job
  }

derive instance Eq PendingId
derive instance Ord PendingId
derive newtype instance Show PendingId

derive instance Eq GoalRecord

instance Show GoalRecord where
  show (GoalRecord goal) = "(GoalRecord " <> show goal <> ")"

derive instance Eq Job
derive instance Generic Job _

instance Show Job where
  show x = genericShow x
