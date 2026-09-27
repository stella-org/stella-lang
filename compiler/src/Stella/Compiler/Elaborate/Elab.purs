-- | The host's side of the elaboration boundary: the state a compile-time
-- | session holds, the transaction an attempt runs in, and the operations
-- | anything above reaches the mechanism through (D39).
-- |
-- | **Three outcomes are distinguished, and the difference between the last two
-- | is what the scheduler rests on.** `Done` carries a result, `Failed` a
-- | diagnostic about the program, and `Postponed` neither: it says the goal
-- | cannot be decided yet and names what would decide it (D40).
-- |
-- | **A defect is outside those three.** The mechanism driven against its
-- | contract, or an invariant of its own found broken, is no judgement about the
-- | program and nothing catches one; keeping it apart is what stops a search from
-- | reading it as a candidate that did not work out.
-- |
-- | **Every assignment to `Ψ` is made through one entry.** What a unification
-- | assigns is owed a re-deciding of the obligations watching it and a wake of
-- | the jobs blocked on it, and an entry that installed the substitution without
-- | both would accept a solution a row constraint forbids, or leave a job asleep
-- | on an assignment that has already happened. `unify` is that entry for type
-- | equations; the judgements of `Unify` are reached through it and not directly.
module Stella.Compiler.Elaborate.Elab
  ( Tentative
  , Counters
  , SolverState
  , Cause(..)
  , Outcome(..)
  , Elab
  , runElab
  , initialState
  , throw
  , break
  , postpone
  , transact
  , unify
  , freshTypeMeta
  , assume
  , require
  , spendFuel
  , fuelRemaining
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Context (XContext)
import Stella.Compiler.Elaborate.Context as Context
import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Kind (XKind)
import Stella.Compiler.Elaborate.Obligation (Basis(..), Breach(..), Obligation, ObligationStore, emptyStore, introduce, recheck)
import Stella.Compiler.Elaborate.Pending (EqualityGoal, Site)
import Stella.Compiler.Elaborate.Row (XRowError)
import Stella.Compiler.Elaborate.Scheduler (Scheduler, emptyScheduler, wake)
import Stella.Compiler.Elaborate.Type (MetaVar, XConstraint, XType(..))
import Stella.Compiler.Elaborate.Unify (MetaContext, UnifyError(..), UnifyProgress, UnifyResult(..), emptyContext, freshMeta, substitute, unifyType)
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | What an attempt owns, and what a rollback restores entire.
-- |
-- | Everything here would otherwise **accumulate** across attempts: a duplicate
-- | metavariable, an obligation taken on twice, a wake an abandoned attempt
-- | performed. The supplies of fresh names are part of it — the counters inside
-- | `metas`, and the scheduler's — so that the names a job takes are a function
-- | of the state it runs against rather than of how many times it has run.
-- |
-- | `written` is every metavariable the current attempt has assigned. A
-- | postponement the mechanism raises names it beside what the equation was
-- | blocked on, since a row refinement can leave a fresh tail as the only name a
-- | later equation is stuck on and what would change the re-run is a solution for
-- | one of the metavariables whose refinement produced it. A rollback restores it
-- | with the rest, so the assignments of a candidate a search tried and discarded
-- | are none of the goal's dependencies.
-- |
-- | **It is the one field here that belongs to a single attempt.** Whoever begins
-- | an attempt empties it and whoever ends one empties it again; left standing, the
-- | assignments of a job that has already committed would be among the
-- | dependencies the next postponement is derived from, and a goal would be woken
-- | by work that had nothing to do with it.
type Tentative =
  { metas :: MetaContext
  , obligations :: ObligationStore
  , scheduler :: Scheduler
  , written :: Set MetaVar
  }

-- | What a rollback leaves alone.
-- |
-- | Fuel bounds the loop's retries, and fuel restored with the rest would let a
-- | goal that postpones unconditionally run forever. Nothing here is part of what
-- | an attempt owns.
-- |
-- | **The split is structural.** A rollback replaces `tentative` and keeps this,
-- | so which half a field stands in is the whole of what decides its fate, and
-- | nothing has to remember to save or to skip one.
type Counters =
  { fuel :: P.Int
  }

type SolverState =
  { tentative :: Tentative
  , counters :: Counters
  }

-- | Why an attempt ended without a result, which is what decides how the
-- | metavariables it waits on are derived.
data Cause
  -- | A `postpone` raised above the mechanism, naming the metavariables it waits
  -- | on. Admission takes the set as it stands: a name that cannot wake the job
  -- | is a defect in whoever postponed rather than something to wait out.
  = ExplicitPostponement (Set MetaVar)
  -- | A postponement the mechanism's own unification raised. `blockedOn` is what
  -- | the equation could not decide between, and `written` is what the attempt
  -- | had assigned when it met it. The dependencies are **extracted** from the
  -- | two rather than taken, a metavariable the attempt created being one no
  -- | assignment can reach once the rollback has deleted it.
  | SolverStuck
      { blockedOn :: Set MetaVar
      , written :: Set MetaVar
      }

-- | What running an `Elab` action reached.
-- |
-- | The first three are the outcomes of a goal, and the three-way split among
-- | them is what the scheduler rests on. **`Broke` is outside that split**: it
-- | says nothing about the program, and no checkpoint catches it, so a defect
-- | reaches the top of the session rather than being read as a candidate that did
-- | not work out.
data Outcome a
  = Done a
  | Postponed Cause
  | Failed Diagnostic
  | Broke Defect

-- | The state is threaded through every outcome and not only through `Done`.
-- |
-- | What an abandoned run leaves behind is what a rollback is defined against:
-- | the counters it spent are kept while everything else is restored, so the
-- | state a failure or a postponement reached has to reach the frame that
-- | catches it.
newtype Elab a = Elab (SolverState -> Tuple (Outcome a) SolverState)

runElab :: forall a. SolverState -> Elab a -> Tuple (Outcome a) SolverState
runElab s (Elab f) = f s

initialState :: P.Int -> SolverState
initialState fuel =
  { tentative:
      { metas: emptyContext
      , obligations: emptyStore
      , scheduler: emptyScheduler
      , written: Set.empty
      }
  , counters: { fuel }
  }

throw :: forall a. Diagnostic -> Elab a
throw diagnostic = Elab \s -> Tuple (Failed diagnostic) s

-- | Report a defect, which nothing catches.
-- |
-- | This is not how a program is rejected. It is for what leaves no sound way to
-- | continue: the mechanism driven against its contract, or an invariant of its
-- | own found broken.
break :: forall a. Defect -> Elab a
break defect = Elab \s -> Tuple (Broke defect) s

-- | Abandon the attempt until one of the metavariables named is assigned.
-- |
-- | Nothing of the abandoned run is kept: the goal is run again from its
-- | beginning against the state the host has by then, so no continuation is
-- | saved (D40).
postpone :: forall a. Set MetaVar -> Elab a
postpone ms = postponeWith (ExplicitPostponement ms)

postponeWith :: forall a. Cause -> Elab a
postponeWith cause = Elab \s -> Tuple (Postponed cause) s

-- | A checkpoint over what an attempt owns, for trying something that may not
-- | work out.
-- |
-- | **What it catches is a diagnostic, and a postponement propagates.** The two
-- | mean opposite things where this is used: a failure says the candidate under
-- | trial is not the one, so the search takes the next, while a postponement says
-- | nothing about the candidate — it says the goal cannot be decided yet. One
-- | that was caught here would have a search reject a candidate for lack of
-- | information and commit to whatever came after it.
-- |
-- | **A defect propagates too, and is the one of the three that means the session
-- | cannot go on.** A search that read one as a failure would take the next
-- | candidate with the defect reported nowhere.
-- |
-- | Everything but a success is rolled back, by one rule rather than three: what
-- | a checkpoint holds is what an attempt owns, and whether anything goes on to
-- | read it is the business of whoever catches the outcome. A propagating
-- | postponement carries the cause it was raised with, which is what the attempt
-- | had written on the way to the point it got stuck at; what the rollback takes
-- | back is the state, so the writes of a candidate that **failed** are absent
-- | from the cause of a later postponement.
transact :: forall a. Elab a -> Elab (Either Diagnostic a)
transact action = Elab \s -> case runElab s action of
  Tuple (Done a) s' ->
    Tuple (Done (Right a)) s'
  Tuple (Failed diagnostic) s' ->
    Tuple (Done (Left diagnostic)) (rollbackTo s.tentative s')
  Tuple (Postponed cause) s' ->
    Tuple (Postponed cause) (rollbackTo s.tentative s')
  Tuple (Broke defect) s' ->
    Tuple (Broke defect) (rollbackTo s.tentative s')

-- | One unit of the loop's budget.
-- |
-- | What exhaustion means is the loop's to decide; this spends and reports
-- | nothing.
spendFuel :: Elab Unit
spendFuel = Elab \s -> Tuple (Done unit) (s { counters { fuel = s.counters.fuel - 1 } })

fuelRemaining :: Elab P.Int
fuelRemaining = Elab \s -> Tuple (Done s.counters.fuel) s

-- | `Γ ; κ ⊢ τ1 ≡ τ2`, together with everything its assignments owe.
-- |
-- | Five things happen here, and no caller can do fewer: the tentative `Ψ` the
-- | unification reached is installed, the obligations watching what it assigned
-- | are re-decided against the site each came from, a breach among them is a
-- | failure, the jobs blocked on those metavariables are woken, and the write set
-- | the attempt carries grows by them.
-- |
-- | **The last four are owed whether the equation solved or became stuck.** A
-- | unification assigns as it descends, so it can refine a metavariable and then
-- | meet a sub-equation it cannot decide; a caller that registered such an
-- | outcome as insufficient information would leave a constraint that is already
-- | broken for nothing to find, and the job would be woken to fail later or not
-- | at all. That is what makes this one operation rather than a judgement with
-- | bookkeeping left to whoever calls it.
-- |
-- | **A failure installs nothing.** The equation is rolled back entire, whether
-- | unification refused it or an obligation did, so no assignment is left for
-- | anything to be decided against and no wake is owed.
-- |
-- | What the site supplies is the kind variables a kind metavariable created here
-- | may mention and the place a failure is reported. **What decides the
-- | substitutions is not it** but the site each obligation carries.
unify :: Site -> EqualityGoal -> Elab Unit
unify site goal = do
  metas <- metaContext
  case unifyType { kindVars: site.context.kindVars } metas goal.kind goal.left goal.right of
    Mismatch err
      | misuse err -> break (UnifierMisuse site.origin err)
      | otherwise -> throw (EquationFailed site.origin err)
    Solved progress ->
      settle site progress
    Stuck { progress, blockedOn } -> do
      settle site progress
      written <- writtenSoFar
      postponeWith (SolverStuck { blockedOn, written })

-- | Which of a unification's errors is about the caller rather than about the
-- | program.
-- |
-- | **Every constructor is listed rather than falling through a wildcard.** The
-- | two kinds of error share one type, so what tells them apart is a decision
-- | made once per error; a wildcard would enrol whatever is added next among the
-- | ones a search may catch, which is the side that hides a defect.
misuse :: UnifyError -> P.Boolean
misuse = case _ of
  -- Driven against the contract: a dependency no assignment can wake, a
  -- metavariable the context does not hold, and a journal nobody has drained.
  MetaUnbound _ -> true
  MetaAlreadyAssigned _ -> true
  KindMetaUnbound _ -> true
  AssignmentsUnread _ -> true

  -- Statements about the program: two sides no substitution equates, a solution
  -- that would let a variable escape the binder it belongs to, an equation this
  -- judgement declines at higher rank, and a side that is no row where the kind
  -- it stands at says one.
  RowMismatch _ _ -> false
  RigidTailRemains _ -> false
  OccursCheck _ _ -> false
  PayloadMismatch _ _ _ -> false
  EscapingVariable _ _ -> false
  EscapingKindVariable _ _ -> false
  KindMismatch _ _ _ -> false
  KindNotEqual _ _ -> false
  KindOccursCheck _ _ -> false
  KindEscapingVariable _ _ -> false
  KindNotQuantifiable _ -> false
  KindDoesNotProduceType _ -> false
  TypeNotEqual _ _ -> false
  ConstraintNotEqual _ _ -> false
  CannotSolveAcrossForall _ _ -> false
  NotARow _ -> false

-- | What every assignment a unification made owes, in the order it is owed.
-- |
-- | The zonk the obligations are re-decided through is the one the installed
-- | context gives, so what each is decided about is the solution as it now
-- | stands. A wake is performed only once they all hold: a breach is a failure of
-- | the equation, and a job queued before it was found would be left on the ready
-- | queue by an equation that never happened.
settle :: Site -> UnifyProgress -> Elab Unit
settle site progress = Elab \s ->
  let
    installed = s.tentative { metas = progress.metas }
  in
    case recheck (substitute progress.metas) progress.assigned installed.obligations of
      Left (Tuple obligation breach) ->
        Tuple (broken site obligation breach) s
      Right obligations ->
        Tuple (Done unit)
          ( s
              { tentative = installed
                  { obligations = obligations
                  , scheduler = wakeAll progress.assigned installed.scheduler
                  , written = Set.union installed.written progress.assigned
                  }
              }
          )

-- | What a broken obligation is, which is not always a fact about the program.
-- |
-- | Five of the six ways one breaks are the author's: a solution carrying a key
-- | that was forbidden, two rows given a key in common, a rigid tail on either
-- | side that nothing proves the constraint of, and a site whose own assumptions
-- | cannot all hold. The sixth is a subject with no row normal form, and a row
-- | constraint names only a row metavariable, so nothing the author wrote produces
-- | one.
broken :: forall a. Site -> Obligation -> Breach -> Outcome a
broken site obligation breach = case invariantBreach breach of
  Just err ->
    Broke (ObligationSubjectNotARow obligation.origin err)

  Nothing ->
    Failed
      ( ObligationBroken
          { equation: site.origin
          , obligation: obligation.origin
          , basis: obligation.basis
          , breach
          }
      )

-- | Listed one by one for the reason `misuse` is.
invariantBreach :: Breach -> Maybe XRowError
invariantBreach = case _ of
  ObligationNotARow err -> Just err
  SolutionCarriesKey _ -> Nothing
  LacksUnprovenAtSite _ _ -> Nothing
  SidesShareKey _ -> Nothing
  DisjointUnprovenAtSite _ _ -> Nothing
  SiteFactsFailed _ -> Nothing

-- | A type metavariable at the kind given, created under the context given.
-- |
-- | Its scope is the type and kind variables that context binds, which is what a
-- | solution may mention. The name it takes comes from the supply in `Ψ`, which
-- | a rollback restores.
freshTypeMeta :: XContext -> XKind -> Elab XType
freshTypeMeta context kind = Elab \s ->
  let
    scope =
      { types: Map.keys context.tyVars
      , kinds: context.kindVars
      }
    Tuple m metas = freshMeta { kind, scope } s.tentative.metas
  in
    Tuple (Done (XMeta m)) (s { tentative { metas = metas } })

-- | Assume a row constraint at a site, returning the context that carries it.
-- |
-- | **Recording the assumption and holding it are one act.** The context is what
-- | a site's facts are derived from, and the `Assumed` obligation is what refuses
-- | an assignment making the constraint unsatisfiable, which no fact derived from
-- | a flexible tail does. Where the constraint is already unsatisfiable the
-- | assumption is rejected, and neither the context nor the store changes.
assume :: Site -> XConstraint -> Elab XContext
assume site constraint = do
  let
    context = Context.assume site.context constraint
  take { constraint, basis: Assumed, context, origin: site.origin }
  pure context

-- | Require a row constraint of what the site builds.
-- |
-- | The obligation carries the site's context, and a rigid tail entering the
-- | constraint has to be proved from that context's facts. Where it is not, the
-- | requirement is rejected and the store does not change.
require :: Site -> XConstraint -> Elab Unit
require site constraint =
  take { constraint, basis: Required, context: site.context, origin: site.origin }

-- | Introduce an obligation, decided against what `Ψ` has solved now.
-- |
-- | A breach is classified as `broken` classifies one: a subject with no row
-- | normal form is a defect, and anything else is a diagnostic naming the site
-- | the constraint came from.
take :: Obligation -> Elab Unit
take obligation = Elab \s ->
  case introduce (substitute s.tentative.metas) obligation s.tentative.obligations of
    Left breach -> case invariantBreach breach of
      Just err ->
        Tuple (Broke (ObligationSubjectNotARow obligation.origin err)) s
      Nothing ->
        Tuple
          ( Failed
              ( ObligationRejected
                  { obligation: obligation.origin
                  , basis: obligation.basis
                  , breach
                  }
              )
          )
          s
    Right (Tuple _ obligations) ->
      Tuple (Done unit) (s { tentative { obligations = obligations } })

-- | What a unification is given.
-- |
-- | Its journal is empty: `settle` installs the context a unification reported,
-- | which has it drained, and nothing else here writes one. That is what makes a
-- | unification's refusal of an undrained journal a statement about a caller
-- | outside this module.
metaContext :: Elab MetaContext
metaContext = Elab \s -> Tuple (Done s.tentative.metas) s

writtenSoFar :: Elab (Set MetaVar)
writtenSoFar = Elab \s -> Tuple (Done s.tentative.written) s

wakeAll :: Set MetaVar -> Scheduler -> Scheduler
wakeAll ms scheduler =
  foldl (\acc m -> wake m acc) scheduler (Set.toUnfoldable ms :: P.Array MetaVar)

-- | The counters are the state the abandoned run left, and everything else is the
-- | checkpoint's.
rollbackTo :: Tentative -> SolverState -> SolverState
rollbackTo saved s = { tentative: saved, counters: s.counters }

instance Functor Elab where
  map f action = Elab \s -> case runElab s action of
    Tuple (Done a) s' -> Tuple (Done (f a)) s'
    Tuple (Postponed cause) s' -> Tuple (Postponed cause) s'
    Tuple (Failed diagnostic) s' -> Tuple (Failed diagnostic) s'
    Tuple (Broke defect) s' -> Tuple (Broke defect) s'

instance Apply Elab where
  apply = ap

instance Applicative Elab where
  pure a = Elab \s -> Tuple (Done a) s

instance Bind Elab where
  bind action f = Elab \s -> case runElab s action of
    Tuple (Done a) s' -> runElab s' (f a)
    Tuple (Postponed cause) s' -> Tuple (Postponed cause) s'
    Tuple (Failed diagnostic) s' -> Tuple (Failed diagnostic) s'
    Tuple (Broke defect) s' -> Tuple (Broke defect) s'

instance Monad Elab

derive instance Eq Cause
derive instance Generic Cause _

instance Show Cause where
  show x = genericShow x

derive instance Eq a => Eq (Outcome a)
derive instance Generic (Outcome a) _

instance Show a => Show (Outcome a) where
  show x = genericShow x
