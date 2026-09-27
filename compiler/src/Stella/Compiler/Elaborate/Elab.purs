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
  , Retained
  , SolverState
  , Cause(..)
  , Outcome(..)
  , Elab
  , ElabEnv
  , SessionEnv
  , Frame
  , emptySessionEnv
  , runElab
  , runElabIn
  , withFrame
  , askEnv
  , currentMetas
  , initialState
  , throw
  , break
  , postpone
  , transact
  , unify
  , freshTypeMeta
  , freshTermMeta
  , createSynthesis
  , checkSynthesisTarget
  , assignTerm
  , zonkTerm
  , assume
  , require
  , issue
  , resolveGoal
  , resolveType
  , resolveExpr
  , resolveMeta
  , resolveScope
  , resolveBinder
  , freshScopeId
  , freshBinderName
  , freshIdent
  , holdOpen
  , release
  , Release(..)
  , requireClosed
  , spendFuel
  , fuelRemaining
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Catalog (ModuleCatalog, catalogOf)
import Stella.Compiler.Elaborate.Context (XContext)
import Stella.Compiler.Elaborate.Context as Context
import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic(..), MalformedGoal(..))
import Stella.Compiler.Elaborate.Kind (XKind)
import Stella.Compiler.Elaborate.Kinding (KindingEnv, emptyKindingEnv)
import Stella.Compiler.Elaborate.Handle (Arena, ExprObject, GoalObject, Handle, HandleClass(..), HandleError(..), HandleObject(..), BinderObject, ScopeId(..), ScopeObject, SessionId, TypeObject, emptyArena, issueIn, resolveIn)
import Stella.Compiler.Elaborate.Obligation (Basis(..), Breach(..), Obligation, ObligationStore, emptyStore, introduce, recheck)
import Stella.Compiler.Elaborate.Pending (EqualityGoal, GoalRecord, Job(..), PendingId, Site, SynthRef, goalOf, newGoal)
import Stella.Compiler.Elaborate.Row (XRowError)
import Stella.Compiler.Elaborate.Scheduler (Scheduler, create, emptyScheduler, enqueueInitial, wake)
import Stella.Compiler.Elaborate.Term (TermMetaVar, XExpr)
import Stella.Compiler.Elaborate.TermMeta (TermError(..), assignTermMeta, termScopeOf, zonkExpr)
import Stella.Compiler.Elaborate.TermMeta as TermMeta
import Stella.Compiler.Elaborate.Type (MetaVar, XConstraint, XType(..))
import Stella.Compiler.TypedCore (Ident(..), TyVar(..))
import Stella.Compiler.Elaborate.Unify (MetaContext, TermBinding(..), UnifyError(..), UnifyProgress, UnifyResult(..), emptyContext, freshMeta, lookupTermMeta, substitute, unifyType)
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Generic.Rep (class Generic)
import Data.Array as Array
import Data.Map (Map)
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
-- | **It and `arena` are the fields here that belong to a single attempt.**
-- | Whoever begins an attempt empties both and whoever commits one empties them
-- | again. Left standing, the assignments of a job that has already committed
-- | would be among the dependencies the next postponement is derived from, and a
-- | goal would be woken by work that had nothing to do with it; and a handle
-- | would outlive the attempt a synthesizer is obliged to hold nothing across.
-- | Inside an attempt both are transactional, as everything else here is.
-- |
-- | `names` are the supplies build scopes and the binders a builder opens draw
-- | from. They are restored by a rollback like every other supply of names, so
-- | a goal run twice against the same state opens the same scopes and binds the
-- | same names; what tells a handle from a stale one is the generation, not these.
-- |
-- | `open` holds the binders an attempt has opened and not yet closed, each
-- | named by the scope its body is built in and holding that scope's ancestors.
-- | An attempt may not end in success with one still open, and a binder may not
-- | be closed while one opened inside its body is: in either case what was built
-- | under the inner one — an obligation proved from an assumption, a job, a
-- | metavariable — would commit without a type that carries it. A rollback
-- | restores it with the rest, so a binder opened by a discarded candidate is no
-- | longer held.
type Tentative =
  { metas :: MetaContext
  , obligations :: ObligationStore
  , scheduler :: Scheduler
  , written :: Set MetaVar
  , arena :: Arena
  , names :: { nextScope :: P.Int, nextBinder :: P.Int, nextIdent :: P.Int }
  , open :: Map ScopeId (Set ScopeId)
  }

-- | What a rollback leaves alone.
-- |
-- | Fuel bounds the loop's retries, and fuel restored with the rest would let a
-- | goal that postpones unconditionally run forever. `nextGeneration` is what a
-- | handle's generation is drawn from, and one restored would hand a new object
-- | the number a handle to a deleted one carries. `session` is the identity of
-- | the session and never changes. Nothing here is part of what an attempt owns.
-- |
-- | **The split is structural.** A rollback replaces `tentative` and keeps this,
-- | so which half a field stands in is the whole of what decides its fate, and
-- | nothing has to remember to save or to skip one.
type Retained =
  { session :: SessionId
  , nextGeneration :: P.Int
  , fuel :: P.Int
  }

type SolverState =
  { tentative :: Tentative
  , retained :: Retained
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
-- | what it spent is kept while everything else is restored, so the
-- | state a failure or a postponement reached has to reach the frame that
-- | catches it.
newtype Elab a = Elab (ElabEnv -> SolverState -> Tuple (Outcome a) SolverState)

-- | What an `Elab` action reads and never changes.
-- |
-- | `session` is fixed for the whole session, assembled before the first job:
-- | the value catalog and the type-level environment. `frame` is the site and
-- | goal of the attempt running, which the runner sets and nothing inside the
-- | attempt changes; an action run outside any attempt has none.
type ElabEnv =
  { session :: SessionEnv
  , frame :: Maybe Frame
  }

type SessionEnv =
  { catalog :: ModuleCatalog
  , kinding :: KindingEnv
  }

-- | Where the running attempt stands. An equality job has a site and no goal.
type Frame =
  { site :: Site
  , goal :: Maybe GoalObject
  }

emptySessionEnv :: SessionEnv
emptySessionEnv = { catalog: catalogOf [], kinding: emptyKindingEnv }

-- | Run an action outside any attempt, reading the session given.
runElabIn :: forall a. SessionEnv -> SolverState -> Elab a -> Tuple (Outcome a) SolverState
runElabIn session s (Elab f) = f { session, frame: Nothing } s

-- | Run an action with an empty session and no frame, as the mechanism's own
-- | operations are run.
runElab :: forall a. SolverState -> Elab a -> Tuple (Outcome a) SolverState
runElab = runElabIn emptySessionEnv

-- | Run an action under the frame given. The frame is read and never written,
-- | so whatever the action reaches, the frame outside is the one it was.
withFrame :: forall a. Frame -> Elab a -> Elab a
withFrame frame (Elab f) = Elab \env s -> f (env { frame = Just frame }) s

-- | What the action is run under.
askEnv :: Elab ElabEnv
askEnv = Elab \env s -> Tuple (Done env) s

runWithin :: forall a. ElabEnv -> SolverState -> Elab a -> Tuple (Outcome a) SolverState
runWithin env s (Elab f) = f env s

-- | The state a session begins in. The session manager supplies an identifier
-- | it issues once for the life of the process running the guest.
initialState :: SessionId -> P.Int -> SolverState
initialState session fuel =
  { tentative:
      { metas: emptyContext
      , obligations: emptyStore
      , scheduler: emptyScheduler
      , written: Set.empty
      , arena: emptyArena
      , names: { nextScope: 1, nextBinder: 0, nextIdent: 0 }
      , open: Map.empty
      }
  , retained: { session, nextGeneration: 0, fuel }
  }

throw :: forall a. Diagnostic -> Elab a
throw diagnostic = Elab \_ s -> Tuple (Failed diagnostic) s

-- | Report a defect, which nothing catches.
-- |
-- | This is not how a program is rejected. It is for what leaves no sound way to
-- | continue: the mechanism driven against its contract, or an invariant of its
-- | own found broken.
break :: forall a. Defect -> Elab a
break defect = Elab \_ s -> Tuple (Broke defect) s

-- | Abandon the attempt until one of the metavariables named is assigned.
-- |
-- | Nothing of the abandoned run is kept: the goal is run again from its
-- | beginning against the state the host has by then, so no continuation is
-- | saved (D40).
postpone :: forall a. Set MetaVar -> Elab a
postpone ms = postponeWith (ExplicitPostponement ms)

postponeWith :: forall a. Cause -> Elab a
postponeWith cause = Elab \_ s -> Tuple (Postponed cause) s

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
transact action = Elab \env s -> case runWithin env s action of
  Tuple (Done a) s' ->
    Tuple (Done (Right a)) s'
  Tuple (Failed diagnostic) s' ->
    Tuple (Done (Left diagnostic)) (rollbackTo s.tentative s')
  Tuple (Postponed cause) s' ->
    Tuple (Postponed cause) (rollbackTo s.tentative s')
  Tuple (Broke defect) s' ->
    Tuple (Broke defect) (rollbackTo s.tentative s')

-- | Place an object in the arena and hand back the handle naming it.
-- |
-- | Its generation is the next the session has never issued. A generation is
-- | never issued twice, so where none is left the session stops rather than
-- | wrap around to one a handle still carries.
issue :: HandleObject -> Elab Handle
issue object = Elab \_ s ->
  if s.retained.nextGeneration >= top then
    Tuple (Broke GenerationsExhausted) s
  else
    let
      Tuple handle arena =
        issueIn s.retained.session s.retained.nextGeneration object s.tentative.arena
    in
      Tuple (Done handle)
        ( s
            { tentative { arena = arena }
            , retained { nextGeneration = s.retained.nextGeneration + 1 }
            }
        )

-- | The object a handle names, where it names one of the class expected. A
-- | handle that names none is a defect of whoever presented it.
resolveObject :: HandleClass -> Handle -> Elab HandleObject
resolveObject expected handle = Elab \_ s ->
  case resolveIn s.retained.session s.retained.nextGeneration expected handle s.tentative.arena of
    Left err -> Tuple (Broke (InvalidHandle handle err)) s
    Right object -> Tuple (Done object) s

resolveGoal :: Handle -> Elab GoalObject
resolveGoal handle = resolveObject GoalClass handle >>= case _ of
  GoalObject goal -> pure goal
  _ -> break (InvalidHandle handle (HandleClassMismatch GoalClass))

resolveType :: Handle -> Elab TypeObject
resolveType handle = resolveObject TypeClass handle >>= case _ of
  TypeObject ty -> pure ty
  _ -> break (InvalidHandle handle (HandleClassMismatch TypeClass))

resolveExpr :: Handle -> Elab ExprObject
resolveExpr handle = resolveObject ExprClass handle >>= case _ of
  ExprObject expr -> pure expr
  _ -> break (InvalidHandle handle (HandleClassMismatch ExprClass))

resolveMeta :: Handle -> Elab MetaVar
resolveMeta handle = resolveObject MetaClass handle >>= case _ of
  MetaObject m -> pure m
  _ -> break (InvalidHandle handle (HandleClassMismatch MetaClass))

resolveScope :: Handle -> Elab ScopeObject
resolveScope handle = resolveObject ScopeClass handle >>= case _ of
  ScopeObject scope -> pure scope
  _ -> break (InvalidHandle handle (HandleClassMismatch ScopeClass))

resolveBinder :: Handle -> Elab BinderObject
resolveBinder handle = resolveObject BinderClass handle >>= case _ of
  BinderObject binder -> pure binder
  _ -> break (InvalidHandle handle (HandleClassMismatch BinderClass))

-- | The identity of a build scope opened in this attempt. The root is 0.
freshScopeId :: Elab ScopeId
freshScopeId = Elab \_ s ->
  Tuple (Done (ScopeId s.tentative.names.nextScope))
    (s { tentative { names { nextScope = s.tentative.names.nextScope + 1 } } })

-- | A type variable a builder binds: the hint, `#`, and a number, the first the
-- | set given does not hold.
-- |
-- | **Freshness is checked against where the name is bound**, the set being the
-- | type variables in scope there. That no source identifier holds `#` keeps a
-- | name apart from what an author wrote and nothing more: a context may hold
-- | one another operation of the host generated, and the numbers are a supply
-- | a rollback restores. A number skipped is spent, so the supply only advances.
freshBinderName :: Set TyVar -> P.String -> Elab TyVar
freshBinderName taken hint = Elab \_ s ->
  let
    Tuple k name = firstFree (\i -> TyVar (hint <> "#" <> show i)) (\v -> Set.member v taken) s.tentative.names.nextBinder
  in
    Tuple (Done name) (s { tentative { names { nextBinder = k + 1 } } })

-- | A value variable a builder binds, by the rule `freshBinderName` follows, from
-- | a supply of its own: the value variables in scope where it is bound are the
-- | set given.
freshIdent :: Set Ident -> P.String -> Elab Ident
freshIdent taken hint = Elab \_ s ->
  let
    Tuple k name = firstFree (\i -> Ident (hint <> "#" <> show i)) (\v -> Set.member v taken) s.tentative.names.nextIdent
  in
    Tuple (Done name) (s { tentative { names { nextIdent = k + 1 } } })

-- The first number from the one given whose name is not taken, and that name.
firstFree :: forall a. (P.Int -> a) -> (a -> P.Boolean) -> P.Int -> Tuple P.Int a
firstFree make taken i =
  let
    name = make i
  in
    if taken name then firstFree make taken (i + 1) else Tuple i name

-- | Hold a binder open, by the scope its body is built in and that scope's
-- | ancestors.
holdOpen :: ScopeId -> Set ScopeId -> Elab Unit
holdOpen body ancestors = Elab \_ s ->
  Tuple (Done unit) (s { tentative { open = Map.insert body ancestors s.tentative.open } })

-- | What closing a binder came to.
data Release
  = Released
  -- | Not held open: closed already, or opened by a candidate a rollback
  -- | discarded.
  | NotOpen
  -- | A binder opened inside its body, named by that body's scope, is open
  -- | still. Closing around it would fix the type that carries the outer binder
  -- | while the inner one can still build under it.
  | EnclosesOpen ScopeId

-- | Close a binder held open, once nothing opened inside its body is.
release :: ScopeId -> Elab Release
release body = Elab \_ s -> case Map.lookup body s.tentative.open of
  Nothing -> Tuple (Done NotOpen) s
  Just _ -> case Array.find (\(Tuple _ ancestors) -> Set.member body ancestors) (Map.toUnfoldable s.tentative.open :: P.Array (Tuple ScopeId (Set ScopeId))) of
    Just (Tuple inner _) -> Tuple (Done (EnclosesOpen inner)) s
    Nothing -> Tuple (Done Released) (s { tentative { open = Map.delete body s.tentative.open } })

-- | Refuse to go on while a binder is still open. What an attempt built under
-- | an open binder would otherwise commit without it.
requireClosed :: Elab Unit
requireClosed = Elab \_ s ->
  if Map.isEmpty s.tentative.open then Tuple (Done unit) s
  else Tuple (Broke (BindersLeftOpen (Map.keys s.tentative.open))) s

-- | One unit of the loop's budget.
-- |
-- | What exhaustion means is the loop's to decide; this spends and reports
-- | nothing.
spendFuel :: Elab Unit
spendFuel = Elab \_ s -> Tuple (Done unit) (s { retained { fuel = s.retained.fuel - 1 } })

fuelRemaining :: Elab P.Int
fuelRemaining = Elab \_ s -> Tuple (Done s.retained.fuel) s

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
settle site progress = Elab \_ s ->
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
freshTypeMeta context kind = Elab \_ s ->
  let
    scope =
      { types: Map.keys context.tyVars
      , kinds: context.kindVars
      }
    Tuple m metas = freshMeta { kind, scope } s.tentative.metas
  in
    Tuple (Done (XMeta m)) (s { tentative { metas = metas } })

-- | A term metavariable at the type given, created under the context given.
-- |
-- | Its scope is what that context binds, read by `termScopeOf` rather than
-- | stated by the caller, so no caller can admit a solution the context does
-- | not have in scope. The caller places it in a term as `ETermMeta`, with the
-- | annotation of the place it stands.
freshTermMeta :: XContext -> XType -> Elab TermMetaVar
freshTermMeta context ty = Elab \_ s ->
  let
    Tuple m metas = TermMeta.freshTermMeta { ty, scope: termScopeOf context } s.tentative.metas
  in
    Tuple (Done m) (s { tentative { metas = metas } })

-- | `⟨ τ by f ⟩` at a site: a term metavariable at `τ` under the site's context,
-- | and the synthesis job that fills it, created together and queued for a first
-- | attempt.
-- |
-- | The job is queued rather than attempted, since it may be created inside an
-- | attempt, and attempting it there would open one inside another. Both belong
-- | to what the current attempt owns, so a rollback removes the two together.
-- | The metavariable is returned for the caller to place as `ETermMeta`.
createSynthesis :: Site -> XType -> SynthRef -> Elab (Tuple PendingId TermMetaVar)
createSynthesis site expectedType synthesizer = Elab \_ s ->
  let
    Tuple goal metas = newGoal site expectedType synthesizer s.tentative.metas
    Tuple id created = create site (JobSynthesis goal) s.tentative.scheduler
  in
    Tuple (Done (Tuple id (goalOf goal).target))
      (s { tentative { metas = metas, scheduler = enqueueInitial id created } })

-- | Check a synthesis job's target against the current `Ψ` and the job's site,
-- | before anything runs the synthesizer.
-- |
-- | `createSynthesis` is the one supported way to make a job and its target; this
-- | is the independent check of what it guarantees. The target must be held
-- | unsolved, stand at the goal's type once both are zonked against the current
-- | `Ψ`, and have a scope within what the site binds — within and not equal,
-- | since a target standing in another solution is narrowed with it. A violation
-- | is a defect of the host and not of the program.
checkSynthesisTarget :: PendingId -> Site -> GoalRecord -> Elab Unit
checkSynthesisTarget id site record = Elab \_ s ->
  let
    goal = goalOf record
    metas = s.tentative.metas
    malformed = case lookupTermMeta metas goal.target of
      Nothing -> Just (TargetAbsent goal.target)
      Just (TermAssigned _) -> Just (TargetSolved goal.target)
      Just (TermUnsolved info)
        | substitute metas info.ty /= substitute metas goal.expectedType ->
            Just (TargetTypeDiffers (substitute metas info.ty) (substitute metas goal.expectedType))
        | not (within info.scope (termScopeOf site.context)) ->
            Just (TargetScopeWider goal.target)
        | otherwise -> Nothing
  in
    case malformed of
      Just reason -> Tuple (Broke (MalformedSynthesisJob id reason)) s
      Nothing -> Tuple (Done unit) s
  where
  within inner outer =
    Set.subset inner.values outer.values
      && Set.subset inner.types outer.types
      && Set.subset inner.kinds outer.kinds

-- | `?m := e`, reported at the site given.
-- |
-- | A solution that escapes the scope of `?m`, or contains it, is a failure: a
-- | search may take another candidate. One naming a metavariable `Ψ` does not
-- | hold, or holds solved, is a defect in whoever assigns.
assignTerm :: forall a. Site -> TermMetaVar -> XExpr a -> Elab Unit
assignTerm site m solution = Elab \_ s ->
  case assignTermMeta s.tentative.metas m solution of
    Left err
      | termMisuse err -> Tuple (Broke (TermMisuse site.origin err)) s
      | otherwise -> Tuple (Failed (TermAssignmentFailed site.origin err)) s
    Right metas ->
      Tuple (Done unit) (s { tentative { metas = metas } })

-- | A term with everything `Ψ` has solved applied to it.
zonkTerm :: forall a. XExpr a -> Elab (XExpr a)
zonkTerm e = Elab \_ s -> Tuple (Done (zonkExpr s.tentative.metas e)) s

-- | Listed one by one for the reason `misuse` is.
termMisuse :: TermError -> P.Boolean
termMisuse = case _ of
  TermMetaUnbound _ -> true
  TermMetaAlreadyAssigned _ -> true
  TermNarrowing err -> misuse err
  TermOccursCheck _ -> false
  TermEscapingValue _ _ -> false
  TermEscapingType _ _ -> false
  TermEscapingKind _ _ -> false
  TermCapturesJoin _ _ -> false

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
take obligation = Elab \_ s ->
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
metaContext = Elab \_ s -> Tuple (Done s.tentative.metas) s

-- | `Ψ` as it stands, for the host's observations to read. Nothing a synthesizer
-- | receives is this; what it receives is a handle and a view.
currentMetas :: Elab MetaContext
currentMetas = metaContext

writtenSoFar :: Elab (Set MetaVar)
writtenSoFar = Elab \_ s -> Tuple (Done s.tentative.written) s

wakeAll :: Set MetaVar -> Scheduler -> Scheduler
wakeAll ms scheduler =
  foldl (\acc m -> wake m acc) scheduler (Set.toUnfoldable ms :: P.Array MetaVar)

-- | What is retained is the state the abandoned run left, and everything else is the
-- | checkpoint's.
rollbackTo :: Tentative -> SolverState -> SolverState
rollbackTo saved s = { tentative: saved, retained: s.retained }

instance Functor Elab where
  map f action = Elab \env s -> case runWithin env s action of
    Tuple (Done a) s' -> Tuple (Done (f a)) s'
    Tuple (Postponed cause) s' -> Tuple (Postponed cause) s'
    Tuple (Failed diagnostic) s' -> Tuple (Failed diagnostic) s'
    Tuple (Broke defect) s' -> Tuple (Broke defect) s'

instance Apply Elab where
  apply = ap

instance Applicative Elab where
  pure a = Elab \_ s -> Tuple (Done a) s

instance Bind Elab where
  bind action f = Elab \env s -> case runWithin env s action of
    Tuple (Done a) s' -> runWithin env s' (f a)
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
