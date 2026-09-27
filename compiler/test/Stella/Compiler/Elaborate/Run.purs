-- | One attempt of a pending job, and the admission of what it waits on.
-- |
-- | Two things are what these cases are for. **The write set belongs to one
-- | attempt**: it is emptied before the checkpoint, so neither a previous job's
-- | assignments nor the attempt's own rollback put anything into what a
-- | postponement reads. And **a postponement is registered only under what can
-- | wake it**: the metavariables the rollback left unsolved, which a fresh tail
-- | the attempt created is not.
module Test.Stella.Compiler.Elaborate.Run (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Context (Origin(..), bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic(..), Inadmissible(..), MalformedGoal(..))
import Stella.Compiler.Elaborate.Elab (Cause(..), Elab, Outcome(..), SolverState, assignTerm, createSynthesis, freshTypeMeta, freshTermMeta, initialState, postpone, runElab, spendFuel, throw, transact, unify)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Pending (EqualityGoal, Job(..), PendingId(..), Site, goalOf, newGoal)
import Stella.Compiler.Elaborate.Term (XExpr(..))
import Stella.Compiler.Elaborate.TermMeta (termScopeOf)
import Stella.Compiler.Elaborate.Run (Attempt(..), admit, attemptPending, attemptPendingWith, runAttempt)
import Stella.Compiler.Elaborate.Scheduler (Scheduler, blockedOn, create, emptyScheduler, invariants, isInitial, lookupPending, reblock, takeReady, wake, readyIds)
import Stella.Compiler.Elaborate.Type (MetaVar(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), MetaContext, MetaInfo, TermBinding(..), UnifyError(..), emptyContext, freshMeta, lookupMeta, lookupTermMeta, substitute)
import Stella.Compiler.TypedCore (Ident(..), Literal(..), ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyName(..), TyVar(..))
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

tA :: XType
tA = XCon (Qualified prim (TyName "A")) []

tB :: XType
tB = XCon (Qualified prim (TyName "B")) []

tC :: XType
tC = XCon (Qualified prim (TyName "C")) []

keyA :: RowKey
keyA = SymbolKey (Symbol "a")

keyB :: RowKey
keyB = SymbolKey (Symbol "b")

keyC :: RowKey
keyC = SymbolKey (Symbol "c")

rigidR :: TyVar
rigidR = TyVar "r"

-- | A synthesizer, by the name resolution gave it.
resolver :: Qualified Ident
resolver = Qualified (ModuleName "Typeclass") (Ident "resolve")

here :: Origin
here = InDeclaration (Qualified prim (Ident "decl"))

site :: Site
site = { context: emptyXContext, origin: here }

-- | `( l : τ | ρ )`
field :: RowKey -> XType -> XType -> XType
field key ty rest = XRowExtend (XRowTypeEntry key ty) rest

pairOf :: XType -> XType -> XType
pairOf x y = XApp (XApp (XCon (Qualified prim (TyName "Pair")) []) x) y

rowTypeInfo :: MetaInfo
rowTypeInfo =
  { kind: XKRow RowType
  , scope: { types: Set.singleton rigidR, kinds: Set.empty }
  }

-- | Five metavariables at `Row Type`, and `Ψ` holding all of them unsolved.
metas :: { r :: MetaVar, s :: MetaVar, v :: MetaVar, w :: MetaVar, x :: MetaVar, ctx :: MetaContext }
metas = { r, s, v, w, x, ctx }
  where
  one = freshMeta rowTypeInfo emptyContext
  two = freshMeta rowTypeInfo (snd one)
  three = freshMeta rowTypeInfo (snd two)
  four = freshMeta rowTypeInfo (snd three)
  five = freshMeta rowTypeInfo (snd four)
  r = fst one
  s = fst two
  v = fst three
  w = fst four
  x = fst five
  ctx = snd five

-- | The fresh tail a two-sided refinement of `?r` and `?s` introduces, which is
-- | the next name the supply gives.
freshTail :: MetaVar
freshTail = MetaVar metas.ctx.next

-- | `?α ≡ ()`, which solves and assigns one metavariable.
solvable :: MetaVar -> EqualityGoal
solvable m = { kind: XKRow RowType, left: XMeta m, right: XRowEmpty }

-- | `Pair { a : A | ?r } { c : C | ?r } ≡ Pair { b : B | ?s } (?v ⊎ ?w)`.
-- |
-- | The first argument refines `?r` and `?s` through a fresh `?t`, and the second
-- | is then `{ c : C, b : B | ?t } ≡ ?v ⊎ ?w`, stuck on `?t`, `?v` and `?w`. `?t`
-- | is gone once the attempt is rolled back.
stuck :: EqualityGoal
stuck =
  { kind: XKType
  , left: pairOf (field keyA tA (XMeta metas.r)) (field keyC tC (XMeta metas.r))
  , right: pairOf (field keyB tB (XMeta metas.s)) (XRowUnion (XMeta metas.v) (XMeta metas.w))
  }

mismatched :: EqualityGoal
mismatched = { kind: XKType, left: tA, right: tB }

failure :: Diagnostic
failure = EquationFailed here (TypeNotEqual tA tB)

sessionWith :: Scheduler -> SolverState
sessionWith scheduler = s
  { tentative = s.tentative
      { metas = metas.ctx
      , scheduler = scheduler
      }
  }
  where
  s = initialState 100

session :: SolverState
session = sessionWith emptyScheduler

-- | A session holding one job just created, before its first attempt: `pending`
-- | holds it and neither queue does.
holdingJob :: EqualityGoal -> Tuple PendingId SolverState
holdingJob goal = Tuple id (sessionWith scheduler)
  where
  Tuple id scheduler = create site (JobUnify goal) emptyScheduler

-- | The job registered under one metavariable, as a postponement leaves it.
blockedUnder :: MetaVar -> PendingId -> Scheduler -> Scheduler
blockedUnder m id scheduler = case lookupPending scheduler id of
  Just p -> reblock p (Set.singleton m) scheduler
  Nothing -> scheduler

solutionOf :: MetaContext -> MetaVar -> Maybe XType
solutionOf ctx m = case lookupMeta ctx m of
  Just (Assigned ty) -> Just (substitute ctx ty)
  _ -> Nothing

spec :: Spec Unit
spec = describe "Elaborate.Run" do
  describe "an attempt" do
    it "commits a success and leaves the write set empty" do
      let
        Tuple outcome s = runAttempt (unify site (solvable metas.r)) session
      outcome `shouldEqual` Done unit
      solutionOf s.tentative.metas metas.r `shouldEqual` Just XRowEmpty
      s.tentative.written `shouldEqual` Set.empty

    it "empties the write set before the checkpoint, so a rollback restores it empty" do
      -- A write set left standing from an earlier job is what the rollback would
      -- otherwise put back, just as a postponement is about to be admitted.
      let
        stale = session { tentative { written = Set.singleton metas.x } }
        Tuple outcome s = runAttempt (unify site (solvable metas.r) *> (postpone (Set.singleton metas.s) :: Elab Unit)) stale
      outcome `shouldEqual` Postponed (ExplicitPostponement (Set.singleton metas.s))
      s.tentative.written `shouldEqual` Set.empty
      solutionOf s.tentative.metas metas.r `shouldEqual` Nothing

    it "reports only this attempt's assignments beside what an equation is stuck on" do
      let
        stale = session { tentative { written = Set.singleton metas.x } }
        Tuple outcome _ = runAttempt (unify site stuck) stale
      outcome `shouldEqual` Postponed
        ( SolverStuck
            { blockedOn: Set.fromFoldable [ freshTail, metas.v, metas.w ]
            , written: Set.fromFoldable [ metas.r, metas.s ]
            }
        )

    it "rolls a failure back and keeps the fuel it spent" do
      let
        Tuple outcome s = runAttempt (spendFuel *> unify site (solvable metas.r) *> (throw failure :: Elab Unit)) session
      outcome `shouldEqual` Failed failure
      solutionOf s.tentative.metas metas.r `shouldEqual` Nothing
      s.counters.fuel `shouldEqual` 99

    it "hands a defect back as the outcome it is, rolled back" do
      let
        absent = MetaVar 99
        Tuple outcome s = runAttempt (unify site (solvable metas.r) *> unify site (solvable absent)) session
      outcome `shouldEqual` Broke (UnifierMisuse here (MetaUnbound absent))
      solutionOf s.tentative.metas metas.r `shouldEqual` Nothing

  describe "admitting a postponement raised above the mechanism" do
    it "admits metavariables that are unsolved" do
      admit metas.ctx (ExplicitPostponement (Set.fromFoldable [ metas.r, metas.s ]))
        `shouldEqual` Right (Set.fromFoldable [ metas.r, metas.s ])

    it "refuses an empty set" do
      admit metas.ctx (ExplicitPostponement Set.empty) `shouldEqual` Left AwaitsNothing

    it "refuses a metavariable Ψ does not hold" do
      let
        absent = MetaVar 99
      admit metas.ctx (ExplicitPostponement (Set.fromFoldable [ metas.r, absent ]))
        `shouldEqual` Left (AwaitsAbsent absent)

    it "refuses a metavariable already solved" do
      let
        Tuple _ s = runAttempt (unify site (solvable metas.r)) session
      admit s.tentative.metas (ExplicitPostponement (Set.singleton metas.r))
        `shouldEqual` Left (AwaitsSolved metas.r)

    it "refuses a metavariable the attempt created, which the rollback deleted" do
      let
        naming :: Elab Unit
        naming = do
          t <- freshTypeMeta emptyXContext (XKRow RowType)
          case t of
            XMeta m -> postpone (Set.singleton m)
            _ -> throw failure

        Tuple outcome s = runAttempt naming session
      case outcome of
        Postponed cause -> admit s.tentative.metas cause `shouldEqual` Left (AwaitsAbsent freshTail)
        _ -> outcome `shouldEqual` Postponed (ExplicitPostponement (Set.singleton freshTail))

  describe "admitting a postponement the mechanism raised" do
    it "keeps what the rollback left unsolved and drops the fresh tail" do
      let
        Tuple outcome s = runAttempt (unify site stuck) session
      case outcome of
        Postponed cause ->
          admit s.tentative.metas cause
            `shouldEqual` Right (Set.fromFoldable [ metas.r, metas.s, metas.v, metas.w ])
        _ -> outcome `shouldEqual` Postponed (SolverStuck { blockedOn: Set.empty, written: Set.empty })

    it "refuses one of which nothing survives" do
      admit metas.ctx (SolverStuck { blockedOn: Set.singleton (MetaVar 99), written: Set.empty })
        `shouldEqual` Left NothingDurable

  describe "attempting a pending job" do
    it "commits a solved job and removes it from every table" do
      let
        Tuple id s0 = holdingJob (solvable metas.r)
        Tuple result s = attemptPending id s0
      result `shouldEqual` Committed
      lookupPending s.tentative.scheduler id `shouldEqual` Nothing
      solutionOf s.tentative.metas metas.r `shouldEqual` Just XRowEmpty

    it "reports a failed job, installs nothing, and removes it" do
      let
        Tuple id s0 = holdingJob mismatched
        Tuple result s = attemptPending id s0
      result `shouldEqual` Rejected failure
      lookupPending s.tentative.scheduler id `shouldEqual` Nothing

    it "registers a stuck job under what can wake it" do
      let
        Tuple id s0 = holdingJob stuck
        Tuple result s = attemptPending id s0
        durable = Set.fromFoldable [ metas.r, metas.s, metas.v, metas.w ]
      result `shouldEqual` Registered durable
      map _.awaiting (lookupPending s.tentative.scheduler id) `shouldEqual` Just durable
      blockedOn s.tentative.scheduler metas.v `shouldEqual` Set.singleton id
      blockedOn s.tentative.scheduler freshTail `shouldEqual` Set.empty
      solutionOf s.tentative.metas metas.r `shouldEqual` Nothing
      invariants s.tentative.scheduler `shouldEqual` []

    it "is woken by an assignment to a metavariable that existed before it" do
      let
        Tuple id s0 = holdingJob stuck
        Tuple _ s1 = attemptPending id s0
        Tuple _ s2 = runAttempt (unify site (solvable metas.v)) s1
      (readyIds s2.tentative.scheduler) `shouldEqual` [ id ]
      invariants s2.tentative.scheduler `shouldEqual` []

    it "leaves an earlier committed job's assignments out of a later registration" do
      let
        Tuple first sched1 = create site (JobUnify (solvable metas.x)) emptyScheduler
        Tuple second sched2 = create site (JobUnify stuck) sched1
        Tuple r1 s1 = attemptPending first (sessionWith sched2)
        Tuple r2 _ = attemptPending second s1
      r1 `shouldEqual` Committed
      r2 `shouldEqual` Registered (Set.fromFoldable [ metas.r, metas.s, metas.v, metas.w ])

    it "keeps the fuel a postponed attempt spent" do
      let
        Tuple id s0 = holdingJob stuck
        spent = s0 { counters { fuel = 7 } }
        Tuple _ s = attemptPending id spent
      s.counters.fuel `shouldEqual` 7

    it "halts on a defect and leaves the job where it was" do
      let
        absent = MetaVar 99
        Tuple id s0 = holdingJob (solvable absent)
        Tuple result s = attemptPending id s0
      result `shouldEqual` Halted (UnifierMisuse here (MetaUnbound absent))
      map _.awaiting (lookupPending s.tentative.scheduler id) `shouldEqual` Just Set.empty

    it "halts on an identifier pending does not hold" do
      let
        Tuple result _ = attemptPending (PendingId 7) session
      result `shouldEqual` Halted (PendingAbsent (PendingId 7))

    it "attempts a job woken and then taken from the ready queue" do
      let
        Tuple id s0 = holdingJob (solvable metas.r)
        queued = wake metas.r (blockedUnder metas.r id s0.tentative.scheduler)
      case takeReady queued of
        Nothing ->
          (readyIds queued) `shouldEqual` [ id ]
        Just (Tuple taken rest) -> do
          taken `shouldEqual` id
          let
            Tuple result s = attemptPending id (s0 { tentative { scheduler = rest } })
          result `shouldEqual` Committed
          lookupPending s.tentative.scheduler id `shouldEqual` Nothing
          invariants s.tentative.scheduler `shouldEqual` []

    it "halts on a job still on the ready queue" do
      let
        Tuple id s0 = holdingJob (solvable metas.r)
        queued = wake metas.r (blockedUnder metas.r id s0.tentative.scheduler)
        Tuple result _ = attemptPending id (s0 { tentative { scheduler = queued } })
      result `shouldEqual` Halted (PendingStillScheduled id)

    it "halts on a job still registered under a metavariable" do
      let
        Tuple id s0 = holdingJob (solvable metas.r)
        blocked = blockedUnder metas.r id s0.tentative.scheduler
        Tuple result _ = attemptPending id (s0 { tentative { scheduler = blocked } })
      result `shouldEqual` Halted (PendingStillScheduled id)

  describe "a runner given" do
    it "registers what an admissible postponement names" do
      let
        Tuple id s0 = holdingJob (solvable metas.r)
        Tuple result s = attemptPendingWith (\_ -> postpone (Set.singleton metas.v)) id s0
      result `shouldEqual` Registered (Set.singleton metas.v)
      blockedOn s.tentative.scheduler metas.v `shouldEqual` Set.singleton id

    it "halts on a postponement naming nothing, naming the job" do
      let
        Tuple id s0 = holdingJob (solvable metas.r)
        Tuple result s = attemptPendingWith (\_ -> postpone Set.empty) id s0
      result `shouldEqual` Halted
        ( PostponementInadmissible
            { origin: here
            , job: JobUnify (solvable metas.r)
            , reason: AwaitsNothing
            }
        )
      map _.awaiting (lookupPending s.tentative.scheduler id) `shouldEqual` Just Set.empty

    it "halts on a postponement naming a metavariable the attempt created" do
      let
        Tuple id s0 = holdingJob (solvable metas.r)
        naming = do
          t <- freshTypeMeta emptyXContext (XKRow RowType)
          case t of
            XMeta m -> postpone (Set.singleton m)
            _ -> throw failure
        Tuple result _ = attemptPendingWith (\_ -> naming) id s0
      result `shouldEqual` Halted
        ( PostponementInadmissible
            { origin: here
            , job: JobUnify (solvable metas.r)
            , reason: AwaitsAbsent freshTail
            }
        )

    it "halts on a postponement naming a metavariable solved before the attempt" do
      let
        Tuple id s0 = holdingJob (solvable metas.x)
        Tuple _ solved = runAttempt (unify site (solvable metas.r)) s0
        Tuple result _ = attemptPendingWith (\_ -> postpone (Set.singleton metas.r)) id solved
      result `shouldEqual` Halted
        ( PostponementInadmissible
            { origin: here
            , job: JobUnify (solvable metas.x)
            , reason: AwaitsSolved metas.r
            }
        )

    it "admits a metavariable the attempt assigned, the rollback having undone it" do
      let
        Tuple id s0 = holdingJob (solvable metas.x)
        assigning = unify site (solvable metas.r) *> postpone (Set.singleton metas.r)
        Tuple result s = attemptPendingWith (\_ -> assigning) id s0
      result `shouldEqual` Registered (Set.singleton metas.r)
      solutionOf s.tentative.metas metas.r `shouldEqual` Nothing

  describe "a synthesis job" do
    it "is created together with its target, at the goal's type and under the site's context" do
      let
        bound = { context: bindVar emptyXContext (Ident "d") tA, origin: here }
        Tuple outcome s = runElab session (createSynthesis bound tB resolver)
      case outcome of
        Done (Tuple id target) -> do
          lookupTermMeta s.tentative.metas target `shouldEqual`
            Just (TermUnsolved { ty: tB, scope: termScopeOf bound.context })
          map _.site (lookupPending s.tentative.scheduler id) `shouldEqual` Just bound
          map (jobTarget <<< _.job) (lookupPending s.tentative.scheduler id) `shouldEqual` Just (Just target)
          (readyIds s.tentative.scheduler) `shouldEqual` [ id ]
          isInitial s.tentative.scheduler id `shouldEqual` true
        _ -> fail ("the job was not created: " <> show outcome)

    it "is rolled back together with its target" do
      let
        attempt :: Elab Unit
        attempt = createSynthesis site tB resolver *> throw failure
        Tuple _ s = runElab session (transact attempt)
      s.tentative.metas.nextTerm `shouldEqual` 0
      Map.size s.tentative.metas.termBindings `shouldEqual` 0
      Map.size s.tentative.scheduler.pending `shouldEqual` 0
      (readyIds s.tentative.scheduler) `shouldEqual` []

    it "halts under the host runner, which holds no synthesizer, and stays pending" do
      let
        Tuple outcome s0 = runElab session (createSynthesis site tB resolver)
      case outcome, takeReady s0.tentative.scheduler of
        Done (Tuple id _), Just (Tuple _ taken) -> do
          let
            Tuple result s = attemptPending id (s0 { tentative { scheduler = taken } })
          result `shouldEqual` Halted (SynthesizerUnavailable resolver)
          map _.id (lookupPending s.tentative.scheduler id) `shouldEqual` Just id
        _, _ -> fail ("the job was not created: " <> show outcome)
  describe "the check of a synthesis job's target" do
    it "passes a target whose scope a narrowing made smaller than its site's" do
      let
        bound = { context: bindVar emptyXContext (Ident "d") tA, origin: here }
        narrowing = do
          Tuple id target <- createSynthesis bound tB resolver
          outer <- freshTermMeta emptyXContext tB
          assignTerm site outer (ETermMeta 0 target)
          pure id
        Tuple outcome s0 = runElab session narrowing
      case outcome of
        Done id -> fst (attemptTaken id s0) `shouldEqual` Halted (SynthesizerUnavailable resolver)
        _ -> fail ("the job was not created: " <> show outcome)

    it "halts on a target Ψ does not hold, running nothing and changing nothing" do
      let
        Tuple record _ = newGoal site tB resolver metas.ctx
        Tuple id scheduler = create site (JobSynthesis record) emptyScheduler
        Tuple result s = attemptPending id (sessionWith scheduler)
      result `shouldEqual` Halted (MalformedSynthesisJob id (TargetAbsent (goalOf record).target))
      s.tentative.metas `shouldEqual` metas.ctx

    it "halts on a target solved already" do
      let
        solving = do
          Tuple id target <- createSynthesis site tB resolver
          assignTerm site target (ELit 0 (LitInt 0))
          pure (Tuple id target)
        Tuple outcome s0 = runElab session solving
      case outcome of
        Done (Tuple id target) ->
          fst (attemptTaken id s0) `shouldEqual` Halted (MalformedSynthesisJob id (TargetSolved target))
        _ -> fail ("the job was not created: " <> show outcome)

    it "halts on a target at another type, and on one scoped wider than its site" do
      let
        Tuple record ctx = newGoal site tB resolver metas.ctx
        target = (goalOf record).target
        Tuple id scheduler = create site (JobSynthesis record) emptyScheduler
        retyped = rebound target (\info -> info { ty = tA }) ctx
        widened = rebound target (\info -> info { scope { values = Set.singleton (Ident "zz") } }) ctx
        attemptWith c = fst (attemptPending id ((sessionWith scheduler) { tentative { metas = c } }))
      attemptWith retyped `shouldEqual` Halted (MalformedSynthesisJob id (TargetTypeDiffers tA tB))
      attemptWith widened `shouldEqual` Halted (MalformedSynthesisJob id (TargetScopeWider target))

    it "compares the two types as the current Ψ zonks them" do
      -- The goal is written at `?α` and the target stands at `B`, as a narrowing
      -- that substituted its type leaves it. They agree once `?α` is `B`, and
      -- not while it is `A`.
      let
        Tuple alpha ctx0 = freshMeta { kind: XKType, scope: { types: Set.empty, kinds: Set.empty } } metas.ctx
        Tuple record ctx1 = newGoal site (XMeta alpha) resolver ctx0
        target = (goalOf record).target
        Tuple id scheduler = create site (JobSynthesis record) emptyScheduler
        standingAtB = rebound target (\info -> info { ty = tB }) ctx1
        solvedAs ty = standingAtB { bindings = Map.insert alpha (Assigned ty) standingAtB.bindings }
        attemptWith c = fst (attemptPending id ((sessionWith scheduler) { tentative { metas = c } }))
      attemptWith (solvedAs tB) `shouldEqual` Halted (SynthesizerUnavailable resolver)
      attemptWith (solvedAs tA) `shouldEqual` Halted (MalformedSynthesisJob id (TargetTypeDiffers tB tA))

  where
  jobTarget = case _ of
    JobSynthesis goal -> Just (goalOf goal).target
    JobUnify _ -> Nothing

  -- Attempt a job queued for its first attempt, taking it from the queue first.
  attemptTaken id s0 = case takeReady s0.tentative.scheduler of
    Just (Tuple _ taken) -> attemptPending id (s0 { tentative { scheduler = taken } })
    Nothing -> attemptPending id s0

  -- Rewrite what `Ψ` records of an unsolved term metavariable.
  rebound target f ctx = ctx
    { termBindings = Map.update
        ( case _ of
            TermUnsolved info -> Just (TermUnsolved (f info))
            other -> Just other
        )
        target
        ctx.termBindings
    }
