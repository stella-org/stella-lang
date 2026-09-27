-- | Submitting jobs, and running the ready queue to where it stops.
-- |
-- | Two things are what these cases are for. **Fuel bounds retries and nothing
-- | else**: a first attempt spends none, a retry spends one whatever it comes to,
-- | and a job the fuel does not reach stays on the ready queue, named. And **the
-- | loop stops where the specification says it stops**: at the first failure, at
-- | a defect, or at quiescence, where a job awaiting nothing is a defect and every
-- | other job left is reported with what it waits on.
module Test.Stella.Compiler.Elaborate.Loop (spec) where

import Prelude

import Stella.Compiler.Elaborate.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Elab (SolverState, initialState, postpone, unify)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Loop (RunResult(..), run, runWith, submitEquality, submitWith)
import Stella.Compiler.Elaborate.Pending (EqualityGoal, Job(..), PendingId, Site)
import Stella.Compiler.Elaborate.Run as Run
import Stella.Compiler.Elaborate.Scheduler (Invariant(..), create, lookupPending)
import Stella.Compiler.Elaborate.Type (MetaVar(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), MetaContext, MetaInfo, UnifyError(..), emptyContext, freshMeta, lookupMeta, substitute)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyName(..), TyVar(..))
import Data.Array.NonEmpty as NonEmptyArray
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

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

-- | Where the equations that solve things stand.
here :: Origin
here = InDeclaration (Qualified prim (Ident "decl"))

-- | Where the job that waits stands, another declaration entirely, so that a
-- | retry reporting any site but its own is caught.
elsewhere :: Origin
elsewhere = InDeclaration (Qualified prim (Ident "other"))

site :: Site
site = { context: emptyXContext, origin: here }

waitingSite :: Site
waitingSite = { context: emptyXContext, origin: elsewhere }

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

-- | `?α ≡ ()`.
solvable :: MetaVar -> EqualityGoal
solvable m = { kind: XKRow RowType, left: XMeta m, right: XRowEmpty }

-- | `?α ≡ ρ`.
solvedAs :: MetaVar -> XType -> EqualityGoal
solvedAs m row = { kind: XKRow RowType, left: XMeta m, right: row }

-- | `Pair { a : A | ?r } { c : C | ?r } ≡ Pair { b : B | ?s } (?v ⊎ ?w)`.
-- |
-- | It refines `?r` and `?s` through a fresh tail and is then stuck on
-- | `{ c : C, b : B | ?t } ≡ ?v ⊎ ?w`, so it is registered under `?r`, `?s`,
-- | `?v` and `?w`. What `?v` is later solved to decides its retry.
stuck :: EqualityGoal
stuck =
  { kind: XKType
  , left: pairOf (field keyA tA (XMeta metas.r)) (field keyC tC (XMeta metas.r))
  , right: pairOf (field keyB tB (XMeta metas.s)) (XRowUnion (XMeta metas.v) (XMeta metas.w))
  }

sessionWith :: Int -> SolverState
sessionWith fuel = s { tentative = s.tentative { metas = metas.ctx } }
  where
  s = initialState fuel

-- | Submit the stuck equation from its own site, then solve `?v` as given, which
-- | wakes it. Nothing has been retried yet.
wokenAfter :: XType -> Int -> Tuple PendingId SolverState
wokenAfter vSolution fuel = Tuple submitted.id s2
  where
  Tuple submitted s1 = submitEquality waitingSite stuck (sessionWith fuel)
  Tuple _ s2 = submitEquality site (solvedAs metas.v vSolution) s1

solutionOf :: MetaContext -> MetaVar -> Maybe XType
solutionOf ctx m = case lookupMeta ctx m of
  Just (Assigned ty) -> Just (substitute ctx ty)
  _ -> Nothing

-- | A job that waits on `?v` by saying so, as a synthesizer would.
waitsOnV :: Job
waitsOnV = JobUnify (solvable metas.x)

spec :: Spec Unit
spec = describe "Elaborate.Loop" do
  describe "submitting" do
    it "attempts a job at once, and removes one that solved" do
      let
        Tuple submitted s = submitEquality site (solvable metas.r) (sessionWith 0)
      submitted.attempt `shouldEqual` Run.Committed
      lookupPending s.tentative.scheduler submitted.id `shouldEqual` Nothing
      solutionOf s.tentative.metas metas.r `shouldEqual` Just XRowEmpty

    it "registers one that is stuck, spending no fuel" do
      let
        Tuple submitted s = submitEquality site stuck (sessionWith 3)
      submitted.attempt `shouldEqual` Run.Registered (Set.fromFoldable [ metas.r, metas.s, metas.v, metas.w ])
      s.counters.fuel `shouldEqual` 3

    it "reports one that failed, and removes it" do
      let
        Tuple submitted s = submitEquality site { kind: XKType, left: tA, right: tB } (sessionWith 0)
      submitted.attempt `shouldEqual` Run.Rejected (EquationFailed here (TypeNotEqual tA tB))
      lookupPending s.tentative.scheduler submitted.id `shouldEqual` Nothing

  describe "running the ready queue" do
    it "completes where nothing is left, with no fuel at all" do
      let
        Tuple result _ = run (sessionWith 0)
      result `shouldEqual` Completed

    it "reports what a job waits on where the ready queue is empty, with no fuel at all" do
      let
        Tuple submitted s0 = submitWith (\_ -> postpone (Set.singleton metas.v)) waitingSite waitsOnV (sessionWith 0)
        Tuple result _ = run s0
      result `shouldEqual` Blocked
        ( NonEmptyArray.singleton
            { id: submitted.id, origin: elsewhere, job: waitsOnV, awaiting: Set.singleton metas.v }
        )

    it "names the next job where there is no fuel, and leaves it on the ready queue" do
      let
        Tuple id s0 = wokenAfter XRowEmpty 0
        Tuple result s = run s0
      result `shouldEqual` Exhausted
        { id, origin: elsewhere, job: JobUnify stuck, awaiting: Set.empty }
      s.tentative.scheduler.ready `shouldEqual` [ id ]

    it "retries a woken job to completion, spending one unit" do
      let
        Tuple _ s0 = wokenAfter (field keyC tC XRowEmpty) 1
        Tuple result s = run s0
      result `shouldEqual` Completed
      s.counters.fuel `shouldEqual` 0

    it "reports a job postponed again, having spent the unit" do
      let
        Tuple id s0 = wokenAfter (XMeta metas.x) 1
        Tuple result s = run s0
      result `shouldEqual` Blocked
        ( NonEmptyArray.singleton
            { id
            , origin: elsewhere
            , job: JobUnify stuck
            , awaiting: Set.fromFoldable [ metas.r, metas.s, metas.w, metas.x ]
            }
        )
      s.counters.fuel `shouldEqual` 0

    it "stops at the first failure, reported at the failing job's own site" do
      let
        Tuple _ s0 = wokenAfter (field keyC tA XRowEmpty) 5
        Tuple result s = run s0
      result `shouldEqual` Rejected (EquationFailed elsewhere (TypeNotEqual tC tA))
      s.counters.fuel `shouldEqual` 4

    it "names the job the fuel did not reach once it has run out" do
      let
        Tuple first s1 = submitWith (\_ -> postpone (Set.singleton metas.v)) waitingSite waitsOnV (sessionWith 1)
        Tuple second s2 = submitWith (\_ -> postpone (Set.singleton metas.v)) waitingSite waitsOnV s1
        Tuple _ s3 = submitEquality site (solvable metas.v) s2
        Tuple result s = runWith (\_ -> pure unit) s3
      first.attempt `shouldEqual` Run.Registered (Set.singleton metas.v)
      result `shouldEqual` Exhausted
        { id: second.id, origin: elsewhere, job: waitsOnV, awaiting: Set.empty }
      s.tentative.scheduler.ready `shouldEqual` [ second.id ]

    it "halts on a defect in a retry" do
      let
        absent = MetaVar 99
        Tuple _ s0 = wokenAfter XRowEmpty 5
        Tuple result _ = runWith (\p -> unify p.site (solvable absent)) s0
      result `shouldEqual` Halted (UnifierMisuse elsewhere (MetaUnbound absent))

    it "halts at quiescence on a job no assignment can reach" do
      let
        Tuple lost scheduler = create site (JobUnify (solvable metas.r)) (sessionWith 0).tentative.scheduler
        s0 = (sessionWith 0) { tentative { scheduler = scheduler } }
        Tuple result _ = run s0
      result `shouldEqual` Halted (UnreachablePending (NonEmptyArray.singleton lost))

    it "halts at quiescence on a job awaiting a metavariable it is not registered under" do
      -- Registered under `?v` and awaiting `?w` too, with the `?w` registration
      -- missing: solving `?w` would never wake it, so it is not a job waiting on
      -- the program.
      let
        Tuple submitted s0 = submitWith (\_ -> postpone (Set.fromFoldable [ metas.v, metas.w ])) waitingSite waitsOnV (sessionWith 0)
        broken = s0 { tentative { scheduler { blocked = Map.delete metas.w s0.tentative.scheduler.blocked } } }
        Tuple result _ = run broken
      result `shouldEqual` Halted (SchedulerBroken (NonEmptyArray.singleton (RegistrationDiffers metas.w submitted.id)))

    it "reports the jobs left blocked in identifier order" do
      let
        Tuple first s1 = submitWith (\_ -> postpone (Set.singleton metas.w)) waitingSite waitsOnV (sessionWith 0)
        Tuple second s2 = submitWith (\_ -> postpone (Set.singleton metas.v)) site waitsOnV s1
        Tuple result _ = run s2
      result `shouldEqual` Blocked
        ( NonEmptyArray.cons'
            { id: first.id, origin: elsewhere, job: waitsOnV, awaiting: Set.singleton metas.w }
            [ { id: second.id, origin: here, job: waitsOnV, awaiting: Set.singleton metas.v } ]
        )
