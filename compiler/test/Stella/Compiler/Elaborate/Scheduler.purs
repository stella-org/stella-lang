-- | The blocked table's bookkeeping, exercised on scripted jobs.
-- |
-- | Nothing here runs a job: what is under test is that a job waits under every
-- | metavariable it named, that waking it removes every one of those
-- | registrations rather than the one that woke it, and that a second
-- | postponement replaces the set rather than adding to it. Each is a way for a
-- | job to be run twice or never, and none of them needs a synthesizer to
-- | provoke.
module Test.Stella.Compiler.Elaborate.Scheduler (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Pending (Job(..), PendingId(..), Site)
import Stella.Compiler.Elaborate.Type (MetaVar(..), XType(..))
import Stella.Compiler.Elaborate.Scheduler (Invariant(..), Phase(..), Queued, Scheduler, blockedOn, complete, create, emptyScheduler, enqueueInitial, invariants, isInitial, lookupPending, readyIds, reblock, takeReady, unwakeable, wake)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
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

-- | A site with nothing bound and nothing assumed. What the scheduler does with
-- | a job does not depend on either.
site :: Site
site =
  { context: emptyXContext
  , origin: InDeclaration (Qualified prim (Ident "decl"))
  }

-- | One equality to carry, `A ≡ B` at `Type`. It is never solved here.
goal :: Job
goal = JobUnify { kind: XKType, left: tA, right: tB }

metaA :: MetaVar
metaA = MetaVar 0

metaB :: MetaVar
metaB = MetaVar 1

-- | A scheduler holding one job, with that job's identifier.
oneJob :: Tuple PendingId Scheduler
oneJob = create site goal emptyScheduler

-- | The same, postponed on the metavariables given.
waitingOn :: Set MetaVar -> Scheduler
waitingOn ms = case lookupPending s (fst oneJob) of
  Nothing -> s
  Just p -> reblock p ms s
  where
  s = snd oneJob

awaitingOf :: Scheduler -> PendingId -> Maybe (Set MetaVar)
awaitingOf s id = map _.awaiting (lookupPending s id)

-- | A ready queue entry for a retry.
retrying :: PendingId -> Queued
retrying id = { id, phase: Retry }

pendingCount :: Scheduler -> P.Int
pendingCount s = Map.size s.pending

spec :: Spec Unit
spec = describe "Elaborate.Scheduler" do
  describe "a job is created before it is attempted" do
    it "holds the job while neither queue does" do
      let
        Tuple id s = oneJob
      (readyIds s) `shouldEqual` []
      Map.isEmpty s.blocked `shouldEqual` true
      awaitingOf s id `shouldEqual` Just Set.empty
      invariants s `shouldEqual` []

    it "counts the job it is attempting as waiting on nothing" do
      unwakeable (snd oneJob) `shouldEqual` [ fst oneJob ]

  describe "a postponement registers the job under each metavariable it named" do
    it "registers it under every one of them" do
      let
        s = waitingOn (Set.fromFoldable [ metaA, metaB ])
      blockedOn s metaA `shouldEqual` Set.singleton (fst oneJob)
      blockedOn s metaB `shouldEqual` Set.singleton (fst oneJob)
      awaitingOf s (fst oneJob) `shouldEqual` Just (Set.fromFoldable [ metaA, metaB ])
      invariants s `shouldEqual` []

    it "leaves it off the ready queue" do
      readyIds (waitingOn (Set.fromFoldable [ metaA, metaB ])) `shouldEqual` []

  describe "waking a job removes every registration it had" do
    it "puts it on the ready queue once and leaves nothing blocked" do
      let
        s = wake metaA (waitingOn (Set.fromFoldable [ metaA, metaB ]))
      (readyIds s) `shouldEqual` [ fst oneJob ]
      Map.isEmpty s.blocked `shouldEqual` true
      awaitingOf s (fst oneJob) `shouldEqual` Just Set.empty
      invariants s `shouldEqual` []

    it "does not queue it a second time when the other metavariable is assigned" do
      let
        s = wake metaB (wake metaA (waitingOn (Set.fromFoldable [ metaA, metaB ])))
      (readyIds s) `shouldEqual` [ fst oneJob ]
      invariants s `shouldEqual` []

    it "names nothing once woken, which is what a report at quiescence reads" do
      awaitingOf (wake metaA (waitingOn (Set.singleton metaA))) (fst oneJob)
        `shouldEqual` Just Set.empty

  describe "a second postponement replaces the set rather than adding to it" do
    it "waits on what it named then and on nothing else" do
      let
        woken = wake metaA (waitingOn (Set.fromFoldable [ metaA, metaB ]))
        s = case lookupPending woken (fst oneJob) of
          Nothing -> woken
          Just p -> reblock p (Set.singleton metaB) (woken { ready = [] })
      blockedOn s metaB `shouldEqual` Set.singleton (fst oneJob)
      blockedOn s metaA `shouldEqual` Set.empty
      awaitingOf s (fst oneJob) `shouldEqual` Just (Set.singleton metaB)
      invariants s `shouldEqual` []

  describe "the ready queue is taken from the front" do
    it "attempts a job woken earlier first" do
      let
        Tuple first s1 = create site goal emptyScheduler
        Tuple second s2 = create site goal s1
        blocked = case Tuple (lookupPending s2 first) (lookupPending s2 second) of
          Tuple (Just p) (Just q) ->
            reblock q (Set.singleton metaA) (reblock p (Set.singleton metaA) s2)
          _ -> s2
        s = wake metaA blocked
      (readyIds s) `shouldEqual` [ first, second ]
      map fst (takeReady s) `shouldEqual` Just first
      map (readyIds <<< snd) (takeReady s) `shouldEqual` Just [ second ]
      invariants s `shouldEqual` []

  describe "a job that is done leaves nothing behind" do
    it "is held by no table once completed" do
      let
        s = complete (fst oneJob) (waitingOn (Set.fromFoldable [ metaA, metaB ]))
      pendingCount s `shouldEqual` 0
      Map.isEmpty s.blocked `shouldEqual` true
      (readyIds s) `shouldEqual` []
      invariants s `shouldEqual` []

  describe "the invariants are checked rather than assumed" do
    it "reports a registration the job's own set does not name" do
      let
        s = waitingOn (Set.singleton metaA)
        broken = s { blocked = Map.insert metaB (Set.singleton (fst oneJob)) s.blocked }
      invariants broken `shouldEqual` [ RegistrationDiffers metaB (fst oneJob) ]

    it "reports a metavariable the job awaits and is registered under nowhere" do
      let
        s = waitingOn (Set.fromFoldable [ metaA, metaB ])
        broken = s { blocked = Map.delete metaB s.blocked }
      invariants broken `shouldEqual` [ RegistrationDiffers metaB (fst oneJob) ]

    it "reports a job that is at once ready and blocked" do
      let
        s = waitingOn (Set.singleton metaA)
        broken = s { ready = [ retrying (fst oneJob) ] }
      invariants broken
        `shouldEqual`
          [ ReadyAndBlocked (fst oneJob), AwaitingWhileReady (fst oneJob) ]

    it "reports one identifier twice on the ready queue" do
      let
        woken = wake metaA (waitingOn (Set.singleton metaA))
        broken = woken { ready = [ retrying (fst oneJob), retrying (fst oneJob) ] }
      invariants broken `shouldEqual` [ DuplicateOnReady (fst oneJob) ]

    it "reports a queued identifier no pending answers to" do
      invariants (emptyScheduler { ready = [ retrying (PendingId 7) ] })
        `shouldEqual` [ UnknownPending (PendingId 7) ]

  describe "a job queued for its first attempt" do
    it "is on the ready queue and marked as never attempted" do
      let
        Tuple id s0 = oneJob
        s = enqueueInitial id s0
      (readyIds s) `shouldEqual` [ id ]
      isInitial s id `shouldEqual` true
      invariants s `shouldEqual` []

    it "is no longer marked once taken" do
      let
        Tuple id s0 = oneJob
      map (\(Tuple _ s) -> isInitial s id) (takeReady (enqueueInitial id s0)) `shouldEqual` Just false

    it "is marked by nothing once completed" do
      let
        Tuple id s0 = oneJob
        s = complete id (enqueueInitial id s0)
      isInitial s id `shouldEqual` false
      invariants s `shouldEqual` []

    it "is not what a wake queues" do
      let
        Tuple id _ = oneJob
      isInitial (wake metaA (waitingOn (Set.singleton metaA))) id `shouldEqual` false
