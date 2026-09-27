-- | The one entry an assignment reaches `Ψ` through, and the transaction an
-- | attempt runs in.
-- |
-- | Two things are what these cases are for. **An assignment owes the same four
-- | things whether the equation solved or became stuck**, so an equation that has
-- | already broken a row constraint is a failure and never a registration; the
-- | pair of stuck cases differing only in what the store holds is what holds that
-- | in place. And **a rollback restores what an attempt owns and nothing else**:
-- | the assignments, the obligations, the wakes and the write set go back, while
-- | the fuel the abandoned run spent stays spent.
-- |
-- | Introducing a row constraint is decided where it happens: an assumption or a
-- | requirement that does not hold is rejected naming the one site it came from,
-- | and leaves neither a context nor an obligation behind.
module Test.Stella.Compiler.Elaborate.Elab (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Context (Origin(..), XContext, bindKindVars, bindTyVar, emptyXContext)
import Stella.Compiler.Elaborate.Context as Context
import Stella.Compiler.Elaborate.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Elab (Cause(..), Elab, Outcome(..), SolverState, assume, freshTypeMeta, initialState, postpone, require, runElab, spendFuel, throw, transact, unify)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Obligation (Basis(..), Breach(..), Obligation, ObligationStore, emptyStore, introduce)
import Stella.Compiler.Elaborate.Pending (EqualityGoal, Job(..), PendingId, Site)
import Stella.Compiler.Elaborate.Scheduler (Scheduler, blockedOn, create, emptyScheduler, lookupPending, reblock, readyIds)
import Stella.Compiler.Elaborate.Type (MetaVar(..), XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), MetaContext, MetaInfo, UnifyError(..), emptyContext, freshMeta, lookupMeta, substitute)
import Stella.Compiler.Elaborate.Row (XRowError(..), xnf)
import Stella.Compiler.TypedCore (Ident(..), KindVar(..), ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyName(..), TyVar(..))
import Data.Either (Either(..))
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

keyA :: RowKey
keyA = SymbolKey (Symbol "a")

keyB :: RowKey
keyB = SymbolKey (Symbol "b")

keyCache :: RowKey
keyCache = SymbolKey (Symbol "cache")

keyK :: RowKey
keyK = SymbolKey (Symbol "k")

rigidR :: TyVar
rigidR = TyVar "r"

-- | Where an equation stands.
here :: Origin
here = InDeclaration (Qualified prim (Ident "decl"))

-- | Where an obligation came from, which is another declaration entirely. The two
-- | are distinct so that a diagnostic copying one origin into both fields, or
-- | reporting them the other way round, is caught.
elsewhere :: Origin
elsewhere = InDeclaration (Qualified prim (Ident "other"))

-- | The site an equation stands at. What it supplies is the kind variables a kind
-- | metavariable created while solving may mention, and the place a failure is
-- | reported; the facts a substitution is judged by travel with the obligations.
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

-- | `?α ≡ ()`, which solves and assigns one metavariable.
solvable :: MetaVar -> EqualityGoal
solvable m = { kind: XKRow RowType, left: XMeta m, right: XRowEmpty }

-- | An equation that refines two tails and then meets a union it cannot decide.
-- |
-- | `?r` and `?s` are assigned by the first argument, leaving the second at
-- | `{ cache : A, b : B | ?t } ≡ ?v ⊎ ?w`, where two flexible tails on one side
-- | admit more than one solution. The assignments stand in what it reports.
stuck :: EqualityGoal
stuck =
  { kind: XKType
  , left: pairOf (field keyA tA (XMeta metas.r)) (XRowUnion (XMeta metas.v) (XMeta metas.w))
  , right: pairOf (field keyB tB (XMeta metas.s)) (field keyCache tA XRowEmpty)
  }

-- | An equation no substitution satisfies.
mismatched :: EqualityGoal
mismatched = { kind: XKType, left: tA, right: tB }

failure :: Diagnostic
failure = EquationFailed here (TypeNotEqual tA tB)

-- | A candidate that assigns and then refuses, which is what a search discards.
failingAfter :: EqualityGoal -> Elab Unit
failingAfter goal = unify site goal *> throw failure

-- | A postponement raised above the mechanism, as a synthesizer's is.
waitingOn :: MetaVar -> Elab Unit
waitingOn m = postpone (Set.singleton m)

-- | A constraint another site assumes, which an assignment may not make
-- | unsatisfiable.
assumed :: XConstraint -> Obligation
assumed constraint =
  { constraint, basis: Assumed, context: emptyXContext, origin: elsewhere }

holding :: Obligation -> ObligationStore
holding ob = case introduce (substitute metas.ctx) ob emptyStore of
  Right (Tuple _ store) -> store
  Left _ -> emptyStore

-- | One job, blocked on the metavariable given.
blocked :: MetaVar -> Tuple PendingId Scheduler
blocked m = case lookupPending s0 id of
  Just p -> Tuple id (reblock p (Set.singleton m) s0)
  Nothing -> Tuple id s0
  where
  Tuple id s0 = create site (JobUnify (solvable m)) emptyScheduler

-- | A session holding the metavariables above, and whatever else a case needs.
sessionWith :: ObligationStore -> Scheduler -> SolverState
sessionWith store scheduler = s
  { tentative = s.tentative
      { metas = metas.ctx
      , obligations = store
      , scheduler = scheduler
      }
  }
  where
  s = initialState 100

session :: SolverState
session = sessionWith emptyStore emptyScheduler

solutionOf :: MetaContext -> MetaVar -> Maybe XType
solutionOf ctx m = case lookupMeta ctx m of
  Just (Assigned ty) -> Just (substitute ctx ty)
  _ -> Nothing

obligationCount :: ObligationStore -> P.Int
obligationCount store = Map.size store.entries

-- | The known keys of a solved row, which is what a refinement is asserted by:
-- | the fresh tail it leaves carries no number anything should depend on.
knownKeysOf :: MetaContext -> MetaVar -> Maybe (P.Array RowKey)
knownKeysOf ctx m = case solutionOf ctx m of
  Nothing -> Nothing
  Just ty -> case xnf ty of
    Left _ -> Nothing
    Right n -> Just (Set.toUnfoldable (Set.fromFoldable (Map.keys n.known)))

-- | A site elsewhere, whose context binds the rigid row variable `r` and the kind
-- | variable `k`.
elsewhereSite :: Site
elsewhereSite = { context: binding, origin: elsewhere }

binding :: XContext
binding = bindKindVars (bindTyVar emptyXContext rigidR (XKRow RowType)) [ KindVar "k" ]

-- | The same site, assuming `k ∉ r`.
assumingKNotInR :: Site
assumingKNotInR = elsewhereSite { context = Context.assume binding (XLacks keyK (XVar rigidR)) }

doneOf :: forall a. Outcome a -> Maybe a
doneOf = case _ of
  Done a -> Just a
  _ -> Nothing

spec :: Spec Unit
spec = describe "Elaborate.Elab" do
  describe "a fresh type metavariable" do
    it "is created at the kind given, under what the context binds" do
      let
        Tuple outcome s = runElab session (freshTypeMeta binding (XKRow RowEffect))
        fresh = MetaVar metas.ctx.next
      outcome `shouldEqual` Done (XMeta fresh)
      lookupMeta s.tentative.metas fresh `shouldEqual` Just
        ( Unsolved
            { kind: XKRow RowEffect
            , scope: { types: Set.singleton rigidR, kinds: Set.singleton (KindVar "k") }
            }
        )

    it "takes its name from a supply a rollback restores" do
      let
        Tuple first s = runElab session (transact (freshTypeMeta binding XKType *> (throw failure :: Elab Unit)))
        Tuple second _ = runElab s (freshTypeMeta binding XKType)
        Tuple unrolled _ = runElab session (freshTypeMeta binding XKType)
      first `shouldEqual` Done (Left failure)
      s.tentative.metas.next `shouldEqual` metas.ctx.next
      second `shouldEqual` unrolled

  describe "an assumption" do
    it "returns the context carrying it and holds it against assignment" do
      let
        constraint = XLacks keyA (XMeta metas.r)
        Tuple outcome s = runElab session do
          context <- assume elsewhereSite constraint
          unify site { kind: XKRow RowType, left: XMeta metas.r, right: field keyA tA XRowEmpty }
          pure context
      outcome `shouldEqual` Failed
        ( ObligationBroken
            { equation: here
            , obligation: elsewhere
            , basis: Assumed
            , breach: SolutionCarriesKey keyA
            }
        )
      solutionOf s.tentative.metas metas.r `shouldEqual` Nothing

    it "is recorded in the context it returns" do
      let
        constraint = XLacks keyA (XMeta metas.r)
        Tuple outcome _ = runElab session (assume elsewhereSite constraint)
      map _.assumed (doneOf outcome) `shouldEqual` Just [ constraint ]

    it "is rejected where it is already unsatisfiable, changing nothing" do
      let
        store = holding (assumed (XLacks keyK (XMeta metas.s)))
        Tuple outcome s = runElab (sessionWith store emptyScheduler)
          (assume elsewhereSite (XLacks keyA (field keyA tA (XMeta metas.r))))
      map _.assumed (doneOf outcome) `shouldEqual` Nothing
      outcome `shouldEqual` Failed
        ( ObligationRejected
            { obligation: elsewhere
            , basis: Assumed
            , breach: SolutionCarriesKey keyA
            }
        )
      s.tentative.obligations `shouldEqual` store

    it "is rejected inside a transaction without leaving an obligation behind" do
      let
        Tuple outcome s = runElab session
          (transact (assume elsewhereSite (XLacks keyA (field keyA tA (XMeta metas.r)))))
      map (map _.assumed) (doneOf outcome) `shouldEqual` Just
        ( Left
            ( ObligationRejected
                { obligation: elsewhere
                , basis: Assumed
                , breach: SolutionCarriesKey keyA
                }
            )
        )
      obligationCount s.tentative.obligations `shouldEqual` 0

  describe "a requirement" do
    it "is rejected where its site does not prove it of a rigid tail" do
      let
        Tuple outcome s = runElab session (require elsewhereSite (XLacks keyK (XVar rigidR)))
      outcome `shouldEqual` Failed
        ( ObligationRejected
            { obligation: elsewhere
            , basis: Required
            , breach: LacksUnprovenAtSite keyK rigidR
            }
        )
      obligationCount s.tentative.obligations `shouldEqual` 0

    it "is settled where its site proves it, and not held" do
      let
        Tuple outcome s = runElab session (require assumingKNotInR (XLacks keyK (XVar rigidR)))
      outcome `shouldEqual` Done unit
      obligationCount s.tentative.obligations `shouldEqual` 0

    it "is held where a flexible tail leaves it open" do
      let
        Tuple outcome s = runElab session (require elsewhereSite (XLacks keyK (XMeta metas.r)))
      outcome `shouldEqual` Done unit
      obligationCount s.tentative.obligations `shouldEqual` 1

    it "reports a subject with no row normal form as a defect" do
      let
        Tuple outcome s = runElab session (require elsewhereSite (XLacks keyK tA))
      outcome `shouldEqual` Broke (ObligationSubjectNotARow elsewhere (XNotARow tA))
      obligationCount s.tentative.obligations `shouldEqual` 0

  describe "what an assignment owes, in one entry" do
    it "installs what a solved equation assigned" do
      let
        Tuple outcome s = runElab session (unify site (solvable metas.r))
      outcome `shouldEqual` Done unit
      solutionOf s.tentative.metas metas.r `shouldEqual` Just XRowEmpty
      s.tentative.written `shouldEqual` Set.singleton metas.r

    it "installs a context holding no assignment nobody has acted on" do
      -- A unification refuses a context whose journal is not empty, so a second
      -- equation over the first's result is what shows the journal drained where
      -- the wakes and the re-decidings were performed.
      let
        Tuple outcome s = runElab session do
          unify site (solvable metas.r)
          unify site (solvable metas.s)
      outcome `shouldEqual` Done unit
      s.tentative.metas.assigned `shouldEqual` Set.empty
      s.tentative.written `shouldEqual` Set.fromFoldable [ metas.r, metas.s ]

    it "wakes the jobs blocked on what it assigned" do
      let
        Tuple id scheduler = blocked metas.r
        Tuple outcome s = runElab (sessionWith emptyStore scheduler) (unify site (solvable metas.r))
      outcome `shouldEqual` Done unit
      (readyIds s.tentative.scheduler) `shouldEqual` [ id ]
      blockedOn s.tentative.scheduler metas.r `shouldEqual` Set.empty
      map _.awaiting (lookupPending s.tentative.scheduler id) `shouldEqual` Just Set.empty

    it "stops holding an obligation the assignment discharged" do
      let
        store = holding (assumed (XLacks keyK (XMeta metas.r)))
        Tuple outcome s = runElab (sessionWith store emptyScheduler) (unify site (solvable metas.r))
      obligationCount store `shouldEqual` 1
      outcome `shouldEqual` Done unit
      obligationCount s.tentative.obligations `shouldEqual` 0

    it "reports a mismatch at the site the equation stands at" do
      let
        Tuple outcome s = runElab session (unify site mismatched)
      outcome `shouldEqual` Failed (EquationFailed here (TypeNotEqual tA tB))
      s.tentative.written `shouldEqual` Set.empty

  describe "an assignment that breaks an obligation" do
    it "fails, naming both sites and what broke" do
      let
        store = holding (assumed (XLacks keyA (XMeta metas.r)))
        Tuple outcome _ = runElab (sessionWith store emptyScheduler)
          (unify site { kind: XKRow RowType, left: XMeta metas.r, right: field keyA tA XRowEmpty })
      outcome `shouldEqual` Failed
        ( ObligationBroken
            { equation: here
            , obligation: elsewhere
            , basis: Assumed
            , breach: SolutionCarriesKey keyA
            }
        )

    it "installs nothing and wakes nothing" do
      let
        store = holding (assumed (XLacks keyA (XMeta metas.r)))
        Tuple id scheduler = blocked metas.r
        Tuple _ s = runElab (sessionWith store scheduler)
          (unify site { kind: XKRow RowType, left: XMeta metas.r, right: field keyA tA XRowEmpty })
      solutionOf s.tentative.metas metas.r `shouldEqual` Nothing
      s.tentative.written `shouldEqual` Set.empty
      (readyIds s.tentative.scheduler) `shouldEqual` []
      blockedOn s.tentative.scheduler metas.r `shouldEqual` Set.singleton id
      obligationCount s.tentative.obligations `shouldEqual` 1

  describe "an equation that assigns and then cannot decide" do
    it "postpones, reporting what it assigned beside what it waits on" do
      let
        Tuple outcome s = runElab session (unify site stuck)
      outcome `shouldEqual` Postponed
        ( SolverStuck
            { blockedOn: Set.fromFoldable [ metas.v, metas.w ]
            , written: Set.fromFoldable [ metas.r, metas.s ]
            }
        )
      knownKeysOf s.tentative.metas metas.r `shouldEqual` Just [ keyB ]

    it "fails instead where one of those assignments broke an obligation" do
      -- The same equation, and the only difference is what the store holds. An
      -- outcome registered as insufficient information would leave a constraint
      -- that is already broken for nothing to find.
      let
        store = holding (assumed (XLacks keyB (XMeta metas.r)))
        Tuple outcome s = runElab (sessionWith store emptyScheduler) (unify site stuck)
      outcome `shouldEqual` Failed
        ( ObligationBroken
            { equation: here
            , obligation: elsewhere
            , basis: Assumed
            , breach: SolutionCarriesKey keyB
            }
        )
      solutionOf s.tentative.metas metas.r `shouldEqual` Nothing

  describe "the transaction" do
    it "catches a diagnostic and restores what the attempt owned" do
      let
        Tuple outcome s = runElab session (transact (failingAfter (solvable metas.r)))
      outcome `shouldEqual` Done (Left failure)
      solutionOf s.tentative.metas metas.r `shouldEqual` Nothing
      s.tentative.written `shouldEqual` Set.empty

    it "propagates a postponement rather than catching it" do
      let
        Tuple outcome _ = runElab session (transact (waitingOn metas.r))
      outcome `shouldEqual` Postponed (ExplicitPostponement (Set.singleton metas.r))

    it "rolls back the assignments, the wakes and the fresh names of one that propagated" do
      let
        Tuple id scheduler = blocked metas.r
        Tuple _ s = runElab (sessionWith emptyStore scheduler)
          (transact (unify site (solvable metas.r) *> waitingOn metas.s))
      solutionOf s.tentative.metas metas.r `shouldEqual` Nothing
      s.tentative.metas.next `shouldEqual` metas.ctx.next
      s.tentative.written `shouldEqual` Set.empty
      (readyIds s.tentative.scheduler) `shouldEqual` []
      blockedOn s.tentative.scheduler metas.r `shouldEqual` Set.singleton id
      map _.awaiting (lookupPending s.tentative.scheduler id) `shouldEqual` Just (Set.singleton metas.r)

    it "leaves the assignments of a discarded candidate out of a later postponement" do
      let
        Tuple outcome _ = runElab session do
          _ <- transact (failingAfter (solvable metas.x))
          unify site stuck
      outcome `shouldEqual` Postponed
        ( SolverStuck
            { blockedOn: Set.fromFoldable [ metas.v, metas.w ]
            , written: Set.fromFoldable [ metas.r, metas.s ]
            }
        )

    it "keeps the fuel a rolled-back candidate spent" do
      let
        spending :: Elab Unit
        spending = spendFuel *> throw failure

        Tuple _ s = runElab session (transact spending)
      s.counters.fuel `shouldEqual` 99

    it "keeps it across a postponement that propagated" do
      let
        spending :: Elab Unit
        spending = spendFuel *> waitingOn metas.r

        Tuple _ s = runElab session (transact spending)
      s.counters.fuel `shouldEqual` 99

  describe "a defect is none of the three outcomes" do
    it "reports a metavariable the context does not hold rather than failing" do
      -- A dependency `Ψ` does not hold is a caller driven against the contract,
      -- and no other candidate repairs it.
      let
        absent = MetaVar 99
        Tuple outcome _ = runElab session (unify site (solvable absent))
      outcome `shouldEqual` Broke (UnifierMisuse here (MetaUnbound absent))

    it "is not caught by a transaction" do
      -- A journal nobody has acted on, which a search reading a defect as a
      -- failure would pass over on its way to the next candidate.
      let
        unread = Set.singleton metas.r
        undrained = session { tentative { metas = metas.ctx { assigned = unread } } }
        Tuple outcome _ = runElab undrained (transact (unify site (solvable metas.s)))
      outcome `shouldEqual` Broke (UnifierMisuse here (AssignmentsUnread unread))
