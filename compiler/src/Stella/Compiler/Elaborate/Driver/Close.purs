-- | Closing a row a function needs nothing of to `()`: a step of the driver,
-- | taken for one owner once the loop is quiescent and the fits are resolved
-- | by direction ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md#closing)).
-- |
-- | **Candidates are found from the owner's term, its undecided fits, and its
-- | residual atoms, and judged on the types alone.** A candidate is an unsolved
-- | metavariable at `Row Effect` that no checking boundary owns. It is closed
-- | where it stands at most once in the types the owner's term writes and its
-- | members are given, and nothing requires anything of it — no undecided fit
-- | has it in its target, no waiting equation or goal could assign it, and no
-- | atom but a `Lacks` names it — a `Lacks` being met by `()`.
-- | A fit only names a row where it is used, so how many fits name one says
-- | nothing of how it stands in a type.
-- |
-- | **The candidates are closed together, under a checkpoint**, and the loop and
-- | the resolution of the owner's fits run again; where either fails, the
-- | closing is undone, and what failed is what the owner is reported by: the
-- | rows decided again without the closing need not fail the same way.
module Stella.Compiler.Elaborate.Driver.Close
  ( Closing(..)
  , Undoing(..)
  , closeRows
  , closeRowsM
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Term (XExpr, standingTypesOfTerm, typesOfTerm)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XConstraint(..), XType(..), metaOccurrences, metasOf)
import Stella.Compiler.Elaborate.Driver.Loop (Attempter, AttempterM, PendingReport, RunResult(..), identically, runAttemptingM)
import Stella.Compiler.Elaborate.Driver.Resolve (ComponentOutcome(..), Resolution(..), resolveOwnersM)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, atLevel, runElabIn, unify)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitState(..))
import Stella.Compiler.Elaborate.Mechanism.Obligation (ResidualAtom(..), residualAtoms)
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Site, goalOf)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), lookupMeta, regionScopeOf, substitute, substituteKind)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic, Warning)
import Stella.Compiler.TypedCore (RowElemKind(..))
import Control.Monad.Rec.Class (class MonadRec)
import Data.Array as Array
import Data.Identity (Identity(..))
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Traversable (traverse)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | What closing an owner's rows came to.
data Closing
  -- | Nothing was a candidate.
  = NothingClosed
  -- | These were closed, and kept.
  | Closed (Set MetaVar)
  -- | These were closed, and the closing was undone where it failed: why,
  -- | which is what the owner is reported by.
  | Undone { closed :: Set MetaVar, cause :: Undoing }

-- | Why a closing was undone.
data Undoing
  -- | Closing, a job it woke, or the resolution after, refused this.
  = UndoneBy Diagnostic
  -- | The loop ran out of fuel with this job next.
  | UndoneWaiting PendingReport

derive instance Eq Undoing
derive instance Generic Undoing _
instance Show Undoing where
  show x = genericShow x

derive instance Eq Closing
derive instance Generic Closing _
instance Show Closing where
  show x = genericShow x

-- | Close the rows of the owner given that nothing needs anything of, at the
-- | level given its binding group's, which closing and resolving again run at:
-- | its members, each the site it is reported at, its term, and the types it is
-- | given. With what the jobs run again warned of where the closing is kept.
-- |
-- | **A candidate is closed at the site of the member it belongs to**: the
-- | first whose term or types write it, or else the fit or the obligation that
-- | found it, so that what closing it breaks is that member's.
closeRows :: forall a k. Ord k => SessionEnv -> Attempter -> (Origin -> k) -> k -> P.Int -> P.Array { site :: Site, term :: XExpr a, types :: P.Array XType } -> SolverState -> Tuple (Either Defect { closing :: Closing, warnings :: P.Array Warning }) SolverState
closeRows session attempter owner key level members s0 = case closeRowsM session (identically attempter) owner key level members s0 of
  Identity result -> result

-- | `closeRows`, each job run again carried out in the monad the attempter
-- | given carries its attempts out in.
closeRowsM :: forall m a k. MonadRec m => Ord k => SessionEnv -> AttempterM m -> (Origin -> k) -> k -> P.Int -> P.Array { site :: Site, term :: XExpr a, types :: P.Array XType } -> SolverState -> m (Tuple (Either Defect { closing :: Closing, warnings :: P.Array Warning }) SolverState)
closeRowsM session attempter owner key level members s0 =
  if Set.isEmpty closable then pure (Tuple (Right { closing: NothingClosed, warnings: [] }) s0)
  else case traverse (\m -> map (Tuple m) (siteOf m)) (Set.toUnfoldable closable :: P.Array MetaVar) of
    -- every candidate was found where some member, fit, or obligation stands
    Nothing -> pure (Tuple (Left (ClosingSiteAbsent (Set.toUnfoldable (Set.filter (isNothing <<< siteOf) closable)))) s0)
    Just sited -> closeAt sited
  where
  closeAt sited = case runElabIn session s0 (atLevel level (for_ sited \(Tuple m site) -> unify site { kind: XKRow RowEffect, left: XMeta m, right: XRowEmpty })) of
    Tuple (Done _) s1 -> do
      Tuple report s2 <- runAttemptingM attempter (s1 { tentative { written = Set.empty } })
      case report.result of
        Halted defect -> pure (Tuple (Left defect) (undo s2))
        Rejected d -> pure (Tuple (Right { closing: Undone { closed: closable, cause: UndoneBy d }, warnings: [] }) (undo s2))
        Exhausted p -> pure (Tuple (Right { closing: Undone { closed: closable, cause: UndoneWaiting p }, warnings: [] }) (undo s2))
        _ -> resolveOwnersM session attempter owner (const level) (_ == key) s2 <#> case _ of
          Tuple (ResolutionHalted defect) s3 -> Tuple (Left defect) (undo s3)
          Tuple (Resolution r) s3 -> case Array.findMap refusal r.components of
            Just d -> Tuple (Right { closing: Undone { closed: closable, cause: UndoneBy d }, warnings: [] }) (undo s3)
            Nothing -> Tuple (Right { closing: Closed closable, warnings: report.warnings <> r.warnings }) s3
    Tuple (Broke defect) s1 -> pure (Tuple (Left defect) (undo s1))
    Tuple (Postponed _) s1 -> pure (Tuple (Left ResolutionPostponed) (undo s1))
    Tuple (Failed d) s1 -> pure (Tuple (Right { closing: Undone { closed: closable, cause: UndoneBy d }, warnings: [] }) (undo s1))

  undo s = s { tentative = s0.tentative }

  refusal c = case c.outcome of
    Refused d -> Just d
    _ -> Nothing

  metas = s0.tentative.metas
  zonked = substitute metas

  -- the types each member's term writes and it is given, where a candidate is
  -- found and sited, every fit kept a fit
  written = map
    (\m -> { site: m.site, metas: Array.concatMap (metaOccurrences <<< zonked) (typesOfTerm (term m) <> m.types) })
    members
  -- where a candidate is counted: a λ's row where its arrow stands, and the row
  -- a decided widening carries no more than an undecided fit's
  occurrences = Array.concatMap (\m -> Array.concatMap (metaOccurrences <<< zonked) (standingTypesOfTerm (term m) <> m.types)) members
  term m = zonkExpr (metas { fits = Map.empty }) m.term

  siteOf m = case Array.find (Array.elem m <<< _.metas) written of
    Just w -> Just w.site
    Nothing -> case Array.find (\f -> Set.member m (Set.union (metasOf f.source) (metasOf f.target))) fits of
      Just f -> Just f.site
      Nothing -> map _.site (Array.find (Set.member m <<< _.metas) atoms)

  owned :: forall r. { origin :: Origin | r } -> P.Boolean
  owned at = owner at.origin == key

  fits = Array.mapMaybe
    ( \record -> case record.state of
        Undecided u | owned record.site -> Just { site: record.site, source: zonked u.source, target: zonked u.target }
        _ -> Nothing
    )
    (Array.fromFoldable (Map.values metas.fits))
  -- the atoms the owner's obligations leave, each about the flexible tails
  -- it holds; one that no longer holds keeps every row it names open
  atoms = Array.concatMap
    ( \entry -> case residualAtoms zonked (regionScopeOf metas) entry.obligation of
        Right left -> map (atomMetas (siteOfObligation entry.obligation)) left
        Left _ -> [ { site: siteOfObligation entry.obligation, metas: constraintMetas entry.obligation.constraint, disjoint: true } ]
    )
    (Array.filter (\entry -> owned entry.obligation) (Array.fromFoldable (Map.values s0.tentative.obligations.entries)))
  -- what a waiting equation or goal could still assign, what it waits on
  -- among it
  equations = Array.mapMaybe
    ( \p -> case p.job of
        JobUnify goal | owned p.site -> Just (Set.unions [ metasOf (zonked goal.left), metasOf (zonked goal.right), p.awaiting ])
        JobSynthesis goal | owned p.site -> Just (Set.union (metasOf (zonked (goalOf goal).expectedType)) p.awaiting)
        _ -> Nothing
    )
    (Array.fromFoldable (Map.values s0.tentative.scheduler.pending))

  siteOfObligation o = { context: o.context, origin: o.origin }

  atomMetas site = case _ of
    LacksAtom _ t -> { site, metas: Set.singleton t, disjoint: false }
    DisjointRigid t _ -> { site, metas: Set.singleton t, disjoint: true }
    DisjointFlexible t1 t2 -> { site, metas: Set.fromFoldable [ t1, t2 ], disjoint: true }

  constraintMetas = case _ of
    XLacks _ row -> metasOf (zonked row)
    XDisjoint l r -> Set.union (metasOf (zonked l)) (metasOf (zonked r))

  found = Set.unions
    [ Set.fromFoldable (Array.concatMap _.metas written)
    , Set.unions (map (\f -> Set.union (metasOf f.source) (metasOf f.target)) fits)
    , Set.unions (map _.metas atoms)
    ]
  required = Set.unions
    [ Set.unions (map (metasOf <<< _.target) fits)
    , Set.unions equations
    , Set.unions (map _.metas (Array.filter _.disjoint atoms))
    ]

  isRow m = case lookupMeta metas m of
    Just (Unsolved info) -> substituteKind metas info.kind == XKRow RowEffect && not (Set.member m metas.boundaryRows)
    _ -> false

  closable = Set.filter (\m -> isRow m && not (Set.member m required) && Array.length (Array.filter (_ == m) occurrences) <= 1) found
