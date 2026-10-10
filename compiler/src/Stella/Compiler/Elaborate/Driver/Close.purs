-- | Closing a row a function needs nothing of to `()`: a step of the driver,
-- | taken for one owner once the loop is quiescent and the fits are resolved
-- | by direction ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md#closing)).
-- |
-- | **Candidates are found from the owner's term, its undecided fits, and its
-- | residual atoms, and judged on the types alone.** A candidate is an unsolved
-- | metavariable at `Row Effect` that no checking boundary owns. It is closed
-- | where it stands at most once in the types the owner's term writes, nothing
-- | requires anything of it — no undecided fit has it in its target, no
-- | waiting equation or goal could assign it, and no atom but a `Lacks` names
-- | it — a `Lacks` being met by `()`.
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
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Term (XExpr, typesOfTerm)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XConstraint(..), XType(..), metaOccurrences, metasOf)
import Stella.Compiler.Elaborate.Driver.Loop (Attempter, PendingReport, RunResult(..), runAttempting)
import Stella.Compiler.Elaborate.Driver.Resolve (ComponentOutcome(..), Resolution(..), resolveOwners)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), SessionEnv, SolverState, runElabIn, unify)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitState(..))
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Site, goalOf)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), lookupMeta, substitute, substituteKind)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic)
import Stella.Compiler.TypedCore (RowElemKind(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..))
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

-- | Close the rows of the owner given that nothing needs anything of, its term
-- | the one given and the site given where it is reported.
closeRows :: forall a k. Ord k => SessionEnv -> Attempter -> (Origin -> k) -> k -> Site -> XExpr a -> SolverState -> Tuple (Either Defect Closing) SolverState
closeRows session attempter owner key site term s0 =
  if Set.isEmpty closable then Tuple (Right NothingClosed) s0
  else case runElabIn session s0 (for_ (Set.toUnfoldable closable :: P.Array MetaVar) \m -> unify site { kind: XKRow RowEffect, left: XMeta m, right: XRowEmpty }) of
    Tuple (Done _) s1 ->
      let
        Tuple report s2 = runAttempting attempter (s1 { tentative { written = Set.empty } })
      in
        case report.result of
          Halted defect -> Tuple (Left defect) (undo s2)
          Rejected d -> Tuple (Right (Undone { closed: closable, cause: UndoneBy d })) (undo s2)
          Exhausted p -> Tuple (Right (Undone { closed: closable, cause: UndoneWaiting p })) (undo s2)
          _ -> case resolveOwners session attempter owner (_ == key) s2 of
            Tuple (ResolutionHalted defect) s3 -> Tuple (Left defect) (undo s3)
            Tuple (Resolution r) s3 -> case Array.findMap refusal r.components of
              Just d -> Tuple (Right (Undone { closed: closable, cause: UndoneBy d })) (undo s3)
              Nothing -> Tuple (Right (Closed closable)) s3
    Tuple (Broke defect) s1 -> Tuple (Left defect) (undo s1)
    Tuple (Postponed _) s1 -> Tuple (Left ResolutionPostponed) (undo s1)
    Tuple (Failed d) s1 -> Tuple (Right (Undone { closed: closable, cause: UndoneBy d })) (undo s1)
  where
  undo s = s { tentative = s0.tentative }

  refusal c = case c.outcome of
    Refused d -> Just d
    _ -> Nothing

  metas = s0.tentative.metas
  zonked = substitute metas

  -- the types the owner's term writes, where a candidate is counted
  occurrences = Array.concatMap (metaOccurrences <<< zonked) (typesOfTerm (zonkExpr metas term))

  owned :: forall r. { origin :: Origin | r } -> P.Boolean
  owned at = owner at.origin == key

  fits = Array.mapMaybe
    ( \record -> case record.state of
        Undecided u | owned record.site -> Just { source: zonked u.source, target: zonked u.target }
        _ -> Nothing
    )
    (Array.fromFoldable (Map.values metas.fits))
  atoms = map (\entry -> entry.obligation.constraint) (Array.filter (\entry -> owned entry.obligation) (Array.fromFoldable (Map.values s0.tentative.obligations.entries)))
  -- what a waiting equation or goal could still assign, what it waits on
  -- among it
  equations = Array.mapMaybe
    ( \p -> case p.job of
        JobUnify goal | owned p.site -> Just (Set.unions [ metasOf (zonked goal.left), metasOf (zonked goal.right), p.awaiting ])
        JobSynthesis goal | owned p.site -> Just (Set.union (metasOf (zonked (goalOf goal).expectedType)) p.awaiting)
        _ -> Nothing
    )
    (Array.fromFoldable (Map.values s0.tentative.scheduler.pending))

  constraintMetas = case _ of
    XLacks _ row -> metasOf (zonked row)
    XDisjoint l r -> Set.union (metasOf (zonked l)) (metasOf (zonked r))

  found = Set.unions
    [ Set.fromFoldable occurrences
    , Set.unions (map (\f -> Set.union (metasOf f.source) (metasOf f.target)) fits)
    , Set.unions (map constraintMetas atoms)
    ]
  required = Set.unions
    [ Set.unions (map (metasOf <<< _.target) fits)
    , Set.unions equations
    , Set.unions (map constraintMetas (Array.filter isDisjoint atoms))
    ]
  isDisjoint = case _ of
    XDisjoint _ _ -> true
    XLacks _ _ -> false

  isRow m = case lookupMeta metas m of
    Just (Unsolved info) -> substituteKind metas info.kind == XKRow RowEffect && not (Set.member m metas.boundaryRows)
    _ -> false

  closable = Set.filter (\m -> isRow m && not (Set.member m required) && Array.length (Array.filter (_ == m) occurrences) <= 1) found
