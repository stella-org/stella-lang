-- | Resolving the undecided fits by direction: a step of the driver, taken where
-- | the loop is quiescent, and no attempt of any job
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md#resolving-fits-by-direction)).
-- |
-- | **Fits are resolved in connected components**: the undecided fits, the
-- | pending jobs, and the obligations of one owner sharing an unsolved
-- | metavariable. The owner is the caller's to say — a declaration body, or a
-- | group of them — and two owners share no metavariable. Each component is
-- | resolved under a checkpoint of its own, in rounds, to a fixpoint:
-- |
-- | 1. A target whose remainder is one flexible tail `?m` takes the compatible
-- |    union of the sources of every fit whose target's remainder is `?m`.
-- | 2. A source whose remainder is one instantiation row `?t` takes its target's
-- |    remainder.
-- |
-- | **Each round's assignments are read off the state as it stands and made
-- | together**, rule 1's before rule 2's; ones that depend on one another — one
-- | metavariable reached twice, or one standing in another's solution — are not
-- | made. Each goes through `unify`, and the loop runs the jobs they wake before
-- | the next round. A checking boundary's own fits are taken by neither rule:
-- | a boundary still waiting stands in for them with `fit(U, ρ)`, or `fit(Sᵢ, ρ)`
-- | for each source where the union is not formed, and its ambient row is
-- | never solved here.
-- |
-- | **A component that ends with a fit or a boundary undecided, or in a
-- | failure, is rolled back to its checkpoint**, and what it came to is the
-- | caller's to report.
module Stella.Compiler.Elaborate.Driver.Resolve
  ( Ambiguity(..)
  , ComponentOutcome(..)
  , Resolved
  , Resolution(..)
  , resolveByDirection
  , resolveOwners
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Row (XRowNormalForm, rebuild)
import Stella.Compiler.Elaborate.CorePlus.Term (FitId)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XType(..), metasOf)
import Stella.Compiler.Elaborate.Driver.Loop (Attempter, RunResult(..), runAttempting)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Outcome(..), SessionEnv, SolverState, boundaryFits, currentMetas, fitRemainders, formUnion, runElabIn, unify)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitRecord, FitState(..))
import Stella.Compiler.Elaborate.Mechanism.Obligation (Entry, ObligationId, watchedBy)
import Stella.Compiler.Elaborate.Mechanism.Pending (HandlerGoal, Job(..), Pending, PendingId, Site, goalOf)
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), MetaContext, isInstantiationRow, lookupMeta, substitute)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic, Warning)
import Stella.Compiler.TypedCore (RowElemKind(..))
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldl, for_)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))

-- | Why a component was left undecided.
data Ambiguity
  -- | Two distinct flexible tails, whose disjointness a union would decide.
  = UnionNotFormed (Set MetaVar)
  -- | Assignments of one round depending on one another.
  | AssignmentsDepend (Set MetaVar)
  -- | A fit or a boundary undecided at the fixpoint.
  | LeftUndecided

derive instance Eq Ambiguity
derive instance Generic Ambiguity _
instance Show Ambiguity where
  show x = genericShow x

-- | What a component came to.
data ComponentOutcome
  -- | Every fit and boundary of it decided, and kept.
  = Settled
  -- | Rolled back: what is undecided, and where.
  | Ambiguous { cause :: Ambiguity, origins :: P.Array Origin }
  -- | Rolled back: an assignment, or a job it woke, failed.
  | Refused Diagnostic

derive instance Eq ComponentOutcome
derive instance Generic ComponentOutcome _
instance Show ComponentOutcome where
  show x = genericShow x

-- | A component, by its owner, and what it came to.
type Resolved k =
  { owner :: k
  , outcome :: ComponentOutcome
  }

-- | What the resolution came to, and the warnings the jobs of the components it
-- | kept committed.
data Resolution k
  = Resolution { components :: P.Array (Resolved k), warnings :: P.Array Warning }
  -- | A defect, which leaves nothing to trust.
  | ResolutionHalted Defect

-- | What a component holds.
type Component k =
  { owner :: k
  , fits :: Set FitId
  , boundaries :: Set PendingId
  }

-- | A part of the state a component is made of — a fit, a job, or an
-- | obligation — and the metavariables it touches.
type Part k =
  { owner :: k
  , fit :: Maybe FitId
  , boundary :: Maybe PendingId
  , metas :: Set MetaVar
  }

-- | One assignment a rule makes, and the site it is made at.
type Assignment =
  { meta :: MetaVar
  , solution :: XType
  , site :: Site
  }

-- | Resolve every component holding an undecided fit or a waiting boundary,
-- | each by the owner the function given reads off the site of what it holds.
resolveByDirection :: forall k. Ord k => SessionEnv -> Attempter -> (Origin -> k) -> SolverState -> Tuple (Resolution k) SolverState
resolveByDirection session attempter owner = resolveOwners session attempter owner (const true)

-- | `resolveByDirection`, for the components of the owners the predicate given
-- | admits alone.
resolveOwners :: forall k. Ord k => SessionEnv -> Attempter -> (Origin -> k) -> (k -> P.Boolean) -> SolverState -> Tuple (Resolution k) SolverState
resolveOwners session attempter owner admitted s0 = case componentsOf owner s0 of
  Left defect -> Tuple (ResolutionHalted defect) s0
  Right components -> foldl step (Tuple (Resolution { components: [], warnings: [] }) s0) (Array.filter (admitted <<< _.owner) components)
  where
  step acc component = case acc of
    Tuple (Resolution r) s -> case resolveComponent session attempter component s of
      Tuple (Right done) s' ->
        Tuple (Resolution { components: Array.snoc r.components { owner: component.owner, outcome: done.outcome }, warnings: r.warnings <> done.warnings }) s'
      Tuple (Left defect) s' -> Tuple (ResolutionHalted defect) s'
    halted -> halted

-- | The components holding an undecided fit or a waiting boundary, in the
-- | order the state holds what each is made of.
componentsOf :: forall k. Ord k => (Origin -> k) -> SolverState -> Either Defect (P.Array (Component k))
componentsOf owner s = case Array.find (\(Tuple _ owners) -> Set.size owners > 1) (Map.toUnfoldable ownersOf :: P.Array (Tuple MetaVar (Set k))) of
  Just (Tuple m _) -> Left (OwnersShareMetavariable m)
  Nothing -> Right (Array.filter holdsWork (Array.mapMaybe collect (connected parts)))
  where
  metas = s.tentative.metas
  unsolved = Set.filter \m -> case lookupMeta metas m of
    Just (Unsolved _) -> true
    _ -> false
  typeMetas t = unsolved (metasOf (substitute metas t))

  fitParts = Array.mapMaybe
    ( \(Tuple f record) -> case record.state of
        Undecided u -> Just { owner: owner record.site.origin, fit: Just f, boundary: Nothing, metas: Set.union (typeMetas u.source) (typeMetas u.target) }
        _ -> Nothing
    )
    (Map.toUnfoldable metas.fits :: P.Array (Tuple FitId FitRecord))
  -- a job is joined by every metavariable an attempt of it could assign, and
  -- not only by what it waits on
  jobParts = map
    ( \(Tuple id p) ->
        { owner: owner p.site.origin
        , fit: Nothing
        , boundary: case p.job of
            JobImplicitHandler _ -> Just id
            _ -> Nothing
        , metas: Set.union p.awaiting case p.job of
            JobUnify goal -> Set.union (typeMetas goal.left) (typeMetas goal.right)
            JobEffectFit f -> case Map.lookup f metas.fits of
              Just { state: Undecided u } -> Set.union (typeMetas u.source) (typeMetas u.target)
              _ -> Set.empty
            JobSynthesis goal -> typeMetas (goalOf goal).expectedType
            JobImplicitHandler goal -> Set.union (unsolved (Set.singleton goal.boundary)) (typeMetas goal.expected)
        }
    )
    (Map.toUnfoldable s.tentative.scheduler.pending :: P.Array (Tuple PendingId Pending))
  obligationParts = map
    (\(Tuple id entry) -> { owner: owner entry.obligation.origin, fit: Nothing, boundary: Nothing, metas: unsolved (watchedBy s.tentative.obligations id) })
    (Map.toUnfoldable s.tentative.obligations.entries :: P.Array (Tuple ObligationId Entry))
  parts = fitParts <> jobParts <> obligationParts

  ownersOf :: Map MetaVar (Set k)
  ownersOf = foldl (\acc u -> foldl (\a m -> Map.insertWith Set.union m (Set.singleton u.owner) a) acc (Set.toUnfoldable u.metas :: P.Array MetaVar)) Map.empty parts

  collect group = map (\u -> { owner: u.owner, fits: Set.fromFoldable (Array.mapMaybe _.fit group), boundaries: Set.fromFoldable (Array.mapMaybe _.boundary group) }) (Array.head group)

  holdsWork c = not (Set.isEmpty c.fits && Set.isEmpty c.boundaries)

-- | The parts grouped by the metavariables of one owner they share, each group
-- | in the order the parts are given, the groups in the order of their first.
connected :: forall k. Ord k => P.Array (Part k) -> P.Array (P.Array (Part k))
connected parts = map (Array.mapMaybe (Array.index parts)) (go Set.empty 0 [])
  where
  count = Array.length parts

  byKey :: Map (Tuple k MetaVar) (P.Array P.Int)
  byKey = foldl (\acc (Tuple i u) -> foldl (\a m -> Map.insertWith (flip (<>)) (Tuple u.owner m) [ i ] a) acc (Set.toUnfoldable u.metas :: P.Array MetaVar)) Map.empty (Array.mapWithIndex Tuple parts)

  neighbours i = case Array.index parts i of
    Just u -> Array.concatMap (\m -> fromMaybe [] (Map.lookup (Tuple u.owner m) byKey)) (Set.toUnfoldable u.metas :: P.Array MetaVar)
    Nothing -> []

  go visited i acc =
    if i >= count then acc
    else if Set.member i visited then go visited (i + 1) acc
    else
      let
        group = reach (Set.singleton i) [ i ]
      in
        go (Set.union visited group) (i + 1) (Array.snoc acc (Array.sort (Set.toUnfoldable group)))

  reach seen frontier = case Array.uncons frontier of
    Nothing -> seen
    Just { head, tail } ->
      let
        new = Array.nub (Array.filter (\j -> not (Set.member j seen)) (neighbours head))
      in
        reach (Set.union seen (Set.fromFoldable new)) (tail <> new)

-- | Resolve one component under a checkpoint of its own, in rounds to a
-- | fixpoint, each round spending one unit of fuel.
resolveComponent :: forall k. SessionEnv -> Attempter -> Component k -> SolverState -> Tuple (Either Defect { outcome :: ComponentOutcome, warnings :: P.Array Warning }) SolverState
resolveComponent session attempter component s0 = round [] s0
  where
  checkpoint = s0.tentative
  ended outcome warnings s = Tuple (Right { outcome, warnings }) (s { tentative { written = Set.empty } })
  -- rolled back to the checkpoint, where it stands read first; the warnings
  -- of the jobs it ran go with what they did
  undecided cause _ s = ended (Ambiguous { cause, origins: undecidedOrigins s }) [] (s { tentative = checkpoint })
  refused diagnostic _ s = ended (Refused diagnostic) [] (s { tentative = checkpoint })
  halted defect s = Tuple (Left defect) (s { tentative = checkpoint })

  -- **A round that assigns nothing is a fixpoint only where it made no
  -- progress**: an equation of a union, or a job it woke, may still have
  -- assigned something or decided a fit, and a union not formed is waited on
  -- until nothing moves.
  round warnings s =
    if s.retained.fuel <= 0 then undecided LeftUndecided warnings s
    else case runElabIn session s (assignmentsOf component (boundariesOf s)) of
      Tuple (Done (Left cause)) s1 -> undecided cause warnings s1
      Tuple (Done (Right found)) s1 -> case runElabIn session s1 (for_ found.assignments \a -> unify a.site { kind: XKRow RowEffect, left: XMeta a.meta, right: a.solution }) of
        Tuple (Done _) s2 ->
          let
            Tuple report s3 = runAttempting attempter (s2 { tentative { written = Set.empty }, retained { fuel = s2.retained.fuel - 1 } })
            warnings' = warnings <> report.warnings
            settledOr cause =
              if Array.null (undecidedOrigins s3) then ended Settled warnings' s3
              else undecided cause warnings' s3
          in
            case report.result of
              Rejected diagnostic -> refused diagnostic warnings' s3
              Halted defect -> halted defect s3
              Exhausted _ -> undecided LeftUndecided warnings' s3
              _
                | not (Array.null found.assignments) || progressed s s3 -> round warnings' s3
                | Set.isEmpty found.unformed -> settledOr LeftUndecided
                | otherwise -> settledOr (UnionNotFormed found.unformed)
        Tuple (Failed diagnostic) s2 -> refused diagnostic warnings s2
        Tuple (Broke defect) s2 -> halted defect s2
        Tuple (Postponed _) s2 -> halted ResolutionPostponed s2
      Tuple (Failed diagnostic) s1 -> refused diagnostic warnings s1
      Tuple (Broke defect) s1 -> halted defect s1
      Tuple (Postponed _) s1 -> halted ResolutionPostponed s1

  -- something assigned, or a fit of the component decided, since the state
  -- given
  progressed before after =
    assignedIn after > assignedIn before || Array.length (undecidedOrigins after) < Array.length (undecidedOrigins before)
  assignedIn s = Map.size
    ( Map.filter
        ( \b -> case b of
            Assigned _ -> true
            Unsolved _ -> false
        )
        s.tentative.metas.bindings
    )

  -- the component's boundaries still waiting, with their goals
  boundariesOf s = Array.mapMaybe
    ( \id -> case Map.lookup id s.tentative.scheduler.pending of
        Just { site, job: JobImplicitHandler goal } -> Just { site, goal }
        _ -> Nothing
    )
    (Set.toUnfoldable component.boundaries)

  -- where each fit and boundary of the component still undecided stands
  undecidedOrigins s =
    Array.mapMaybe
      ( \f -> case Map.lookup f s.tentative.metas.fits of
          Just { site, state: Undecided _ } -> Just site.origin
          _ -> Nothing
      )
      (Set.toUnfoldable component.fits)
      <> map _.site.origin (boundariesOf s)

-- | The assignments of one round, read off the state as it stands, and the
-- | tails of each union not formed yet; or why the component is ambiguous.
assignmentsOf :: forall k. Component k -> P.Array { site :: Site, goal :: HandlerGoal } -> Elab (Either Ambiguity { assignments :: P.Array Assignment, unformed :: Set MetaVar })
assignmentsOf component boundaries = do
  metas <- currentMetas
  remainders <- fitRemainders component.fits
  virtual <- map Array.concat $ for boundaries \b -> map (map (\r -> { site: b.site, source: r.source, target: r.target })) (boundaryFits b.site b.goal)
  let
    boundaryRows = metas.boundaryRows
    -- a fit whose target is a boundary's ambient row is that boundary's, and
    -- the boundary stands in for it
    owned = Array.filter (\f -> Set.isEmpty (Set.intersection f.target.flexible boundaryRows)) remainders
    fits = map (\f -> { site: f.site, source: f.source, target: f.target }) owned <> virtual

    lone :: XRowNormalForm -> Maybe MetaVar
    lone n = case Set.toUnfoldable n.flexible :: P.Array MetaVar of
      [ m ] | Map.isEmpty n.known && Set.isEmpty n.rigid && not (Set.member m boundaryRows) -> Just m
      _ -> Nothing

    targets = Array.nub (Array.mapMaybe (lone <<< _.target) fits)
  rule1 <- for targets \m -> case Array.filter (\f -> lone f.target == Just m) fits of
    into | Just first <- Array.head into ->
      map (map (\u -> [ { meta: m, solution: rebuild u, site: first.site } ])) (formUnion (map (\f -> { site: f.site, row: f.source }) into))
    _ -> pure (Right [])
  let
    rule2 = Array.mapMaybe
      ( \f -> case lone f.source of
          Just t | isInstantiationRow metas t -> Just { meta: t, solution: rebuild f.target, site: f.site }
          _ -> Nothing
      )
      fits
  let
    formed = Array.concat (Array.mapMaybe (either (const Nothing) Just) rule1)
    unformed = Set.unions (Array.mapMaybe (either Just (const Nothing)) rule1)
  pure (map (\assignments -> { assignments, unformed }) (independent metas (formed <> rule2)))

-- | The assignments given, where none depends on another: one metavariable
-- | given one solution, and no solution holding a metavariable assigned
-- | beside it.
independent :: MetaContext -> P.Array Assignment -> Either Ambiguity (P.Array Assignment)
independent metas assignments =
  if not (Set.isEmpty conflicting) then Left (AssignmentsDepend conflicting)
  else Right distinct
  where
  solved a = substitute metas a.solution
  distinct = Array.nubByEq (\a b -> a.meta == b.meta && solved a == solved b) assignments
  assigned = Set.fromFoldable (map _.meta distinct)
  twice = Set.fromFoldable (map _.meta (Array.filter (\a -> Array.length (Array.filter (\b -> b.meta == a.meta) distinct) > 1) distinct))
  standing = Set.unions (map (\a -> Set.intersection assigned (metasOf (solved a))) distinct)
  conflicting = Set.union twice standing
