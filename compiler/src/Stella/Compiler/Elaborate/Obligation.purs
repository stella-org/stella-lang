-- | The row constraints a substitution must preserve, and where each came from.
-- |
-- | A constraint whose row has a flexible tail says nothing about the variables a
-- | context binds, so it yields no atomic fact and a context cannot enforce it
-- | ([Context](Context.purs)). What it does say is a condition on what that
-- | metavariable may be solved to — `k ∉ ?r` forbids `?r := ( k : A | () )` —
-- | which is what is kept here and re-decided at every assignment.
-- |
-- | **Each obligation carries the context it came from**, and is decided against
-- | the facts of that context and no other. The assignment to be judged may
-- | happen anywhere, under assumptions that have nothing to do with the
-- | constraint being preserved.
-- |
-- | ```text
-- | at the outer site      k ∉ ?r  required of a row being built
-- |                        k ∉ t   assumed
-- | at an inner site       ?r := t
-- | ```
-- |
-- | What admits that assignment is the outer site's `k ∉ t`. Deciding it against
-- | the site the assignment was made at would prove it from assumptions that do
-- | not hold where the requirement arose, and refuse it where the assumptions
-- | that do hold prove it.
-- |
-- | Which facts decide it is one half; the other is **what it takes to hold at
-- | all**, which is what `Basis` below distinguishes.
module Stella.Compiler.Elaborate.Obligation
  ( ObligationId(..)
  , Basis(..)
  , Obligation
  , Entry
  , ObligationStore
  , Standing(..)
  , Breach(..)
  , emptyStore
  , introduce
  , touching
  , obligationOf
  , watchedBy
  , standing
  , recheck
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Context (FactsError, Origin, XContext, Zonk, facts)
import Stella.Compiler.Elaborate.Row (XRowError, knownKeys, rigidTails, sharedKey, xnf)
import Stella.Compiler.Elaborate.Type (MetaVar, XConstraint(..))
import Stella.Compiler.TypedCore (RowKey, TyVar)
import Stella.Compiler.TypedCore.Entailment (AtomicFacts, knownDisjoint, knownToLack, noFacts)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, foldr)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

newtype ObligationId = ObligationId P.Int

-- | Why a constraint has to hold, which is what decides what it takes to hold.
-- |
-- | The two are not interchangeable, and deciding one by the other's rule is a
-- | hole either way: an assumption held to the second rule can prove itself,
-- | since zonking it is how its own site's facts grow, and a requirement held to
-- | the first admits a rigid tail nothing proves anything about.
data Basis
  -- | The site assumes it. What a site assumes is the authority its facts are
  -- | derived from, so nothing has to prove it; what an assignment may not do is
  -- | make it **unsatisfiable**, and the final Core context would then carry a
  -- | contradiction.
  = Assumed
  -- | The solver requires it of a row it is building — that a record row not
  -- | repeat a key, that two rows joined by `⊎` stay apart. A rigid tail entering
  -- | such a row has to be **proved** to satisfy it from the facts of the site the
  -- | requirement arose at: what holds of a rigid variable is what its own context
  -- | gives and nothing else.
  | Required

-- | One row constraint that must hold, why it must, and where it came from.
type Obligation =
  { constraint :: XConstraint
  , basis :: Basis
  , context :: XContext
  , origin :: Origin
  }

-- | What the store holds of an obligation beside the obligation itself: the
-- | metavariables it is currently indexed under.
-- |
-- | These change as the obligation is re-decided. A refinement that solves `?r`
-- | to a row whose tail is `?t` leaves the obligation watching `?t`, and nothing
-- | has to say which fresh tail arose from which: zonking the constraint says it.
type Entry =
  { obligation :: Obligation
  , watching :: Set MetaVar
  }

-- | The obligations, indexed by the metavariables whose assignment has to
-- | re-decide them.
-- |
-- | This is part of what an attempt owns: an assumption introduced by an attempt
-- | that is abandoned, and a propagation one performed, are both undone with the
-- | rest of its work.
type ObligationStore =
  { entries :: Map ObligationId Entry
  , watchers :: Map MetaVar (Set ObligationId)
  , next :: P.Int
  }

-- | Whether an obligation still has anything to watch.
data Standing
  -- | Proved from the facts of its own site, with no metavariable left in it.
  -- | Nothing can break it afterwards, so the store stops holding it.
  = Discharged
  -- | It holds of what is known and still constrains these metavariables.
  | Watching (Set MetaVar)

data Breach
  -- | `k ∉ ρ` where the solution put `k` into `ρ`.
  = SolutionCarriesKey RowKey
  -- | `k ∉ ρ` where the solution put a rigid tail into `ρ` that the obligation's
  -- | own site does not prove lacks `k`.
  | LacksUnprovenAtSite RowKey TyVar
  -- | `ρ1 # ρ2` where the solution gave the two a key in common.
  | SidesShareKey RowKey
  -- | `ρ1 # ρ2` where two rigid tails met that the obligation's own site does not
  -- | prove disjoint.
  | DisjointUnprovenAtSite TyVar TyVar
  -- | The assumptions of the site an obligation came from are contradictory,
  -- | which is a property of that context and is reported against it.
  | SiteFactsFailed FactsError
  | ObligationNotARow XRowError

emptyStore :: ObligationStore
emptyStore =
  { entries: Map.empty
  , watchers: Map.empty
  , next: 0
  }

-- | Take on an obligation, deciding it where it is introduced.
-- |
-- | **Nothing enters the store undecided.** What the store holds is what is
-- | watched, and what watches nothing is never re-decided: an obligation whose
-- | constraint has no metavariable in it would sit there unread while a closed
-- | requirement went unproved or an assumption stood already contradicted.
-- | Deciding it here is what makes the store's contents mean "holds so far, and
-- | these are what could still break it".
-- |
-- | ```text
-- | Left breach        refused where it is introduced
-- | Right (Nothing)    settled, and nothing left that could break it
-- | Right (Just id)    watched, under the metavariables it still constrains
-- | ```
introduce
  :: Zonk
  -> Obligation
  -> ObligationStore
  -> Either Breach (Tuple (Maybe ObligationId) ObligationStore)
introduce zonk obligation store = case decide zonk obligation of
  Left breach ->
    Left breach
  Right Discharged ->
    Right (Tuple Nothing store)
  Right (Watching ms) ->
    let
      Tuple id store' = hold obligation ms store
    in
      Right (Tuple (Just id) store')

-- | Which facts an obligation is decided against, and what they decide.
-- |
-- | A `Required` one is decided against **the facts of its own site**, derived
-- | through the same zonk, so that what admits an assignment is what was assumed
-- | where the requirement arose and not what happens to be assumed where the
-- | assignment was made. An `Assumed` one needs no facts at all: what would prove
-- | it is itself.
decide :: Zonk -> Obligation -> Either Breach Standing
decide zonk obligation = case obligation.basis of
  Assumed ->
    standing Assumed noFacts zonk obligation.constraint
  Required -> case facts zonk obligation.context of
    Left err -> Left (SiteFactsFailed err)
    Right sitefacts -> standing Required sitefacts zonk obligation.constraint

-- | Record an obligation under the metavariables it watches.
-- |
-- | Which those are is what deciding it said, and it is not the same as which the
-- | constraint mentions: one that is already solved is mentioned by the written
-- | form and watched by nothing.
hold :: Obligation -> Set MetaVar -> ObligationStore -> Tuple ObligationId ObligationStore
hold obligation watching store =
  Tuple id
    store
      { entries = Map.insert id { obligation, watching } store.entries
      , watchers = foldr (watch id) store.watchers (Set.toUnfoldable watching :: P.Array MetaVar)
      , next = store.next + 1
      }
  where
  id = ObligationId store.next

touching :: MetaVar -> ObligationStore -> Set ObligationId
touching m store = fromMaybe Set.empty (Map.lookup m store.watchers)

obligationOf :: ObligationStore -> ObligationId -> Maybe Obligation
obligationOf store id = map _.obligation (Map.lookup id store.entries)

watchedBy :: ObligationStore -> ObligationId -> Set MetaVar
watchedBy store id = case Map.lookup id store.entries of
  Nothing -> Set.empty
  Just entry -> entry.watching

-- | Whether one constraint still holds of what `Ψ` has solved.
-- |
-- | **A flexible tail defers rather than decides.** Nothing is known about what
-- | it will be solved to, so the constraint is neither settled nor broken; it is
-- | kept and re-decided when that metavariable is assigned. What is decided now
-- | is what the known part and the rigid tails say, since no assignment changes
-- | either.
-- |
-- | The satisfiability of the zonked constraint is read whatever its basis. The
-- | entailment of its rigid tails is read only where the basis is `Required`,
-- | and the facts are then the ones the site it arose at gives.
standing :: Basis -> AtomicFacts -> Zonk -> XConstraint -> Either Breach Standing
standing basis sitefacts zonk = case _ of
  XLacks key row -> do
    n <- normalize row
    if Map.member key n.known then
      Left (SolutionCarriesKey key)
    else do
      _ <- case basis of
        Assumed -> Right unit
        Required -> case Array.find (\t -> not (knownToLack sitefacts key t)) (rigidTails n) of
          Just t -> Left (LacksUnprovenAtSite key t)
          Nothing -> Right unit
      Right (watchingOf n.flexible)

  XDisjoint left right -> do
    l <- normalize left
    r <- normalize right
    case sharedKey l r of
      Just key ->
        Left (SidesShareKey key)
      Nothing -> do
        _ <- case basis of
          Assumed -> Right unit
          Required -> do
            _ <- keysAgainstTails l r
            _ <- keysAgainstTails r l
            tailsApart l r
        Right (watchingOf (Set.union l.flexible r.flexible))

  where
  normalize row = case xnf (zonk row) of
    Left err -> Left (ObligationNotARow err)
    Right n -> Right n

  -- Each key of one side must be absent from every rigid tail of the other.
  keysAgainstTails a b =
    foldM
      ( \_ key -> case Array.find (\t -> not (knownToLack sitefacts key t)) (rigidTails b) of
          Just t -> Left (LacksUnprovenAtSite key t)
          Nothing -> Right unit
      )
      unit
      (knownKeys a)

  tailsApart l r =
    foldM
      ( \_ t1 -> case Array.find (\t2 -> not (knownDisjoint sitefacts t1 t2)) (rigidTails r) of
          Just t2 -> Left (DisjointUnprovenAtSite t1 t2)
          Nothing -> Right unit
      )
      unit
      (rigidTails l)

-- | Re-decide every obligation the metavariables given are watched by.
-- |
-- | This is what an assignment owes: the substitution is recorded, the jobs
-- | blocked on the metavariable are woken, and the obligations it was watched by
-- | are re-decided. A `Required` obligation is decided against **the facts of its
-- | own site**, derived through the same zonk, so that what admits an assignment
-- | is what was assumed where the requirement arose and not what happens to be
-- | assumed where the assignment was made.
-- |
-- | An `Assumed` one needs no facts at all: what would prove it is itself.
recheck
  :: Zonk
  -> Set MetaVar
  -> ObligationStore
  -> Either (Tuple ObligationId Breach) ObligationStore
recheck zonk assigned store =
  foldM one store affected
  where
  affected :: P.Array ObligationId
  affected =
    Set.toUnfoldable
      ( foldr (\m acc -> Set.union (touching m store) acc) Set.empty
          (Set.toUnfoldable assigned :: P.Array MetaVar)
      )

  one acc id = case Map.lookup id acc.entries of
    Nothing ->
      Right acc
    Just entry -> case decide zonk entry.obligation of
      Left breach -> Left (Tuple id breach)
      Right Discharged -> Right (forget id entry acc)
      Right (Watching ms) -> Right (rewatch id entry ms acc)

-- | An obligation nothing can break again is dropped, together with what
-- | indexed it.
forget :: ObligationId -> Entry -> ObligationStore -> ObligationStore
forget id entry store =
  store
    { entries = Map.delete id store.entries
    , watchers = foldr (unwatch id) store.watchers
        (Set.toUnfoldable entry.watching :: P.Array MetaVar)
    }

-- | The index follows the constraint. A metavariable that has been solved is no
-- | longer watched, since nothing will assign it again, and one the solution
-- | introduced is watched from now on.
rewatch :: ObligationId -> Entry -> Set MetaVar -> ObligationStore -> ObligationStore
rewatch id entry ms store =
  store
    { entries = Map.insert id (entry { watching = ms }) store.entries
    , watchers =
        foldr (watch id)
          ( foldr (unwatch id) store.watchers
              (Set.toUnfoldable (Set.difference entry.watching ms) :: P.Array MetaVar)
          )
          (Set.toUnfoldable (Set.difference ms entry.watching) :: P.Array MetaVar)
    }

watch :: ObligationId -> MetaVar -> Map MetaVar (Set ObligationId) -> Map MetaVar (Set ObligationId)
watch id m watchers = Map.insertWith Set.union m (Set.singleton id) watchers

unwatch :: ObligationId -> MetaVar -> Map MetaVar (Set ObligationId) -> Map MetaVar (Set ObligationId)
unwatch id m watchers = case Map.lookup m watchers of
  Nothing -> watchers
  Just ids ->
    let
      rest = Set.delete id ids
    in
      if Set.isEmpty rest then Map.delete m watchers else Map.insert m rest watchers

watchingOf :: Set MetaVar -> Standing
watchingOf ms = if Set.isEmpty ms then Discharged else Watching ms

derive instance Eq ObligationId
derive instance Ord ObligationId
derive newtype instance Show ObligationId

derive instance Eq Basis
derive instance Generic Basis _

instance Show Basis where
  show x = genericShow x

derive instance Eq Standing
derive instance Generic Standing _

instance Show Standing where
  show x = genericShow x

derive instance Eq Breach
derive instance Generic Breach _

instance Show Breach where
  show x = genericShow x
