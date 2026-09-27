-- | The three tables a pending job lives in, and the bookkeeping that moves it
-- | between them.
-- |
-- | ```text
-- | ready   : [(PendingId, Phase)]
-- | blocked : Meta ⇀ Set PendingId
-- | pending : PendingId ⇀ Pending
-- | ```
-- |
-- | Nothing here runs a job. An assignment that reaches a blocked job leaves it
-- | on the ready queue and nothing more, so that the loop is the only thing that
-- | opens an attempt: running a job from inside an assignment would open one
-- | while another is still open, and a job reachable from two assignments of one
-- | attempt would start twice.
-- |
-- | The whole of this is part of what an attempt owns, so a rollback restores
-- | it: a wake an abandoned attempt made goes back to waiting where it was.
module Stella.Compiler.Elaborate.Scheduler
  ( Scheduler
  , Phase(..)
  , Queued
  , Invariant(..)
  , emptyScheduler
  , create
  , enqueueInitial
  , readyIds
  , nextReady
  , isInitial
  , reblock
  , wake
  , takeReady
  , complete
  , lookupPending
  , blockedOn
  , unwakeable
  , invariants
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Pending (Job, Pending, PendingId(..), Site)
import Stella.Compiler.Elaborate.Type (MetaVar)
import Data.Array as Array
import Data.Foldable (foldl, foldr)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | Why a job is on the ready queue.
data Phase
  -- | For its first attempt: it was created inside an attempt, which may not
  -- | run it there. Fuel bounds retries, so the loop spends none on it.
  = Initial
  -- | For another attempt, a wake having put it there.
  | Retry

-- | An entry of the ready queue. The phase is carried by the entry itself, so
-- | whether a job is a first attempt is read from one place.
type Queued =
  { id :: PendingId
  , phase :: Phase
  }

type Scheduler =
  { ready :: P.Array Queued
  , blocked :: Map MetaVar (Set PendingId)
  , pending :: Map PendingId Pending
  , nextId :: P.Int
  }

-- | What the tables hold of one another. Each is checked rather than assumed,
-- | since every one of them is a way for a job to be run twice or never.
data Invariant
  -- | A job registered under a metavariable its `awaiting` does not name, or
  -- | awaiting one it is not registered under. The removal a wake performs reads
  -- | `awaiting`, so a registration the set does not name is never removed.
  = RegistrationDiffers MetaVar PendingId
  -- | A job on the ready queue that still awaits something. It would be run and
  -- | then woken again by an assignment it no longer depends on.
  | AwaitingWhileReady PendingId
  -- | An identifier one of the queues holds and `pending` does not.
  | UnknownPending PendingId
  -- | One identifier twice on the ready queue, which runs one job twice.
  | DuplicateOnReady PendingId
  -- | A job at once ready and blocked. An assignment would wake what is already
  -- | on the queue.
  | ReadyAndBlocked PendingId

emptyScheduler :: Scheduler
emptyScheduler =
  { ready: []
  , blocked: Map.empty
  , pending: Map.empty
  , nextId: 0
  }

-- | A job the elaborator has just met.
-- |
-- | It exists and awaits nothing, which is the state a job is in while it is
-- | being attempted: neither queue holds it, and the frame running it does.
create :: Site -> Job -> Scheduler -> Tuple PendingId Scheduler
create site job s =
  Tuple id
    s
      { pending = Map.insert id { id, site, awaiting: Set.empty, job } s.pending
      , nextId = s.nextId + 1
      }
  where
  id = PendingId s.nextId

-- | Queue a job just created for its first attempt, as the attempt that created
-- | it may not run it.
enqueueInitial :: PendingId -> Scheduler -> Scheduler
enqueueInitial id s = s { ready = Array.snoc s.ready { id, phase: Initial } }

-- | The identifiers on the ready queue, front first.
readyIds :: Scheduler -> P.Array PendingId
readyIds s = map _.id s.ready

-- | The entry `takeReady` would take.
nextReady :: Scheduler -> Maybe Queued
nextReady s = Array.head s.ready

-- | Whether a job is on the ready queue for its first attempt.
isInitial :: Scheduler -> PendingId -> P.Boolean
isInitial s id = Array.any (\q -> q.id == id && q.phase == Initial) s.ready

-- | Register a job under each metavariable it waits on.
-- |
-- | The caller has admitted the set: every metavariable in it is one `Ψ` holds
-- | unsolved, so each can be woken by an assignment (D40). The pending is
-- | written back rather than looked up, the frame that postponed it being what
-- | holds it.
reblock :: Pending -> Set MetaVar -> Scheduler -> Scheduler
reblock p ms s =
  s
    { pending = Map.insert p.id (p { awaiting = ms }) s.pending
    , blocked = foldr (register p.id) s.blocked (Set.toUnfoldable ms :: P.Array MetaVar)
    }

-- | An assignment reaching the jobs blocked on it.
-- |
-- | Waking removes a job from **every** metavariable it was registered under and
-- | not only from the one that woke it; `awaiting` is what that removal reads, so
-- | nothing scans the table. A stale entry left behind would put a job on the
-- | queue that is already on it.
-- |
-- | Where one assignment wakes several jobs, they are queued in the order they
-- | were created, an identifier being allocated in that order. Each is queued for
-- | a retry.
wake :: MetaVar -> Scheduler -> Scheduler
wake m s = foldl (\acc id -> wakeOne id acc) s ids
  where
  ids :: P.Array PendingId
  ids = Set.toUnfoldable (fromMaybe Set.empty (Map.lookup m s.blocked))

  wakeOne id acc = case Map.lookup id acc.pending of
    -- An identifier the table holds and `pending` does not names no job, so
    -- there is nothing to wake and nothing to read a registration from.
    Nothing -> acc { blocked = unregister id m acc.blocked }
    Just p ->
      acc
        { blocked = foldr (unregister id) acc.blocked
            (Set.toUnfoldable p.awaiting :: P.Array MetaVar)
        , pending = Map.insert id (p { awaiting = Set.empty }) acc.pending
        , ready = Array.snoc acc.ready { id, phase: Retry }
        }

-- | The next job to attempt.
-- |
-- | The queue is taken from the front and pushed at the back, so that a job
-- | woken earlier is attempted earlier and nothing on it can be starved by work
-- | that keeps arriving.
takeReady :: Scheduler -> Maybe (Tuple PendingId Scheduler)
takeReady s = case Array.uncons s.ready of
  Nothing -> Nothing
  Just { head, tail } -> Just (Tuple head.id (s { ready = tail }))

-- | A job that is solved, or that has failed.
-- |
-- | Nothing is left that names it: a registration outliving the job would wake
-- | an identifier no table can resolve.
complete :: PendingId -> Scheduler -> Scheduler
complete id s = case Map.lookup id s.pending of
  Nothing -> s
  Just p ->
    s
      { pending = Map.delete id s.pending
      , blocked = foldr (unregister id) s.blocked
          (Set.toUnfoldable p.awaiting :: P.Array MetaVar)
      , ready = Array.filter (\q -> q.id /= id) s.ready
      }

lookupPending :: Scheduler -> PendingId -> Maybe Pending
lookupPending s id = Map.lookup id s.pending

blockedOn :: Scheduler -> MetaVar -> Set PendingId
blockedOn s m = fromMaybe Set.empty (Map.lookup m s.blocked)

-- | The jobs no assignment can reach: held by `pending`, on neither queue, and
-- | registered under nothing.
-- |
-- | While a job is being attempted it is exactly that, so this is empty only
-- | where nothing is running. At quiescence a job here would be one the loop
-- | never reaches and no report names.
unwakeable :: Scheduler -> P.Array PendingId
unwakeable s = do
  Tuple id p <- Map.toUnfoldable s.pending
  if Set.isEmpty p.awaiting && not (Array.elem id (readyIds s)) then [ id ] else []

-- | Both directions of the registration equivalence are walked. The table and
-- | the set each name what the other is read through, so a check of one
-- | direction alone passes a job that waits on a metavariable it is registered
-- | under nowhere, and that assignment never reaches it.
invariants :: Scheduler -> P.Array Invariant
invariants s =
  Array.concat
    [ registrations
    , awaited
    , readyEntries
    , duplicates
    ]
  where
  ready = readyIds s

  registrations = do
    Tuple m ids <- Map.toUnfoldable s.blocked
    id <- Set.toUnfoldable ids
    case Map.lookup id s.pending of
      Nothing -> [ UnknownPending id ]
      Just p
        | not (Set.member m p.awaiting) -> [ RegistrationDiffers m id ]
        | Array.elem id ready -> [ ReadyAndBlocked id ]
        | otherwise -> []

  awaited = do
    Tuple id p <- Map.toUnfoldable s.pending
    m <- Set.toUnfoldable p.awaiting
    if Set.member id (blockedOn s m) then [] else [ RegistrationDiffers m id ]

  readyEntries = do
    id <- ready
    case Map.lookup id s.pending of
      Nothing -> [ UnknownPending id ]
      Just p
        | not (Set.isEmpty p.awaiting) -> [ AwaitingWhileReady id ]
        | otherwise -> []

  duplicates =
    map DuplicateOnReady
      (Array.nub (Array.filter (\id -> Array.length (Array.filter (_ == id) ready) > 1) ready))

register :: PendingId -> MetaVar -> Map MetaVar (Set PendingId) -> Map MetaVar (Set PendingId)
register id m blocked =
  Map.insertWith Set.union m (Set.singleton id) blocked

-- | An entry that becomes empty is deleted, so that the domain of the table is
-- | the metavariables something is actually waiting on.
unregister :: PendingId -> MetaVar -> Map MetaVar (Set PendingId) -> Map MetaVar (Set PendingId)
unregister id m blocked = case Map.lookup m blocked of
  Nothing -> blocked
  Just ids ->
    let
      rest = Set.delete id ids
    in
      if Set.isEmpty rest then Map.delete m blocked else Map.insert m rest blocked

derive instance Eq Phase
derive instance Generic Phase _

instance Show Phase where
  show x = genericShow x

derive instance Eq Invariant
derive instance Generic Invariant _

instance Show Invariant where
  show x = genericShow x
