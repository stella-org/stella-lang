-- | A pending job: the envelope every postponable thing shares, and the job
-- | inside it.
-- |
-- | Scheduling, the site, the dependency set, and the transaction are the same
-- | machinery whichever job is inside, which is why the envelope is one record
-- | and the job is a sum.
module Stella.Compiler.Elaborate.Pending
  ( PendingId(..)
  , Site
  , EqualityGoal
  , Job(..)
  , Pending
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Context (Origin, XContext)
import Stella.Compiler.Elaborate.Kind (XKind)
import Stella.Compiler.Elaborate.Type (MetaVar, XType)

import Data.Generic.Rep (class Generic)
import Data.Set (Set)
import Data.Show.Generic (genericShow)

-- | What the blocked table registers.
-- |
-- | Registering the identifier rather than the job is what lets a wake remove
-- | every entry one job has: two entries holding the job itself would have to be
-- | recognized as one.
newtype PendingId = PendingId P.Int

-- | What a job is decided against, which the three kinds take different things
-- | from.
-- |
-- | **What an equality takes is the kind variables in scope where it was written**
-- | — a kind metavariable created while solving it may mention those and no
-- | others — and the place a failure is reported. One woken far from where it was
-- | written, creating a kind metavariable under whatever elaboration has since
-- | reached, would admit a kind variable that is out of scope at the equation or
-- | refuse one that is in it.
-- |
-- | **What a substitution must preserve is decided elsewhere.** The row
-- | constraints naming a metavariable are obligations, each holding on the
-- | assumptions of the site **it** came from — several different sites, in
-- | general, and not necessarily the one the equation stands at
-- | ([Obligation](Obligation.purs)).
type Site =
  { context :: XContext
  , origin :: Origin
  }

-- | `Γ ; κ ⊢ τ1 ≡ τ2` postponed, with the kind both sides stand at.
-- |
-- | A row equality is one of these at a row kind, its payload equations being
-- | discharged by type unification. A kind equality is never one: kind equality
-- | is syntactic (D2), so it is decided where it is met and has nothing to wait
-- | for.
type EqualityGoal =
  { kind :: XKind
  , left :: XType
  , right :: XType
  }

data Job = JobUnify EqualityGoal

-- | `awaiting` is the metavariables the job last postponed on.
-- |
-- | It is assigned and never accumulated: a second postponement names whatever
-- | set it names then, which need not contain what the job waited on before.
-- | Waking reads it to remove the job from every metavariable it was registered
-- | under, then empties it, so that a report at quiescence names what is still
-- | being waited on.
type Pending =
  { id :: PendingId
  , site :: Site
  , awaiting :: Set MetaVar
  , job :: Job
  }

derive instance Eq PendingId
derive instance Ord PendingId
derive newtype instance Show PendingId

derive instance Eq Job
derive instance Generic Job _

instance Show Job where
  show x = genericShow x
