-- | Fits: the containment `source ⊆ target` between the row a function
-- | performs and the row ambient where it is applied (D8), what `Ψ` records of
-- | one, and how one is decided
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md#fitting-an-effect-row)).
-- |
-- | **A fit is decided on the difference of its two rows**, after both are
-- | normalized, and not on their equality. The keys the two share cancel, their
-- | payloads equated, and so do the tails they share; what is left decides:
-- |
-- | ```text
-- | the source's remainder is empty:
-- |     the target's is empty too             Equal
-- |     otherwise                             Widen w, w the target's remainder
-- | a known key or a rigid tail of the source,
-- |     and no flexible tail in the target    not contained
-- | otherwise                                 waiting on the flexible tails left
-- | ```
-- |
-- | A known key or a rigid tail of the source the target cannot absorb is not
-- | contained whatever the source's own tail is: assigning a source tail only
-- | adds to the source.
module Stella.Compiler.Elaborate.Mechanism.Fit
  ( FitUse(..)
  , FitState(..)
  , FitSite
  , FitRecord
  , Remainders
  , Classified(..)
  , classify
  , sharedEntries
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin, XContext)
import Stella.Compiler.Elaborate.CorePlus.Row (XRowNormalForm, rebuild)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XRowEntry, XType)
import Stella.Compiler.TypedCore (RowKey)
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)

-- | What a fit is placed for.
data FitUse
  -- | It wraps an expression, an `EFit` holding it: a function applied, or the
  -- | outermost arrow of a checking position. Its `Widen w` becomes `openEff [w]`
  -- | around that expression.
  = Wrapping
  -- | It demands the containment alone and produces no term: a cell read or
  -- | write.
  | Demanding

-- | What is decided of a fit.
data FitState
  -- | `source ⊆ target`, waiting. `equated` are the keys the two share whose
  -- | payloads have been equated, so a key is equated once however many times
  -- | the fit is decided again.
  = Undecided { source :: XType, target :: XType, equated :: Set RowKey }
  -- | The two rows are one.
  | Equal
  -- | The target is the source and the row given besides.
  | Widen XType

-- | Where a fit was placed: the context there and the place a failure is
-- | reported.
type FitSite =
  { context :: XContext
  , origin :: Origin
  }

-- | What `Ψ` records of a fit.
type FitRecord =
  { use :: FitUse
  , site :: FitSite
  , state :: FitState
  }

-- | What is left of the two rows once what they share has cancelled.
type Remainders =
  { source :: XRowNormalForm
  , target :: XRowNormalForm
  }

-- | A fit decided against the two rows as they stand.
data Classified
  -- | Decided `Equal` or `Widen`.
  = Contained FitState
  | NotContained Remainders
  -- | Undecided, until one of the flexible tails left is assigned.
  | Waiting (Set MetaVar)

-- | Decide `source ⊆ target` over the two normal forms given, each substituted
-- | already. The keys the two share cancel here, so their payloads are the
-- | caller's to have equated ([`sharedEntries`](#v:sharedEntries)).
classify :: XRowNormalForm -> XRowNormalForm -> Classified
classify source target =
  if Map.isEmpty sourceKnown && Set.isEmpty sourceRigid && Set.isEmpty sourceFlexible then
    Contained (if Map.isEmpty targetKnown && Set.isEmpty targetRigid && Set.isEmpty targetFlexible then Equal else Widen (rebuild remainders.target))
  else if (not (Map.isEmpty sourceKnown) || not (Set.isEmpty sourceRigid)) && Set.isEmpty targetFlexible then
    NotContained remainders
  else
    Waiting (Set.union sourceFlexible targetFlexible)
  where
  sharedKeys = Set.intersection (Map.keys source.known) (Map.keys target.known)

  sourceKnown = Map.filterKeys (\k -> not (Set.member k sharedKeys)) source.known
  targetKnown = Map.filterKeys (\k -> not (Set.member k sharedKeys)) target.known
  sourceRigid = Set.difference source.rigid target.rigid
  targetRigid = Set.difference target.rigid source.rigid
  sourceFlexible = Set.difference source.flexible target.flexible
  targetFlexible = Set.difference target.flexible source.flexible

  remainders =
    { source: { known: sourceKnown, rigid: sourceRigid, flexible: sourceFlexible }
    , target: { known: targetKnown, rigid: targetRigid, flexible: targetFlexible }
    }

-- | The entries of each key the two normal forms hold, the source's first, whose
-- | payloads must be equal for the key to cancel.
sharedEntries :: XRowNormalForm -> XRowNormalForm -> P.Array { key :: RowKey, source :: XRowEntry, target :: XRowEntry }
sharedEntries source target = Array.mapMaybe entries (Set.toUnfoldable (Set.intersection (Map.keys source.known) (Map.keys target.known)))
  where
  entries key = { key, source: _, target: _ } <$> Map.lookup key source.known <*> Map.lookup key target.known

derive instance Eq FitUse
derive instance Generic FitUse _

instance Show FitUse where
  show x = genericShow x

derive instance Eq FitState
derive instance Generic FitState _

instance Show FitState where
  show x = genericShow x

derive instance Eq Classified
derive instance Generic Classified _

instance Show Classified where
  show x = genericShow x
