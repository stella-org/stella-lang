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
  , remaindersOf
  , sharedEntries
  , Union
  , sharedAcross
  , unionOf
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin, XContext)
import Stella.Compiler.Elaborate.CorePlus.Row (XRowNormalForm, emptyXNormalForm, rebuild)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XConstraint(..), XRowEntry, XType(..))
import Stella.Compiler.TypedCore (RowKey)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

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
  if isEmpty r.source then
    Contained (if isEmpty r.target then Equal else Widen (rebuild r.target))
  else if (not (Map.isEmpty r.source.known) || not (Set.isEmpty r.source.rigid)) && Set.isEmpty r.target.flexible then
    NotContained r
  else
    Waiting (Set.union r.source.flexible r.target.flexible)
  where
  r = remaindersOf source target

-- | What is left of each of two rows once the keys and the tails they share
-- | have cancelled.
remaindersOf :: XRowNormalForm -> XRowNormalForm -> Remainders
remaindersOf source target =
  { source: { known: Map.filterKeys (\k -> not (Set.member k shared)) source.known, rigid: Set.difference source.rigid target.rigid, flexible: Set.difference source.flexible target.flexible }
  , target: { known: Map.filterKeys (\k -> not (Set.member k shared)) target.known, rigid: Set.difference target.rigid source.rigid, flexible: Set.difference target.flexible source.flexible }
  }
  where
  shared = Set.intersection (Map.keys source.known) (Map.keys target.known)

isEmpty :: XRowNormalForm -> P.Boolean
isEmpty n = Map.isEmpty n.known && Set.isEmpty n.rigid && Set.isEmpty n.flexible

-- | The entries of each key the two normal forms hold, the source's first, whose
-- | payloads must be equal for the key to cancel.
sharedEntries :: XRowNormalForm -> XRowNormalForm -> P.Array { key :: RowKey, source :: XRowEntry, target :: XRowEntry }
sharedEntries source target = Array.mapMaybe entries (Set.toUnfoldable (Set.intersection (Map.keys source.known) (Map.keys target.known)))
  where
  entries key = { key, source: _, target: _ } <$> Map.lookup key source.known <*> Map.lookup key target.known

-- | What the compatible union of rows needs to be a row, each need with the two
-- | rows given it is between: a key of one absent from a tail of the other, and
-- | two tails of two apart.
type Union =
  { row :: XRowNormalForm
  , apart :: P.Array { between :: Tuple P.Int P.Int, constraint :: XConstraint }
  }

-- | The entries of each key two of the rows given hold, with the two rows they
-- | are of, whose payloads must be equal for the rows to have a union.
sharedAcross :: P.Array XRowNormalForm -> P.Array { between :: Tuple P.Int P.Int, key :: RowKey, first :: XRowEntry, other :: XRowEntry }
sharedAcross rows = Array.concatMap (\(Tuple i j) -> map (\e -> { between: Tuple i j, key: e.key, first: e.source, other: e.target }) (pairOf i j)) (pairs (Array.length rows))
  where
  pairOf i j = case Array.index rows i, Array.index rows j of
    Just a, Just b -> sharedEntries a b
    _, _ -> []

-- | The compatible union of the rows given, the least row holding each formed
-- | without a new decision, their shared keys equated already; or, where they
-- | hold two distinct flexible tails, those tails: that the two are apart would
-- | be a new decision.
unionOf :: P.Array XRowNormalForm -> Either (Set MetaVar) Union
unionOf rows =
  if Set.size flexible > 1 then Left flexible
  else Right { row: Array.foldl add emptyXNormalForm rows, apart: Array.concatMap needs (pairs (Array.length rows)) }
  where
  flexible = Array.foldl (\acc n -> Set.union acc n.flexible) Set.empty rows

  add acc n = { known: Map.union acc.known n.known, rigid: Set.union acc.rigid n.rigid, flexible: Set.union acc.flexible n.flexible }

  needs (Tuple i j) = case Array.index rows i, Array.index rows j of
    Just a, Just b -> map (\constraint -> { between: Tuple i j, constraint }) (lacks a b <> lacks b a <> disjoint a b)
    _, _ -> []

  -- each key of one absent from each tail of the other that does not hold it
  lacks a b =
    Array.concatMap (\key -> map (XLacks key) (only b a))
      (Array.filter (\key -> not (Map.member key b.known)) (Array.fromFoldable (Map.keys a.known)))

  -- two tails apart, where neither holds the other
  disjoint a b =
    Array.concatMap (\t -> map (XDisjoint t) (only b a)) (only a b)

  -- the tails of one the other does not hold
  only a b = Array.filter (\t -> not (Array.elem t (tailsOf b))) (tailsOf a)

  tailsOf n = map XVar (Set.toUnfoldable n.rigid) <> map XMeta (Set.toUnfoldable n.flexible)

-- | Every pair of positions below the count given, the lower first.
pairs :: P.Int -> P.Array (Tuple P.Int P.Int)
pairs n = Array.concatMap (\i -> map (Tuple i) (Array.range (i + 1) (n - 1))) (if n < 2 then [] else Array.range 0 (n - 2))

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
