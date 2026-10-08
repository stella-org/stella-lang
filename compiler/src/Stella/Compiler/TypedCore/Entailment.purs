-- | The entailment decision `Γ ⊨ C`.
-- |
-- | The conditions look for atomic facts about row variables — `k ∉ t` and
-- | `t1 # t2` — whereas assumptions concern composite rows, so each assumption
-- | is decomposed over its normal form once, into `Γ*`. The only closure added
-- | is symmetry of `#`.
-- |
-- | Deciding is comparison of normal forms plus a scan of `Γ*`. There is no
-- | search, no backtracking, and no order to depend on. The checker re-derives
-- | entailment at every `e [•]`; no proof term is carried (D5).
module Stella.Compiler.TypedCore.Entailment
  ( AtomicFacts
  , DecomposeError(..)
  , noFacts
  , decompose
  , addAssumption
  , addLacks
  , addDisjoint
  , forget
  , knownToLack
  , knownDisjoint
  , entails
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Name (TyVar)
import Stella.Compiler.TypedCore.Row (RowError, RowNormalForm, nf)
import Stella.Compiler.TypedCore.Type (Constraint(..), RowKey, Type)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, foldr)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isNothing)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | `Γ*`.
-- |
-- | `lacks` holds each `k ∉ t`, and `disjoint` each `t1 # t2` together with its
-- | mirror image, which is the whole of the closure.
type AtomicFacts =
  { lacks :: Map TyVar (Set RowKey)
  , disjoint :: Set (Tuple TyVar TyVar)
  }

-- | An assumption can be unsatisfiable on its own, which is a property of the
-- | context rather than of the constraint being decided.
data DecomposeError
  -- | `k ∉ ρ` where `ρ` is known to contain `k`.
  = LacksContradiction RowKey
  -- | `ρ1 # ρ2` where the two share a known key.
  | DisjointContradiction RowKey
  | DecomposeRowError RowError

noFacts :: AtomicFacts
noFacts = { lacks: Map.empty, disjoint: Set.empty }

-- | Build `Γ*` from the row constraints assumed in `Γ`. It is constructed once,
-- | since `Γ` is finite and each normal form is finite.
decompose :: P.Array Constraint -> Either DecomposeError AtomicFacts
decompose = foldM addAssumption noFacts

-- | Decompose one assumption over its normal form and add what it yields.
addAssumption :: AtomicFacts -> Constraint -> Either DecomposeError AtomicFacts
addAssumption facts = case _ of
  Lacks key row -> do
    n <- normalize row
    if Map.member key n.known then
      Left (LacksContradiction key)
    else
      Right (foldr (addLacks key) facts (tailOf n))

  Disjoint left right -> do
    l <- normalize left
    r <- normalize right
    case sharedKey l r of
      Just key ->
        Left (DisjointContradiction key)
      Nothing ->
        Right (withPairs (withKeysOf r l (withKeysOf l r facts)))
        where
        -- { k ∉ t | k ∈ dom(F_a), t ∈ T_b }
        withKeysOf a b acc =
          foldr (\t inner -> foldr (\key i -> addLacks key t i) inner (domainArray a)) acc (tailOf b)

        -- { t1 # t2 | t1 ∈ T1, t2 ∈ T2 }
        withPairs acc =
          foldr (\t1 inner -> foldr (addDisjoint t1) inner (tailOf r)) acc (tailOf l)

-- | `Γ ⊨ C`.
entails :: AtomicFacts -> Constraint -> Either DecomposeError P.Boolean
entails facts = case _ of
  Lacks key row -> do
    n <- normalize row
    Right (not (Map.member key n.known) && Array.all (knownToLack facts key) (tailOf n))

  Disjoint left right -> do
    l <- normalize left
    r <- normalize right
    Right
      ( isNothing (sharedKey l r)
          && Array.all (\key -> Array.all (knownToLack facts key) (tailOf r)) (domainArray l)
          && Array.all (\key -> Array.all (knownToLack facts key) (tailOf l)) (domainArray r)
          && Array.all (\t1 -> Array.all (knownDisjoint facts t1) (tailOf r)) (tailOf l)
      )

-- | `r # r` is not excluded. It is satisfiable, constraining `r` to the empty
-- | row, and an assumption entails itself. What makes `r ⊎ r` ill-kinded in an
-- | ordinary context is that nothing derives `r # r` there.
-- |
-- | Its consequence — that `r` is then empty, so `k ∉ r` and `r # s` hold of
-- | every `k` and `s` — is not derived. `Γ ⊨ C` is sound for the set-theoretic
-- | reading of rows and intentionally incomplete: the only closure `Γ*`
-- | computes is symmetry of `#`. Recording which variables are known empty
-- | would be implementable and would still decide by a scan; it is left out
-- | because it carries more of the row semantics into entailment while
-- | admitting very few further programs.
knownDisjoint :: AtomicFacts -> TyVar -> TyVar -> P.Boolean
knownDisjoint facts t1 t2 =
  Set.member (Tuple t1 t2) facts.disjoint

knownToLack :: AtomicFacts -> RowKey -> TyVar -> P.Boolean
knownToLack facts key t =
  Set.member key (fromMaybe Set.empty (Map.lookup t facts.lacks))

addLacks :: RowKey -> TyVar -> AtomicFacts -> AtomicFacts
addLacks key t facts =
  facts { lacks = Map.insertWith Set.union t (Set.singleton key) facts.lacks }

-- | Both directions are recorded here, which is the whole of the closure `Γ*`
-- | carries. Every decomposition adds its facts through this and `addLacks`, so
-- | that the closure has one implementation.
addDisjoint :: TyVar -> TyVar -> AtomicFacts -> AtomicFacts
addDisjoint t1 t2 facts =
  facts { disjoint = Set.insert (Tuple t1 t2) (Set.insert (Tuple t2 t1) facts.disjoint) }

-- | Drop every fact about a variable, which a binder of its name hides.
forget :: TyVar -> AtomicFacts -> AtomicFacts
forget t facts =
  { lacks: Map.delete t facts.lacks
  , disjoint: Set.filter (\(Tuple t1 t2) -> t1 /= t && t2 /= t) facts.disjoint
  }

sharedKey :: RowNormalForm -> RowNormalForm -> Maybe RowKey
sharedKey l r = Array.head (Array.filter (\key -> Map.member key r.known) (domainArray l))

domainArray :: RowNormalForm -> P.Array RowKey
domainArray n = Set.toUnfoldable (Set.fromFoldable (Map.keys n.known))

tailOf :: RowNormalForm -> P.Array TyVar
tailOf n = Set.toUnfoldable n.tail

normalize :: Type -> Either DecomposeError RowNormalForm
normalize row = case nf row of
  Left err -> Left (DecomposeRowError err)
  Right n -> Right n

derive instance Eq DecomposeError
derive instance Generic DecomposeError _

instance Show DecomposeError where
  show x = genericShow x
