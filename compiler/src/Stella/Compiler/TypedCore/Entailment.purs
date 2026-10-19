-- | The entailment decision `Γ ⊨ C`.
-- |
-- | The conditions look for atomic facts about tails — `k ∉ t` and `t1 # t2` —
-- | whereas assumptions concern composite rows, so each assumption is
-- | decomposed over its canonical form once, into `Γ*`. The only closure added
-- | is symmetry of `#`.
-- |
-- | Deciding is comparison of canonical forms plus a scan of `Γ*`. There is no
-- | search, no backtracking, and no order to depend on. The checker re-derives
-- | entailment at every `e [•]`; no proof term is carried (D5).
-- |
-- | **An assumption may be unsatisfiable.** A type application can substitute
-- | a row into a constraint abstraction and make what it assumes false, so a
-- | context is formed whatever its assumptions. One whose assumptions are
-- | inconsistent entails every constraint. That is the only place ex falso
-- | reaches: it never makes an unbound variable bound or an ill-kinded type
-- | well-kinded, and a sharpness premise holds there because it is an
-- | entailment.
-- |
-- | **A tail is any canonical tail**, a row variable or an opaque one alike, so
-- | that decomposing and deciding treat a tail the same whatever is substituted
-- | into it, and entailment is preserved by every substitution.
module Stella.Compiler.TypedCore.Entailment
  ( AtomicFacts
  , noFacts
  , decompose
  , addAssumption
  , addLacks
  , addDisjoint
  , forget
  , unionFacts
  , knownToLack
  , knownDisjoint
  , entails
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Canonical (Canonical(..), VarRef(..), canonical, occursFree, rowParts)
import Stella.Compiler.TypedCore.Name (TyVar)
import Stella.Compiler.TypedCore.Type (Constraint(..), RowKey, Type)
import Data.Array as Array
import Data.Foldable (foldl, foldr)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..), fst)

-- | `Γ*`.
-- |
-- | `lacks` holds each `k ∉ t`, and `disjoint` each `t1 # t2` together with its
-- | mirror image, which is the whole of the closure. A tail is held in
-- | canonical form. `inconsistent` records that an assumption is
-- | unsatisfiable.
-- |
-- | Both constraints are negative, so the empty row satisfies whatever an
-- | assumption says of a row variable, and two assumptions each satisfiable on
-- | its own are satisfiable together. Inconsistency is therefore decided one
-- | assumption at a time: `k ∉ ρ` where `k` is a known key of `ρ`, and
-- | `ρ1 # ρ2` where the two share a known key. `r # r` is satisfiable, by the
-- | empty row.
type AtomicFacts =
  { lacks :: Map Canonical (Set RowKey)
  , disjoint :: Set (Tuple Canonical Canonical)
  , inconsistent :: P.Boolean
  }

noFacts :: AtomicFacts
noFacts = { lacks: Map.empty, disjoint: Set.empty, inconsistent: false }

-- | Build `Γ*` from the row constraints assumed in `Γ`. It is constructed once,
-- | since `Γ` is finite and each canonical form is finite.
decompose :: P.Array Constraint -> AtomicFacts
decompose = foldl addAssumption noFacts

-- | Decompose one assumption over its canonical form and add what it yields.
addAssumption :: AtomicFacts -> Constraint -> AtomicFacts
addAssumption facts = case _ of
  Lacks key row ->
    let
      n = partsOf row
    in
      if Set.member key n.keys then facts { inconsistent = true }
      else foldr (lacksTail key) facts n.tails

  Disjoint left right ->
    let
      l = partsOf left
      r = partsOf right
      -- { k ∉ t | k ∈ keys(a), t ∈ tails(b) }
      withKeysOf a b acc =
        foldr (\t inner -> foldr (\key i -> lacksTail key t i) inner (keysOf a)) acc b.tails
      -- { t1 # t2 | t1 ∈ tails(ρ1), t2 ∈ tails(ρ2) }
      withPairs acc =
        foldr (\t1 inner -> foldr (disjointTails t1) inner r.tails) acc l.tails
    in
      if shareKey l r then facts { inconsistent = true }
      else withPairs (withKeysOf r l (withKeysOf l r facts))

-- | `Γ ⊨ C`.
entails :: AtomicFacts -> Constraint -> P.Boolean
entails facts constraint = facts.inconsistent || case constraint of
  Lacks key row ->
    let
      n = partsOf row
    in
      not (Set.member key n.keys) && Array.all (tailLacks facts key) n.tails

  Disjoint left right ->
    let
      l = partsOf left
      r = partsOf right
    in
      not (shareKey l r)
        && Array.all (\key -> Array.all (tailLacks facts key) r.tails) (keysOf l)
        && Array.all (\key -> Array.all (tailLacks facts key) l.tails) (keysOf r)
        && Array.all (\t1 -> Array.all (tailsDisjoint facts t1) r.tails) l.tails

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
knownDisjoint facts t1 t2 = tailsDisjoint facts (variable t1) (variable t2)

knownToLack :: AtomicFacts -> RowKey -> TyVar -> P.Boolean
knownToLack facts key t = tailLacks facts key (variable t)

addLacks :: RowKey -> TyVar -> AtomicFacts -> AtomicFacts
addLacks key t = lacksTail key (variable t)

addDisjoint :: TyVar -> TyVar -> AtomicFacts -> AtomicFacts
addDisjoint t1 t2 = disjointTails (variable t1) (variable t2)

-- | Drop every fact about a tail a variable occurs free in, which a binder of
-- | its name hides. An inconsistency mentions no variable's instantiation, so
-- | it stays.
forget :: TyVar -> AtomicFacts -> AtomicFacts
forget a facts = facts
  { lacks = Map.filterKeys (not <<< occursFree a) facts.lacks
  , disjoint = Set.filter (\(Tuple t1 t2) -> not (occursFree a t1 || occursFree a t2)) facts.disjoint
  }

-- | The facts of both.
unionFacts :: AtomicFacts -> AtomicFacts -> AtomicFacts
unionFacts a b =
  { lacks: Map.unionWith Set.union a.lacks b.lacks
  , disjoint: Set.union a.disjoint b.disjoint
  , inconsistent: a.inconsistent || b.inconsistent
  }

tailLacks :: AtomicFacts -> RowKey -> Canonical -> P.Boolean
tailLacks facts key t =
  Set.member key (fromMaybe Set.empty (Map.lookup t facts.lacks))

tailsDisjoint :: AtomicFacts -> Canonical -> Canonical -> P.Boolean
tailsDisjoint facts t1 t2 =
  Set.member (Tuple t1 t2) facts.disjoint

lacksTail :: RowKey -> Canonical -> AtomicFacts -> AtomicFacts
lacksTail key t facts =
  facts { lacks = Map.insertWith Set.union t (Set.singleton key) facts.lacks }

-- | Both directions are recorded here, which is the whole of the closure `Γ*`
-- | carries. Every decomposition adds its facts through this and `lacksTail`,
-- | so that the closure has one implementation.
disjointTails :: Canonical -> Canonical -> AtomicFacts -> AtomicFacts
disjointTails t1 t2 facts =
  facts { disjoint = Set.insert (Tuple t1 t2) (Set.insert (Tuple t2 t1) facts.disjoint) }

variable :: TyVar -> Canonical
variable t = CVar (Free t)

-- | A row's known keys, and its tails.
type Parts =
  { keys :: Set RowKey
  , tails :: P.Array Canonical
  }

partsOf :: Type -> Parts
partsOf row =
  { keys: Set.map fst parts.entries
  , tails: Set.toUnfoldable parts.tails
  }
  where
  parts = rowParts (canonical row)

shareKey :: Parts -> Parts -> P.Boolean
shareKey l r = not (Set.isEmpty (Set.intersection l.keys r.keys))

keysOf :: Parts -> P.Array RowKey
keysOf n = Set.toUnfoldable n.keys
