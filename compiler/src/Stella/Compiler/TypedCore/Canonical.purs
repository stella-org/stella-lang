-- | Canonical forms of types, which type equality compares.
-- |
-- | Canonicalization is total: it is defined on every type, well-kinded or
-- | not, and in every context. A row is canonically a set of `(key, payload)`
-- | pairs together with a set of tails, so union is set union. Equal pairs
-- | collapse, which makes `ρ ⊎ ρ` and `ρ` one row, and two pairs of one key with
-- | different payloads stay apart rather than making the form undefined.
-- | Sharpness is kinding's to establish; on a sharp row the pairs are the graph
-- | of its finite-map normal form.
-- |
-- | Being total is what makes equality stable under substitution: `r ⊎ r ≡ r`
-- | holds, and so does `( x : Int ) ⊎ ( x : Int ) ≡ ( x : Int )` that
-- | substituting `( x : Int )` for `r` makes of it.
module Stella.Compiler.TypedCore.Canonical
  ( VarRef(..)
  , Canonical(..)
  , CanonicalPayload(..)
  , CanonicalConstraint(..)
  , canonical
  , canonicalConstraint
  , canonicalPayload
  , RowParts
  , rowParts
  , occursFree
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Kind (Kind)
import Stella.Compiler.TypedCore.Name (EffName, Qualified, RegionName, TyName, TyVar)
import Stella.Compiler.TypedCore.Type (Constraint(..), RowEntry, RowKey, RowPayload(..), Type(..), rowEntryKey, rowEntryPayload)
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | A type variable seen through the binders enclosing it. A bound variable is
-- | identified by the depth of its binder, so two types that differ only in the
-- | names they bind have one canonical form.
data VarRef
  = Bound P.Int
  | Free TyVar

-- | A type in canonical form.
-- |
-- | `CRow entries tails` holds no tail that is itself a row, and is never a row
-- | of no entries and a single tail: that row is its tail, so `a ⊎ ()` and `a`
-- | are one form. Anything else standing in a tail, a type that is no row
-- | among them, is kept as an opaque tail.
data Canonical
  = CVar VarRef
  | CCon (Qualified TyName) (P.Array Kind)
  | CApp Canonical Canonical
  | CForall Kind Canonical
  | CConstrained CanonicalConstraint Canonical
  | CRow (Set (Tuple RowKey CanonicalPayload)) (Set Canonical)

data CanonicalPayload
  = CTypePayload Canonical
  | CEffectPayload (Qualified EffName) (P.Array Canonical)
  | CRegionPayload RegionName

data CanonicalConstraint
  = CLacks RowKey Canonical
  | CDisjoint Canonical Canonical

-- | The binders passed through, and the depth reached.
type Scope =
  { names :: Map TyVar P.Int
  , depth :: P.Int
  }

emptyScope :: Scope
emptyScope = { names: Map.empty, depth: 0 }

canonical :: Type -> Canonical
canonical = canonicalIn emptyScope

canonicalConstraint :: Constraint -> CanonicalConstraint
canonicalConstraint = constraintIn emptyScope

canonicalPayload :: RowPayload -> CanonicalPayload
canonicalPayload = payloadIn emptyScope

type RowParts =
  { entries :: Set (Tuple RowKey CanonicalPayload)
  , tails :: Set Canonical
  }

-- | The entries and the tails of a row, a type that is no row being a row of
-- | that one tail.
rowParts :: Canonical -> RowParts
rowParts = case _ of
  CRow entries tails -> { entries, tails }
  other -> { entries: Set.empty, tails: Set.singleton other }

-- | Whether a variable occurs free. A bound occurrence is a `Bound` level, so
-- | every `Free` occurrence is free.
occursFree :: TyVar -> Canonical -> P.Boolean
occursFree a = go
  where
  go = case _ of
    CVar ref -> ref == Free a
    CCon _ _ -> false
    CApp f x -> go f || go x
    CForall _ body -> go body
    CConstrained constraint body -> inConstraint constraint || go body
    CRow entries tails -> Array.any inEntry (Set.toUnfoldable entries) || Array.any go (Set.toUnfoldable tails)

  inConstraint = case _ of
    CLacks _ row -> go row
    CDisjoint left right -> go left || go right

  inEntry (Tuple _ payload) = case payload of
    CTypePayload ty -> go ty
    CEffectPayload _ args -> Array.any go args
    CRegionPayload _ -> false

canonicalIn :: Scope -> Type -> Canonical
canonicalIn sc = case _ of
  TVar a -> CVar (resolve sc a)
  TCon name kinds -> CCon name kinds
  TApp f x -> CApp (canonicalIn sc f) (canonicalIn sc x)
  TForall a kind body ->
    CForall kind (canonicalIn { names: Map.insert a sc.depth sc.names, depth: sc.depth + 1 } body)
  TConstrained constraint body -> CConstrained (constraintIn sc constraint) (canonicalIn sc body)
  TRowEmpty -> CRow Set.empty Set.empty
  TRowExtend entry rest ->
    union { entries: Set.singleton (entryIn sc entry), tails: Set.empty } (rowParts (canonicalIn sc rest))
  TRowUnion left right -> union (rowParts (canonicalIn sc left)) (rowParts (canonicalIn sc right))

constraintIn :: Scope -> Constraint -> CanonicalConstraint
constraintIn sc = case _ of
  Lacks key row -> CLacks key (canonicalIn sc row)
  Disjoint left right -> CDisjoint (canonicalIn sc left) (canonicalIn sc right)

payloadIn :: Scope -> RowPayload -> CanonicalPayload
payloadIn sc = case _ of
  TypePayload ty -> CTypePayload (canonicalIn sc ty)
  EffectPayload name args -> CEffectPayload name (map (canonicalIn sc) args)
  RegionPayload name -> CRegionPayload name

entryIn :: Scope -> RowEntry -> Tuple RowKey CanonicalPayload
entryIn sc entry = Tuple (rowEntryKey entry) (payloadIn sc (rowEntryPayload entry))

-- | Set union of both parts. A row of no entries and one tail is that tail.
union :: RowParts -> RowParts -> Canonical
union l r =
  let
    entries = Set.union l.entries r.entries
    tails = Set.union l.tails r.tails
  in
    case single tails of
      Just only | Set.isEmpty entries -> only
      _ -> CRow entries tails

single :: forall a. Set a -> Maybe a
single s = case Set.findMin s of
  Just a | Set.size s == 1 -> Just a
  _ -> Nothing

resolve :: Scope -> TyVar -> VarRef
resolve sc a = case Map.lookup a sc.names of
  Just level -> Bound level
  Nothing -> Free a

derive instance Eq VarRef
derive instance Ord VarRef
derive instance Generic VarRef _
instance Show VarRef where
  show x = genericShow x

derive instance Eq Canonical
derive instance Ord Canonical
derive instance Generic Canonical _
instance Show Canonical where
  show x = genericShow x

derive instance Eq CanonicalPayload
derive instance Ord CanonicalPayload
derive instance Generic CanonicalPayload _
instance Show CanonicalPayload where
  show x = genericShow x

derive instance Eq CanonicalConstraint
derive instance Ord CanonicalConstraint
derive instance Generic CanonicalConstraint _
instance Show CanonicalConstraint where
  show x = genericShow x
