-- | The type equality decision `Γ ⊢ τ1 ≡ τ2`.
-- |
-- | Two types are equal when they are α-equivalent, their rows agree by the
-- | normal form of [Rows], and they are otherwise structurally identical. There
-- | is no β-reduction and no δ-reduction, because the type grammar has
-- | application but no abstraction (D1).
-- |
-- | This decides equality; it identifies nothing. Solving `?r ≡ ?s` by
-- | constructing a substitution is unification, which belongs to elaboration.
-- |
-- | **The domain is a pair of well-kinded types of one kind**, that is, types
-- | for which the caller has `Γ ⊢ τ1 : κ` and `Γ ⊢ τ2 : κ`. Comparing a row
-- | against a non-row is outside it and yields a `RowError`, not `false`:
-- | answering `false` would let a kinding lapse inside the checker pass for an
-- | ordinary mismatch.
module Stella.Compiler.TypedCore.Equality
  ( typeEquiv
  , rowEquiv
  , constraintEquiv
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Name (TyVar)
import Stella.Compiler.TypedCore.Row (RowError, RowNormalForm, nf)
import Stella.Compiler.TypedCore.Type (Constraint(..), RowKey, RowPayload(..), Type(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))

-- | A type variable seen through the binders enclosing it. A bound variable is
-- | identified by the depth of its binder, so two types that differ only in the
-- | names they bind resolve to the same reference.
data VarRef
  = Bound P.Int
  | Free TyVar

derive instance Eq VarRef
derive instance Ord VarRef

-- | The binders passed through on each side, and the depth reached.
type Scope =
  { left :: Map.Map TyVar P.Int
  , right :: Map.Map TyVar P.Int
  , depth :: P.Int
  }

emptyScope :: Scope
emptyScope = { left: Map.empty, right: Map.empty, depth: 0 }

bindPair :: Scope -> TyVar -> TyVar -> Scope
bindPair sc a b =
  { left: Map.insert a sc.depth sc.left
  , right: Map.insert b sc.depth sc.right
  , depth: sc.depth + 1
  }

resolve :: Map.Map TyVar P.Int -> TyVar -> VarRef
resolve env a = case Map.lookup a env of
  Just level -> Bound level
  Nothing -> Free a

typeEquiv :: Type -> Type -> Either RowError P.Boolean
typeEquiv = equiv emptyScope

-- | Row equality, which compares normal forms and never closes a row variable.
rowEquiv :: Type -> Type -> Either RowError P.Boolean
rowEquiv = rowEquivIn emptyScope

constraintEquiv :: Constraint -> Constraint -> Either RowError P.Boolean
constraintEquiv = constraintEquivIn emptyScope

equiv :: Scope -> Type -> Type -> Either RowError P.Boolean
equiv sc t1 t2
  | isRowSyntax t1 || isRowSyntax t2 = rowEquivIn sc t1 t2

equiv sc t1 t2 = case t1, t2 of
  TVar a, TVar b ->
    Right (resolve sc.left a == resolve sc.right b)

  TCon n1 kinds1, TCon n2 kinds2 ->
    Right (n1 == n2 && kinds1 == kinds2)

  TApp f1 a1, TApp f2 a2 ->
    both (equiv sc f1 f2) (equiv sc a1 a2)

  TForall a k1 body1, TForall b k2 body2
    | k1 == k2 -> equiv (bindPair sc a b) body1 body2

  TConstrained c1 body1, TConstrained c2 body2 ->
    both (constraintEquivIn sc c1 c2) (equiv sc body1 body2)

  _, _ ->
    Right false

constraintEquivIn :: Scope -> Constraint -> Constraint -> Either RowError P.Boolean
constraintEquivIn sc c1 c2 = case c1, c2 of
  Lacks k1 r1, Lacks k2 r2
    | k1 == k2 -> rowEquivIn sc r1 r2

  Disjoint a1 b1, Disjoint a2 b2 ->
    both (rowEquivIn sc a1 a2) (rowEquivIn sc b1 b2)

  _, _ ->
    Right false

rowEquivIn :: Scope -> Type -> Type -> Either RowError P.Boolean
rowEquivIn sc r1 r2 = do
  n1 <- nf r1
  n2 <- nf r2
  if tailRefs sc.left n1 /= tailRefs sc.right n2 then
    Right false
  else if domain n1 /= domain n2 then
    Right false
  else
    payloadsEquiv sc n1 n2

-- | `T`, with each variable resolved through the binders it sits under, so that
-- | a bound row variable compares by depth rather than by name.
tailRefs :: Map.Map TyVar P.Int -> RowNormalForm -> Set VarRef
tailRefs env n = Set.map (resolve env) n.tail

domain :: RowNormalForm -> Set RowKey
domain n = Set.fromFoldable (Map.keys n.known)

payloadsEquiv :: Scope -> RowNormalForm -> RowNormalForm -> Either RowError P.Boolean
payloadsEquiv sc n1 n2 =
  map (Array.all identity) (traverse compareAt (Map.toUnfoldable n1.known))
  where
  compareAt (Tuple key payload1) = case Map.lookup key n2.known of
    Nothing -> Right false
    Just payload2 -> payloadEquiv sc payload1 payload2

payloadEquiv :: Scope -> RowPayload -> RowPayload -> Either RowError P.Boolean
payloadEquiv sc p1 p2 = case p1, p2 of
  TypePayload a, TypePayload b ->
    equiv sc a b

  EffectPayload e1 as, EffectPayload e2 bs
    | e1 == e2 && Array.length as == Array.length bs ->
        map (Array.all identity) (traverse (\(Tuple a b) -> equiv sc a b) (Array.zip as bs))

  -- A region's payload is its name. No type binds a region name, so two are
  -- equal exactly when the names are (D36).
  RegionPayload r1, RegionPayload r2 ->
    Right (r1 == r2)

  _, _ ->
    Right false

both :: Either RowError P.Boolean -> Either RowError P.Boolean -> Either RowError P.Boolean
both l r = do
  a <- l
  if a then r else Right false

isRowSyntax :: Type -> P.Boolean
isRowSyntax = case _ of
  TRowEmpty -> true
  TRowExtend _ _ -> true
  TRowUnion _ _ -> true
  _ -> false
