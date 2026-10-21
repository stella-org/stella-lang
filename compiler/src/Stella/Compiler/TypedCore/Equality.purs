-- | The type equality decision `τ1 ≡ τ2`.
-- |
-- | Two types are equal when their canonical forms are: they are α-equivalent,
-- | their rows agree as sets of entries and of tails, and they are otherwise
-- | structurally identical. There is no β-reduction and no δ-reduction, because
-- | the type grammar has application but no abstraction (D1).
-- |
-- | Equality is total and needs no context, so it is stable under
-- | substitution: `τ1 ≡ τ2` gives `τ1[σ] ≡ τ2[σ]` whatever `σ` is. Sharpness is
-- | kinding's, not equality's. It decides; it identifies nothing. Solving
-- | `?r ≡ ?s` by constructing a substitution is unification, which belongs to
-- | elaboration.
module Stella.Compiler.TypedCore.Equality
  ( typeEquiv
  , constraintEquiv
  , schemeEquiv
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Canonical (canonical, canonicalConstraint)
import Stella.Compiler.TypedCore.Kind (Kind(..))
import Stella.Compiler.TypedCore.Name (KindVar(..))
import Stella.Compiler.TypedCore.Type (Constraint, Type, TypeScheme, substituteKindsInType)
import Data.Array as Array
import Data.Map as Map
import Data.Tuple (Tuple(..))

typeEquiv :: Type -> Type -> P.Boolean
typeEquiv t1 t2 = canonical t1 == canonical t2

-- | Constraints compare by their form: `ρ1 # ρ2` and `ρ2 # ρ1` entail each
-- | other and are distinct constraints all the same.
constraintEquiv :: Constraint -> Constraint -> P.Boolean
constraintEquiv c1 c2 = canonicalConstraint c1 == canonicalConstraint c2

-- | Scheme equality: as many kind variables bound on each side, and the bodies
-- | equal once each side's variables are renamed, in order, to one name for
-- | each position. The names renamed to are none a source writes, so no free
-- | variable of either body is captured; type variables compare up to
-- | α-equivalence, as `typeEquiv` compares them.
schemeEquiv :: TypeScheme -> TypeScheme -> P.Boolean
schemeEquiv s1 s2
  | Array.length s1.kindVars /= Array.length s2.kindVars = false
  | otherwise = typeEquiv (renamed s1) (renamed s2)
      where
      renamed s = substituteKindsInType (Map.fromFoldable (Array.mapWithIndex (\i k -> Tuple k (KVar (KindVar ("$k" <> show i)))) s.kindVars)) s.body
