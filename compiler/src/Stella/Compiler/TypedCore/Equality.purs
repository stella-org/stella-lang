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
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Canonical (canonical, canonicalConstraint)
import Stella.Compiler.TypedCore.Type (Constraint, Type)

typeEquiv :: Type -> Type -> P.Boolean
typeEquiv t1 t2 = canonical t1 == canonical t2

-- | Constraints compare by their form: `ρ1 # ρ2` and `ρ2 # ρ1` entail each
-- | other and are distinct constraints all the same.
constraintEquiv :: Constraint -> Constraint -> P.Boolean
constraintEquiv c1 c2 = canonicalConstraint c1 == canonicalConstraint c2
