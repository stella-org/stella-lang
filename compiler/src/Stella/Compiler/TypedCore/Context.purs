-- | The local context `Γ`.
-- |
-- | `Γ` grows at a binder and shrinks on leaving it, and later entries may refer
-- | to earlier ones. Nothing in it crosses a module boundary and nothing in it
-- | carries a kind scheme, which is the whole of the difference between it and
-- | the global signature `Σ`.
-- |
-- | The row constraints it assumes are kept decomposed, since entailment reads
-- | atomic facts about row variables rather than the assumptions as written.
module Stella.Compiler.TypedCore.Context
  ( Context
  , emptyContext
  , bindKindVars
  , bindTyVar
  , lookupTyVar
  , bindVar
  , lookupVar
  , bindRegion
  , lookupRegion
  , kindVarInScope
  , assume
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Entailment (AtomicFacts, DecomposeError, addAssumption, addLacks, forget, noFacts)
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..))
import Stella.Compiler.TypedCore.Name (Ident, KindVar, RegionName, TyVar)
import Stella.Compiler.TypedCore.Type (Constraint, RowKey(..), Type)
import Data.Either (Either)
import Data.Foldable (foldr)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.Set (Set)
import Data.Set as Set

-- | `regions` holds the region names in scope, each with its layout: the type of
-- | every cell, by key.
type Context =
  { kindVars :: Set KindVar
  , tyVars :: Map TyVar Kind
  , vars :: Map Ident Type
  , regions :: Map RegionName (Map RowKey Type)
  , facts :: AtomicFacts
  }

emptyContext :: Context
emptyContext =
  { kindVars: Set.empty
  , tyVars: Map.empty
  , vars: Map.empty
  , regions: Map.empty
  , facts: noFacts
  }

-- | Bind the kind variables of a declaration's scheme. A kind variable enters
-- | `Γ` here and nowhere else: neither grammar has a kind quantifier (D3).
bindKindVars :: Context -> P.Array KindVar -> Context
bindKindVars ctx vars =
  ctx { kindVars = foldr Set.insert ctx.kindVars vars }

-- | Bind a type variable. A variable of the name already bound is hidden, and
-- | so is every fact assumed of it: what was assumed of the outer variable says
-- | nothing of the inner one.
bindTyVar :: Context -> TyVar -> Kind -> Context
bindTyVar ctx name kind =
  ctx { tyVars = Map.insert name kind ctx.tyVars, facts = forget name ctx.facts }

lookupTyVar :: Context -> TyVar -> Maybe Kind
lookupTyVar ctx name = Map.lookup name ctx.tyVars

bindVar :: Context -> Ident -> Type -> Context
bindVar ctx name ty =
  ctx { vars = Map.insert name ty ctx.vars }

lookupVar :: Context -> Ident -> Maybe Type
lookupVar ctx name = Map.lookup name ctx.vars

-- | Bind a region name with its layout.
-- |
-- | A row variable already in scope is bound outside the region, so whatever it
-- | is instantiated with is formed where the region is not in scope and cannot
-- | mention it. That is recorded as `RegionKey ℓ ∉ t` for every such variable of
-- | kind `Row Effect`. A row variable bound later, inside the region, gets no
-- | such fact.
bindRegion :: Context -> RegionName -> Map RowKey Type -> Context
bindRegion ctx name layout =
  ctx
    { regions = Map.insert name layout ctx.regions
    , facts = foldr (addLacks (RegionKey name)) ctx.facts effectRowVars
    }
  where
  effectRowVars = Map.keys (Map.filter (_ == KRow RowEffect) ctx.tyVars)

lookupRegion :: Context -> RegionName -> Maybe (Map RowKey Type)
lookupRegion ctx name = Map.lookup name ctx.regions

kindVarInScope :: Context -> KindVar -> P.Boolean
kindVarInScope ctx name = Set.member name ctx.kindVars

-- | Assume a row constraint.
-- |
-- | An assumption that contradicts itself is rejected here rather than carried,
-- | so what `Γ*` holds is always satisfiable.
assume :: Context -> Constraint -> Either DecomposeError Context
assume ctx constraint =
  ctx { facts = _ } <$> addAssumption ctx.facts constraint
