-- | The scheme of a declaration as an interface carries it: its Core scheme,
-- | with what the surface says beyond Core kept on its spine.
-- |
-- | Two things a surface signature says are gone from its Core scheme. A
-- | synthesized argument, `{{ d :: C τ̄ by f }}`, is an ordinary parameter of
-- | the dictionary's type in Core (D11), and a module importing the declaration
-- | needs to know that a goal fills it. A computation, `τ / ρ`, is a thunk
-- | `Unit -{ρ}-> τ` in Core, and a reference to it is forced where it stands
-- | (proposal 05). Both stand on the spine of a scheme, under its quantifiers and
-- | constraints, so the spine is where this type differs from Core's and
-- | everything below it is a Core type.
-- |
-- | **The Core scheme is derived, never stored beside it**, so the two cannot
-- | disagree. A type synonym the scheme mentions is expanded.
module Stella.Compiler.Interface.Scheme
  ( Scheme
  , SchemeBody(..)
  , SynthesizedParameter
  , plainScheme
  , plainBody
  , coreScheme
  , coreBody
  ) where

import Prelude
import Prim hiding (Type, Constraint)

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Stella.Compiler.TypedCore.Kind (Kind, Scheme) as K
import Stella.Compiler.TypedCore.Name (Ident, Qualified, TyVar)
import Stella.Compiler.TypedCore.Prim (fn, pureFn, unitTy)
import Stella.Compiler.TypedCore.Type (Constraint, Type(..), TypeScheme)

-- | A scheme over its kind variables, which a reference instantiates
-- | explicitly (D3).
type Scheme = K.Scheme SchemeBody

-- | The spine of a scheme.
-- |
-- | **A `Plain` type is not headed by a `forall` or a constraint**: the spine
-- | takes every quantifier and constraint in front of it, so one scheme has one
-- | spine.
data SchemeBody
  -- | The rest of the spine, holding nothing the surface says beyond Core.
  = Plain Type
  -- | `τ / ρ`, the type a computation produces and the row it performs.
  | Computation Type Type
  | Forall TyVar K.Kind SchemeBody
  | Constrained Constraint SchemeBody
  -- | `{{ d :: C τ̄ by f }} -> σ`, a parameter a synthesis goal fills, behind a
  -- | pure arrow.
  | Synthesized SynthesizedParameter SchemeBody

-- | A synthesized argument: the name written for it, which binds nothing, the
-- | type of the dictionary it is, and the synthesizer that fills it.
type SynthesizedParameter =
  { name :: Maybe Ident
  , dictionary :: Type
  , synthesizer :: Qualified Ident
  }

-- | The scheme of a declaration whose signature says nothing beyond Core.
plainScheme :: TypeScheme -> Scheme
plainScheme s = { kindVars: s.kindVars, body: plainBody s.body }

-- | A Core type as a spine, its quantifiers and constraints taken onto it.
plainBody :: Type -> SchemeBody
plainBody = case _ of
  TForall a k body -> Forall a k (plainBody body)
  TConstrained c body -> Constrained c (plainBody body)
  t -> Plain t

coreScheme :: Scheme -> TypeScheme
coreScheme s = { kindVars: s.kindVars, body: coreBody s.body }

-- | The Core type a spine stands for: a computation is a thunk, and a
-- | synthesized argument an ordinary parameter of the dictionary's type.
coreBody :: SchemeBody -> Type
coreBody = case _ of
  Plain t -> t
  Computation result row -> fn (TCon unitTy []) row result
  Forall a k body -> TForall a k (coreBody body)
  Constrained c body -> TConstrained c (coreBody body)
  Synthesized p body -> pureFn p.dictionary (coreBody body)

derive instance Eq SchemeBody
derive instance Generic SchemeBody _

instance Show SchemeBody where
  show x = genericShow x
