-- | The effects a compile-time session knows, as a `perform` and a handler read
-- | them: each effect's type parameters, and each operation's own type binders,
-- | argument type, and the type it resumes with.
-- |
-- | The table is built once from the signature the session's kinding comes
-- | from, and never changes. An operation's types are read from its declaration
-- | rather than recovered from anything else, as a constructor's fields are.
module Stella.Compiler.Elaborate.Effects
  ( EffectShape
  , OperationShape
  , EffectEnv
  , effectsOf
  , emptyEffectEnv
  , lookupEffect
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Kind (fromCoreKind)
import Stella.Compiler.Elaborate.Term (XTyBinder)
import Stella.Compiler.Elaborate.Type (XType, fromCore)
import Stella.Compiler.TypedCore (EffName, OpName, Qualified)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)

-- | What an operation of an effect takes and gives, in terms of the effect's
-- | parameters and its own type binders.
type OperationShape =
  { tyBinders :: P.Array XTyBinder
  , argument :: XType
  , resumesWith :: XType
  }

-- | An effect's type parameters and its operations.
type EffectShape =
  { params :: P.Array XTyBinder
  , operations :: Map OpName OperationShape
  }

type EffectEnv = Map (Qualified EffName) EffectShape

emptyEffectEnv :: EffectEnv
emptyEffectEnv = Map.empty

-- | The effect table of a signature.
effectsOf :: Signature -> EffectEnv
effectsOf sig = map shape sig.effects
  where
  shape info =
    { params: map binder info.params
    , operations: map operation info.operations
    }

  operation op =
    { tyBinders: map binder op.tyBinders
    , argument: fromCore op.argument
    , resumesWith: fromCore op.resumesWith
    }

  binder b = { name: b.name, kind: fromCoreKind b.kind }

lookupEffect :: EffectEnv -> Qualified EffName -> Maybe EffectShape
lookupEffect env name = Map.lookup name env
