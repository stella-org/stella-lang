-- | The constructors of the data types a compile-time session knows, as the
-- | occurrence typing of a decision tree reads them.
-- |
-- | A constructor field's type is read from the declaration of the data type,
-- | not recovered from the constructor's scheme: the scheme says what the
-- | constructor is as a function, and which of its arrows are fields, what data
-- | type it builds, and how that type's parameters line up with the scheme's
-- | binders are the declaration's to say. The table is built once from the
-- | signature the session's kinding comes from, and never changes.
module Stella.Compiler.Elaborate.Environment.Constructors
  ( ConstructorShape
  , ConstructorEnv
  , constructorsOf
  , emptyConstructorEnv
  , lookupConstructor
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Kind (fromCoreKind)
import Stella.Compiler.Elaborate.CorePlus.Term (XTyBinder)
import Stella.Compiler.Elaborate.CorePlus.Type (XType, fromCore)
import Stella.Compiler.TypedCore (Ident, KindVar, Qualified, TyName)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)

-- | What a constructor carries: the data type it builds, that type's kind and
-- | type parameters, and its fields in terms of them.
type ConstructorShape =
  { owner :: Qualified TyName
  , kindVars :: P.Array KindVar
  , params :: P.Array XTyBinder
  , fields :: P.Array XType
  }

type ConstructorEnv = Map (Qualified Ident) ConstructorShape

emptyConstructorEnv :: ConstructorEnv
emptyConstructorEnv = Map.empty

-- | The constructor table of a signature.
constructorsOf :: Signature -> ConstructorEnv
constructorsOf sig = map shape sig.ctors
  where
  shape info =
    { owner: info.owner
    , kindVars: info.scheme.kindVars
    , params: map (\p -> { name: p.name, kind: fromCoreKind p.kind }) info.params
    , fields: map fromCore info.fields
    }

lookupConstructor :: ConstructorEnv -> Qualified Ident -> Maybe ConstructorShape
lookupConstructor env name = Map.lookup name env

