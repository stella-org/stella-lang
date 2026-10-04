-- | The global signature `Σ`.
-- |
-- | `Σ` is an unordered table of declarations, assembled from a module and from
-- | the interfaces of the modules it imports and fixed throughout the checking
-- | of that module. The rules only look things up in it, never extend or shrink
-- | it, which is why the judgements leave it implicit.
-- |
-- | Every name in it is fully qualified. `Σ` is also what separates the two row
-- | key kinds: a structural key needs nothing from it, while an `EffectKey` is
-- | the identity of a declaration recorded here.
module Stella.Compiler.TypedCore.Signature
  ( Signature
  , TyConInfo(..)
  , CanonicalClass(..)
  , CtorInfo
  , EffectInfo
  , ValueInfo
  , AttributeInfo
  , emptySignature
  , tyConKind
  , lookupTyCon
  , lookupCtor
  , lookupEffect
  , lookupOperation
  , lookupValue
  , lookupAttribute
  , effectParamKinds
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Decl (KeywordParameter, OpDecl)
import Stella.Compiler.TypedCore.Kind (Kind, KindScheme)
import Stella.Compiler.TypedCore.Name (EffName, Ident, OpName, Qualified, TyName)
import Stella.Compiler.TypedCore.Type (TyBinder, Type, TypeScheme)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)

type Signature =
  { types :: Map (Qualified TyName) TyConInfo
  , ctors :: Map (Qualified Ident) CtorInfo
  , effects :: Map (Qualified EffName) EffectInfo
  , values :: Map (Qualified Ident) ValueInfo
  , attributes :: Map (Qualified Ident) AttributeInfo
  }

-- | A type constructor entry, which is a data entry or an intrinsic one.
-- |
-- | The distinction is load-bearing rather than descriptive: `switchCtor` takes
-- | a data value apart, and a type with no constructors would exhaust
-- | vacuously, so a `switchCtor` over an intrinsic type must be ill-formed
-- | rather than trivially total.
data TyConInfo
  -- | The constructors the declaration gives it, as it lists them. Nothing
  -- | reads an order from this: what a rule asks of it is which constructors
  -- | there are, and a tag is carried by the entry of each.
  = DataTyCon KindScheme (P.Array (Qualified Ident))
  -- | No data constructors whatever. No declaration produces one of these: an
  -- | intrinsic reaches `Σ` with `Prim` or through the manifest of the
  -- | primitive surface.
  | IntrinsicTyCon KindScheme CanonicalClass

-- | How a value of an intrinsic type is built, and what may examine one.
data CanonicalClass
  = CanonicalLiteral
  | CanonicalFunction
  | CanonicalRecord
  | CanonicalVariant
  -- | Core has no rule that compares or decomposes one. It travels from the
  -- | `foreign` that produced it to the `foreign` that consumes it.
  | CanonicalOpaque

-- | A data constructor as `Σ` records it. The arity is the number of fields.
-- |
-- | `params` are the type parameters of the owning declaration, which
-- | `fields` are written in terms of: taking a constructor's value apart
-- | instantiates them from the type of the occurrence.
type CtorInfo =
  { owner :: Qualified TyName
  , tag :: P.Int
  , params :: P.Array TyBinder
  , fields :: P.Array Type
  , scheme :: TypeScheme
  }

-- | An effect declaration as the rules read it.
-- |
-- | An effect constructor carries no kind scheme: its kind is `κ̄ -> Effect`,
-- | fixed by `params`, so an element of a `Row Effect` is written `E τ̄` and
-- | needs no instantiation.
type EffectInfo =
  { params :: P.Array TyBinder
  , operations :: Map OpName OpDecl
  }

-- | A top-level value or a foreign. Typing treats the two alike; which one it
-- | is decides whether evaluation unfolds a definition or calls an
-- | implementation.
type ValueInfo =
  { scheme :: TypeScheme
  , isForeign :: P.Boolean
  }

-- | An attribute declaration as the rules read it: its parameter types, closed,
-- | and its keyword parameters with their defaults.
type AttributeInfo =
  { positional :: P.Array Type
  , keyword :: P.Array KeywordParameter
  }

emptySignature :: Signature
emptySignature =
  { types: Map.empty
  , ctors: Map.empty
  , effects: Map.empty
  , values: Map.empty
  , attributes: Map.empty
  }

tyConKind :: TyConInfo -> KindScheme
tyConKind = case _ of
  DataTyCon kind _ -> kind
  IntrinsicTyCon kind _ -> kind

lookupTyCon :: Signature -> Qualified TyName -> Maybe TyConInfo
lookupTyCon sig name = Map.lookup name sig.types

lookupCtor :: Signature -> Qualified Ident -> Maybe CtorInfo
lookupCtor sig name = Map.lookup name sig.ctors

lookupEffect :: Signature -> Qualified EffName -> Maybe EffectInfo
lookupEffect sig name = Map.lookup name sig.effects

-- | The signature a `perform` reads its operation from. The key of the row
-- | element leads to the effect; the effect leads here.
lookupOperation :: Signature -> Qualified EffName -> OpName -> Maybe OpDecl
lookupOperation sig name op = case lookupEffect sig name of
  Nothing -> Nothing
  Just info -> Map.lookup op info.operations

lookupValue :: Signature -> Qualified Ident -> Maybe ValueInfo
lookupValue sig name = Map.lookup name sig.values

lookupAttribute :: Signature -> Qualified Ident -> Maybe AttributeInfo
lookupAttribute sig name = Map.lookup name sig.attributes

-- | `κ̄` of `E : κ̄ -> Effect`, which is what an element's payload is checked
-- | against.
effectParamKinds :: EffectInfo -> P.Array Kind
effectParamKinds info = map _.kind info.params

derive instance Eq CanonicalClass
derive instance Ord CanonicalClass
derive instance Generic CanonicalClass _

instance Show CanonicalClass where
  show = genericShow

derive instance Eq TyConInfo
derive instance Generic TyConInfo _

instance Show TyConInfo where
  show x = genericShow x
