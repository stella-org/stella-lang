-- | Kinds and types of the Surface AST.
-- |
-- | Every name is resolved: a type constructor and a type synonym are held by
-- | the qualified name of the declaration, an effect likewise, and a type
-- | variable by the binding it refers to. Parentheses are gone, the range of a
-- | node covering what they enclosed.
-- |
-- | Three forms are confined to one position each, and so are not types of
-- | their own here: a computation type `τ / ρ` stands only at the end of the
-- | spine of a computation declaration's signature (`ComputationType`), `->*` only in an
-- | operation's signature (`OperationSignature`), and `E ~> ρ` only at the end
-- | of the quantifiers of a handler's signature (`HandlerSignature`).
module Stella.Compiler.Surface.Type
  ( Kind(..)
  , kindOrigin
  , Type(..)
  , typeOrigin
  , TypeVarBinder
  , TypeOperatorTarget(..)
  , RecordRowItem(..)
  , VariantRowItem(..)
  , EffectRowItem(..)
  , EffectApplication
  , Signature
  , ComputationType
  , SignaturePrefix(..)
  , OperationSignature
  , HandlerSignature(..)
  ) where

import Prelude
import Prim hiding (Type, Symbol)

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Stella.Compiler.Surface.Name (TypeVar)
import Stella.Compiler.Surface.Origin (Origin)
import Stella.Compiler.TypedCore.Kind (RowElemKind)
import Stella.Compiler.TypedCore.Name (EffName, Ident, KindVar, Qualified, Symbol, Tag, TyName)

-- | A kind. `Type`, `Effect`, and `Row` are the words a kind is made of, and
-- | `Row` is applied to `Type` or `Effect` alone. A kind variable is bound by
-- | the declaration it appears in, implicitly and at the front (D3), so it is
-- | held by its name.
data Kind
  = KindType Origin
  | KindEffect Origin
  | KindRow Origin RowElemKind
  | KindArrow Origin Kind Kind
  | KindVariable Origin KindVar
  -- | Where resolution reported an error.
  | KindInvalid Origin

kindOrigin :: Kind -> Origin
kindOrigin = case _ of
  KindType o -> o
  KindEffect o -> o
  KindRow o _ -> o
  KindArrow o _ _ -> o
  KindVariable o _ -> o
  KindInvalid o -> o

data Type
  = TypeVariable Origin TypeVar
  -- | A data type, a newtype, a foreign type, or an intrinsic. `()` is
  -- | `Prim.Unit`.
  | TypeConstructor Origin (Qualified TyName)
  -- | A type synonym, expanded where the type is elaborated.
  | TypeSynonym Origin (Qualified TyName)
  -- | `_`, a type left for elaboration to infer.
  | TypeWildcard Origin
  -- | `?name`, a typed hole. `?_` holds `_`.
  | TypeHole Origin String
  | TypeApp Origin Type Type
  -- | A type operator applied to its two operands: the operator, then the
  -- | operands, rebracketed by fixity. The operator is the entity it names, with
  -- | the origin of where it was written; one naming an effect stands as an
  -- | effect application where a row's element does, and is held here anywhere
  -- | else, for kinding to judge.
  | TypeOperator Origin { origin :: Origin, target :: TypeOperatorTarget } Type Type
  -- | `τ1 -> τ2`, with the row `/ ρ` puts on it where one is written. An arrow
  -- | without one is pure.
  | TypeFunction Origin Type Type (Maybe Type)
  | TypeForall Origin (Array TypeVarBinder) Type
  -- | `C => τ`, where `C` is written as a type.
  | TypeConstrained Origin Type Type
  | TypeKinded Origin Type Kind
  -- | A tuple of two or more components.
  | TypeTuple Origin (Array Type)
  | TypeRecord Origin (Array RecordRowItem)
  | TypeVariant Origin (Array VariantRowItem)
  | TypeEffectRow Origin (Array EffectRowItem)
  -- | `{{ name :: τ by f }}`: the parameter a constraint desugars to, filled by
  -- | the synthesizer `f`. The name is written for the reader and binds nothing.
  | TypeSynthesized Origin (Maybe Ident) Type (Qualified Ident)
  -- | Where resolution reported an error.
  | TypeInvalid Origin

typeOrigin :: Type -> Origin
typeOrigin = case _ of
  TypeVariable o _ -> o
  TypeConstructor o _ -> o
  TypeSynonym o _ -> o
  TypeWildcard o -> o
  TypeHole o _ -> o
  TypeApp o _ _ -> o
  TypeOperator o _ _ _ -> o
  TypeFunction o _ _ _ -> o
  TypeForall o _ _ -> o
  TypeConstrained o _ _ -> o
  TypeKinded o _ _ -> o
  TypeTuple o _ -> o
  TypeRecord o _ -> o
  TypeVariant o _ -> o
  TypeEffectRow o _ -> o
  TypeSynthesized o _ _ _ -> o
  TypeInvalid o -> o

-- | What a type operator is another name for: an entity of the type namespace.
-- | Whether applying it to two operands is well kinded is decided where the
-- | application is kinded.
data TypeOperatorTarget
  = TargetTypeConstructor (Qualified TyName)
  | TargetTypeSynonym (Qualified TyName)
  | TargetEffect (Qualified EffName)

-- | A type variable a `forall` or a declaration binds, with its kind where one
-- | is written.
type TypeVarBinder =
  { origin :: Origin
  , var :: TypeVar
  , kind :: Maybe Kind
  }

-- | An item of a record's row. A spread with no operand is the anonymous one,
-- | which every anonymous spread of a signature shares per row kind.
data RecordRowItem
  = RecordField Origin Symbol Type
  | RecordSpread Origin (Maybe Type)

-- | An item of a variant's row: a tag, `'Ok :: τ`, or a label, `ok :: τ`.
data VariantRowItem
  = VariantTag Origin Tag Type
  | VariantLabel Origin Symbol Type
  | VariantSpread Origin (Maybe Type)

-- | An item of an effect row: an effect whose key is derived from it, an
-- | instance whose key is written, `cache :: State Int`, or a spread.
data EffectRowItem
  = EffectElement EffectApplication
  | EffectInstance Origin Symbol EffectApplication
  | EffectSpread Origin (Maybe Type)

-- | An effect applied to its arguments, `State Int`. The head of an element of
-- | an effect row is a declared effect (D16).
type EffectApplication =
  { origin :: Origin
  , effect :: Qualified EffName
  , arguments :: Array Type
  }

-- | A written signature together with the type variables it quantifies
-- | implicitly, outermost, which are the ones it mentions and nothing around it
-- | binds.
type Signature a =
  { implicit :: Array TypeVar
  , body :: a
  }

-- | The signature of a computation declaration, `forall ā. C => τ / ρ`: its
-- | spine — quantifiers, constraints, and synthesized arguments — in the order
-- | written, then the type of what it produces and the row it performs.
type ComputationType =
  { origin :: Origin
  , prefix :: Array SignaturePrefix
  , result :: Type
  , row :: Type
  }

data SignaturePrefix
  = PrefixForall Origin (Array TypeVarBinder)
  | PrefixConstraint Type
  -- | `{{ d :: C τ̄ by f }} ->`, behind a pure arrow: a `TypeSynthesized`, or
  -- | `TypeInvalid` where resolution reported an error.
  | PrefixSynthesized Type

-- | An operation's signature, `forall b̄. σ1 -> … -> σn ->* τ`: its own type
-- | variables, the arguments to the left of `->*`, and the type the
-- | continuation resumes with to its right. It is not a function type (D21).
type OperationSignature =
  { origin :: Origin
  , binders :: Array TypeVarBinder
  , arguments :: Array Type
  , resumesWith :: Type
  }

-- | A handler declaration's signature: the shape `forall ā. E ~> ( t̄ )` of a
-- | capability translation, with the binders of each `forall` in front of `~>`
-- | in the order written, or a type written in full.
data HandlerSignature
  = Capability
      { origin :: Origin
      , quantifiers :: Array (Array TypeVarBinder)
      , source :: EffectApplication
      , targets :: Array EffectApplication
      }
  | General Type

derive instance Eq Kind
derive instance Generic Kind _

instance Show Kind where
  show x = genericShow x

derive instance Eq Type
derive instance Generic Type _

instance Show Type where
  show x = genericShow x

derive instance Eq TypeOperatorTarget
derive instance Generic TypeOperatorTarget _

instance Show TypeOperatorTarget where
  show = genericShow

derive instance Eq RecordRowItem
derive instance Generic RecordRowItem _

instance Show RecordRowItem where
  show = genericShow

derive instance Eq VariantRowItem
derive instance Generic VariantRowItem _

instance Show VariantRowItem where
  show = genericShow

derive instance Eq EffectRowItem
derive instance Generic EffectRowItem _

instance Show EffectRowItem where
  show = genericShow

derive instance Eq SignaturePrefix
derive instance Generic SignaturePrefix _

instance Show SignaturePrefix where
  show = genericShow

derive instance Eq HandlerSignature
derive instance Generic HandlerSignature _

instance Show HandlerSignature where
  show = genericShow
