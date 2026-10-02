-- | Declarations and modules of the Surface AST.
-- |
-- | **What stands before a declaration is part of it.** Its attributes are
-- | resolved, their arguments normalized; the one directive of this version,
-- | `#observ(none)`, is a field of a foreign declaration; and the modifier
-- | `implicit` is a field of a handler declaration. A signature is joined to the
-- | definition it gives a type to, and a kind signature to the declaration it
-- | gives a kind to.
-- |
-- | A declared name is held qualified by its module, as every reference to it
-- | is, so a declaration and a reference to it compare equal.
module Stella.Compiler.Surface.Decl
  ( Module
  , Import
  , Declaration(..)
  , declarationOrigin
  , ValueDeclaration
  , ComputationDeclaration
  , DataDeclaration
  , ConstructorDeclaration
  , NewtypeDeclaration
  , SynonymDeclaration
  , EffectDeclaration
  , OperationDeclaration
  , HandlerDeclaration
  , ForeignDeclaration
  , Observation(..)
  , ForeignTypeDeclaration
  , FixityDeclaration
  , Associativity(..)
  , FixityTarget(..)
  , AttributeDeclaration
  , KeywordParameter
  , Attribute
  , KeywordArgument
  , Constant(..)
  , constantOrigin
  ) where

import Prelude
import Prim hiding (Type, Symbol)

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Stella.Compiler.Surface.Expr (Binder, Expr, HandlerBody)
import Stella.Compiler.Surface.Name (OperatorName)
import Stella.Compiler.Surface.Origin (Origin)
import Stella.Compiler.Surface.Type (ComputationType, HandlerSignature, Kind, OperationSignature, Signature, Type, TypeVarBinder)
import Stella.Compiler.TypedCore.Name (EffName, Ident, ModuleName, Qualified, Symbol, TyName)
import Stella.Compiler.TypedCore.Term (Literal)

-- | A module, its imports being the dependencies its header declares (D22).
type Module =
  { origin :: Origin
  , name :: ModuleName
  , imports :: Array Import
  , declarations :: Array Declaration
  }

type Import =
  { origin :: Origin
  , module :: ModuleName
  }

data Declaration
  = DeclValue ValueDeclaration
  | DeclComputation ComputationDeclaration
  | DeclData DataDeclaration
  | DeclNewtype NewtypeDeclaration
  | DeclSynonym SynonymDeclaration
  | DeclEffect EffectDeclaration
  | DeclHandler HandlerDeclaration
  | DeclForeign ForeignDeclaration
  | DeclForeignType ForeignTypeDeclaration
  | DeclFixity FixityDeclaration
  | DeclAttribute AttributeDeclaration

declarationOrigin :: Declaration -> Origin
declarationOrigin = case _ of
  DeclValue d -> d.origin
  DeclComputation d -> d.origin
  DeclData d -> d.origin
  DeclNewtype d -> d.origin
  DeclSynonym d -> d.origin
  DeclEffect d -> d.origin
  DeclHandler d -> d.origin
  DeclForeign d -> d.origin
  DeclForeignType d -> d.origin
  DeclFixity d -> d.origin
  DeclAttribute d -> d.origin

-- | A value, defined by one equation over irrefutable patterns.
type ValueDeclaration =
  { origin :: Origin
  , attributes :: Array Attribute
  , name :: Qualified Ident
  , signature :: Maybe (Signature Type)
  , params :: Array Binder
  , body :: Expr
  }

-- | A computation: no parameter, an effect row, and a signature, which is what
-- | makes it one (proposal 05).
type ComputationDeclaration =
  { origin :: Origin
  , attributes :: Array Attribute
  , name :: Qualified Ident
  , signature :: Signature ComputationType
  , body :: Expr
  }

type DataDeclaration =
  { origin :: Origin
  , attributes :: Array Attribute
  , name :: Qualified TyName
  , kind :: Maybe Kind
  , params :: Array TypeVarBinder
  , constructors :: Array ConstructorDeclaration
  }

type ConstructorDeclaration =
  { origin :: Origin
  , name :: Qualified Ident
  , fields :: Array Type
  }

type NewtypeDeclaration =
  { origin :: Origin
  , attributes :: Array Attribute
  , name :: Qualified TyName
  , kind :: Maybe Kind
  , params :: Array TypeVarBinder
  , constructor :: { origin :: Origin, name :: Qualified Ident, field :: Type }
  }

type SynonymDeclaration =
  { origin :: Origin
  , attributes :: Array Attribute
  , name :: Qualified TyName
  , kind :: Maybe Kind
  , params :: Array TypeVarBinder
  , body :: Type
  }

type EffectDeclaration =
  { origin :: Origin
  , attributes :: Array Attribute
  , name :: Qualified EffName
  , params :: Array TypeVarBinder
  , operations :: Array OperationDeclaration
  }

type OperationDeclaration =
  { origin :: Origin
  , name :: Qualified Ident
  , signature :: OperationSignature
  }

-- | A handler declaration. `effect` is the effect it handles: the left of `~>`,
-- | or, for a signature written in full, the one element the thunk's row holds
-- | and the result's row does not.
type HandlerDeclaration =
  { origin :: Origin
  , attributes :: Array Attribute
  , implicit :: Boolean
  , name :: Qualified Ident
  , params :: Array Binder
  , signature :: Signature HandlerSignature
  , effect :: Qualified EffName
  , body :: HandlerBody
  }

type ForeignDeclaration =
  { origin :: Origin
  , attributes :: Array Attribute
  , observation :: Observation
  , name :: Qualified Ident
  , signature :: Signature Type
  }

-- | What a foreign declaration asserts of its observational effects (D41).
data Observation
  -- | Nothing written: the entry may observe.
  = MayObserve
  -- | `#observ(none)`.
  | ObservesNone

-- | `foreign type T :: κ` (proposal 06).
type ForeignTypeDeclaration =
  { origin :: Origin
  , attributes :: Array Attribute
  , name :: Qualified TyName
  , kind :: Kind
  }

-- | `infixl 6 add as +`.
type FixityDeclaration =
  { origin :: Origin
  , associativity :: Associativity
  , precedence :: Int
  , target :: FixityTarget
  , operator :: OperatorName
  }

data Associativity
  = AssociateNone
  | AssociateLeft
  | AssociateRight

-- | What an operator is another name for.
data FixityTarget
  = FixityValue (Qualified Ident)
  | FixityConstructor (Qualified Ident)

-- | `attribute name τ … (label :: τ = c) …`. Its parameter types are closed, so
-- | a use of it needs no instantiation.
type AttributeDeclaration =
  { origin :: Origin
  , name :: Qualified Ident
  , positional :: Array Type
  , keyword :: Array KeywordParameter
  }

type KeywordParameter =
  { origin :: Origin
  , label :: String
  , type :: Type
  , default :: Maybe Constant
  }

-- | An attribute attached to a declaration, its arguments normalized: as many
-- | positional arguments as the declaration has parameters, and every keyword
-- | argument, in the order the declaration gives its parameters, a default
-- | standing for one left out.
type Attribute =
  { origin :: Origin
  , name :: Qualified Ident
  , positional :: Array Constant
  , keyword :: Array KeywordArgument
  }

type KeywordArgument =
  { label :: String
  , value :: Constant
  }

-- | An argument of an attribute. A default carries the origin of the attribute
-- | it was filled into.
data Constant
  = ConstantLiteral Origin Literal
  -- | A global name, which is a dependency of the module.
  | ConstantValue Origin (Qualified Ident)
  -- | A constructor applied to constants.
  | ConstantConstructor Origin (Qualified Ident) (Array Constant)
  | ConstantRecord Origin (Array { label :: Symbol, value :: Constant })
  -- | Where resolution reported an error.
  | ConstantInvalid Origin

constantOrigin :: Constant -> Origin
constantOrigin = case _ of
  ConstantLiteral o _ -> o
  ConstantValue o _ -> o
  ConstantConstructor o _ _ -> o
  ConstantRecord o _ -> o
  ConstantInvalid o -> o

derive instance Eq Declaration
derive instance Generic Declaration _

instance Show Declaration where
  show = genericShow

derive instance Eq Observation
derive instance Generic Observation _

instance Show Observation where
  show = genericShow

derive instance Eq Associativity
derive instance Generic Associativity _

instance Show Associativity where
  show = genericShow

derive instance Eq FixityTarget
derive instance Generic FixityTarget _

instance Show FixityTarget where
  show = genericShow

derive instance Eq Constant
derive instance Generic Constant _

instance Show Constant where
  show x = genericShow x
