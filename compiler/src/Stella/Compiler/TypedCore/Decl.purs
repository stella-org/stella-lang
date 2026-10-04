-- | Declarations and modules of Typed Core.
-- |
-- | Modules are namespaces (D22). `imports` records the dependencies name
-- | resolution established; since every Core name is fully qualified, it has no
-- | influence on type checking and is retained for build ordering and linking.
module Stella.Compiler.TypedCore.Decl
  ( Module
  , Export(..)
  , Decl(..)
  , declAnnotation
  , ValueBinding
  , DataDecl
  , CtorDecl
  , EffectDecl
  , OpDecl
  , ForeignDecl
  , AttributeDecl
  , KeywordParameter
  , Attribute
  , KeywordArgument
  , Constant(..)
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Name (EffName, Ident, KindVar, ModuleName, OpName, Qualified, Symbol, TyName)
import Stella.Compiler.TypedCore.Term (Expr, Literal)
import Data.Maybe (Maybe)
import Stella.Compiler.TypedCore.Type (TyBinder, Type, TypeScheme)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

type Module a =
  { annotation :: a
  , name :: ModuleName
  , imports :: P.Array ModuleName
  , exports :: P.Array Export
  , decls :: P.Array (Decl a)
  }

-- | An exported name.
-- |
-- | A type and its constructors are exported separately, so exporting the type
-- | alone yields an abstract type. This is the whole of data abstraction (D22).
data Export
  = ExportValue Ident
  | ExportType TyName
  | ExportCtor Ident
  | ExportEffect EffName

-- | A declaration.
-- |
-- | Value declarations are in dependency order: a `DeclNonRec` refers neither to
-- | itself nor to a later value declaration, and every cycle is contained in a
-- | `DeclRec` group.
-- |
-- | A declaration carries its own annotation, so that an error in a scheme, a
-- | data field, an operation signature, or a foreign type is reported at the
-- | declaration rather than at something inside it.
data Decl a
  = DeclData a DataDecl
  | DeclEffect a EffectDecl
  | DeclForeign a ForeignDecl
  | DeclNonRec a (ValueBinding a)
  | DeclRec a (P.Array (ValueBinding a))
  | DeclAttribute a AttributeDecl

declAnnotation :: forall a. Decl a -> a
declAnnotation = case _ of
  DeclData a _ -> a
  DeclEffect a _ -> a
  DeclForeign a _ -> a
  DeclNonRec a _ -> a
  DeclRec a _ -> a
  DeclAttribute a _ -> a

-- | A top-level value binding. Its right-hand side is checked at ambient effect
-- | row `()`: defining a value performs no effects.
type ValueBinding a =
  { name :: Ident
  , scheme :: TypeScheme
  , value :: Expr a
  , attributes :: P.Array Attribute
  }

-- | A data declaration.
-- |
-- | `isNewtype` tells a backend that the representation may be erased. The
-- | checker verifies the shape it claims — one constructor with one field — so
-- | the flag is not a trusted unchecked input.
type DataDecl =
  { name :: TyName
  , kindVars :: P.Array KindVar
  , params :: P.Array TyBinder
  , constructors :: P.Array CtorDecl
  , isNewtype :: P.Boolean
  , attributes :: P.Array Attribute
  }

-- | A data constructor. Its type is `forall k̄. forall (ā : κ̄). fields -> T ā`
-- | with pure arrows throughout; `tag` is unique within the type and the arity
-- | is the number of fields.
type CtorDecl =
  { name :: Ident
  , tag :: P.Int
  , fields :: P.Array Type
  }

-- | An effect declaration.
-- |
-- | An effect constructor carries no kind scheme: its kind is `κ̄ -> Effect`,
-- | binding no kind variable, so an element of a `Row Effect` is written `E τ̄`
-- | and needs no instantiation.
type EffectDecl =
  { name :: EffName
  , params :: P.Array TyBinder
  , operations :: P.Array OpDecl
  , attributes :: P.Array Attribute
  }

-- | An operation signature, `forall (b̄ : κ̄'). σ ->* τ`.
-- |
-- | An operation signature is not a function type (D21): `argument` is what the
-- | operation takes and `resumesWith` is what the continuation resumes with,
-- | and there is no functional relationship between them. A Core operation
-- | takes one argument; the surface packs several into a record.
type OpDecl =
  { name :: OpName
  , tyBinders :: P.Array TyBinder
  , argument :: Type
  , resumesWith :: Type
  }

-- | A foreign declaration. The checker trusts the declared type and never
-- | examines an implementation, but it does verify that every arrow of the type
-- | is pure (D23).
type ForeignDecl =
  { name :: Ident
  , scheme :: TypeScheme
  , attributes :: P.Array Attribute
  }

-- | An attribute declaration, `attribute name τ … (label :: τ = c) …`: the
-- | types of its positional parameters and its keyword parameters, each with its
-- | default where it has one. Every type is closed, so a use of the attribute
-- | needs no instantiation. It declares no value: no term refers to it.
type AttributeDecl =
  { name :: Ident
  , positional :: P.Array Type
  , keyword :: P.Array KeywordParameter
  }

type KeywordParameter =
  { label :: P.String
  , type :: Type
  , default :: Maybe Constant
  }

-- | An attribute attached to a declaration, its arguments normalized: as many
-- | positional arguments as its declaration has parameters, and every keyword
-- | argument in the order the declaration gives them, a default standing for
-- | one left out. What an attribute means is its reader's; the type checker
-- | confirms that each argument has the type its parameter declares.
type Attribute =
  { name :: Qualified Ident
  , positional :: P.Array Constant
  , keyword :: P.Array KeywordArgument
  }

type KeywordArgument =
  { label :: P.String
  , value :: Constant
  }

-- | An argument of an attribute: a literal, a global value, a constructor
-- | applied to constants, or a record of constants.
data Constant
  = ConstantLiteral Literal
  | ConstantValue (Qualified Ident)
  | ConstantConstructor (Qualified Ident) (P.Array Constant)
  | ConstantRecord (P.Array { label :: Symbol, value :: Constant })

derive instance Eq Export
derive instance Ord Export
derive instance Generic Export _

instance Show Export where
  show = genericShow

derive instance Eq a => Eq (Decl a)
derive instance Generic (Decl a) _

instance Show a => Show (Decl a) where
  show x = genericShow x

derive instance Eq Constant
derive instance Ord Constant
derive instance Generic Constant _

instance Show Constant where
  show x = genericShow x
