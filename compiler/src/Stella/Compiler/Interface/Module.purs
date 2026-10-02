-- | What one module contributes to the build environment once it is compiled:
-- | what name resolution and elaboration in a module downstream read of it, and
-- | what an optimizer downstream reads of it
-- | ([Modules](../../../../docs/technical-references/06-Modules/01-Modules.md)).
-- |
-- | **Names and entities are held apart.** The export tables say which names
-- | the module publishes and what each is another name for, an entity
-- | qualified by the module declaring it; what an entity is — its scheme, its
-- | constructors, its attributes — is held by the declaring module's interface
-- | alone, in its declarations. A module re-exporting a name therefore holds
-- | the name and the way it came, and nothing of the entity.
-- |
-- | **The declarations are every top-level declaration of the module**, not
-- | only those it exports: an exported scheme may mention a type the module
-- | keeps abstract or unexported, and Core refers to an entry published to the
-- | catalog alone. Which names source may write is the export tables' to say.
module Stella.Compiler.Interface.Module
  ( ModuleInterface
  , Exports
  , Export
  , TypeExport
  , TypeEntity(..)
  , Via(..)
  , Declarations
  , ValueEntry
  , ValueSort(..)
  , TypeEntry
  , TypeSort(..)
  , ConstructorEntry
  , EffectEntry
  , OperationEntry
  , OperatorEntry
  , AttributeEntry
  , KeywordParameterEntry
  , Attribute
  , Constant(..)
  , ImplicitHandler
  , ForeignSummary
  , emptyExports
  , emptyDeclarations
  , isComputation
  , foreignSummary
  , dmiOf
  ) where

import Prelude
import Prim hiding (Type, Symbol)

import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Show.Generic (genericShow)
import Stella.Compiler.Interface (Dmi)
import Stella.Compiler.Interface.Scheme (Scheme, SchemeBody(..), coreBody)
import Stella.Compiler.Surface.Decl (Associativity, FixityTarget, Observation)
import Stella.Compiler.Surface.Name (OperatorName)
import Stella.Compiler.TypedCore.Kind (KindScheme)
import Stella.Compiler.TypedCore.Name (EffName, Ident(..), ModuleName, Qualified(..), Symbol, TyName)
import Stella.Compiler.TypedCore.Prim (asFunction, ioTy)
import Stella.Compiler.TypedCore.Signature (CanonicalClass)
import Stella.Compiler.TypedCore.Term (Literal)
import Stella.Compiler.TypedCore.Type (RowEntry, TyBinder, Type(..))

type ModuleInterface =
  { name :: ModuleName
  -- | The modules its header imports, which is what its dependencies are (D22).
  , imports :: Array ModuleName
  , exports :: Exports
  , declarations :: Declarations
  -- | The implicit handlers it declares, as insertion reads them
  -- | ([Effect Handlers](../../../../docs/technical-references/02-Surface-Language/02-Effect-Handlers.md)).
  , implicitHandlers :: Array ImplicitHandler
  -- | The values published to the catalog without being exported to source: a
  -- | synthesizer finds one, and no import names one.
  , catalogOnly :: Set Ident
  -- | The definitional arity of each value it declares and exports that has
  -- | one, which is what makes a saturated call to it a `callk`. A value it
  -- | re-exports has its arity in the interface of the module declaring it.
  , arities :: Map Ident Int
  }

-- | The names a module publishes, one table per namespace, each keyed by the
-- | name as an importer writes it.
type Exports =
  { values :: Map String (Export (Qualified Ident))
  , types :: Map String TypeExport
  , operators :: Map String (Export (Qualified OperatorName))
  , macros :: Map String (Export (Qualified Ident))
  , attributes :: Map String (Export (Qualified Ident))
  -- | The modules it re-exports whole, `module N`: every name of theirs is in
  -- | the tables above as well.
  , modules :: Array ModuleName
  }

-- | A name a module publishes: the entity it is another name for, and the way
-- | it reached the module.
type Export a =
  { entity :: a
  , via :: Via
  }

-- | A type or an effect a module publishes, together with the members it
-- | publishes with it — constructors of a data type, operations of an effect —
-- | in the order they are declared. Each member is in the value table as well.
type TypeExport =
  { entity :: TypeEntity
  , via :: Via
  , members :: Array Ident
  }

-- | What a name of the type namespace is: a type, or an effect.
data TypeEntity
  = TypeEntity (Qualified TyName)
  | EffectEntity (Qualified EffName)

-- | How a published name reached the module publishing it.
data Via
  -- | The module declares it.
  = Declared
  -- | The module imports it from the module given, and re-exports it.
  | ThroughImport ModuleName

-- | Every top-level declaration of a module, by what it declares.
type Declarations =
  { values :: Map Ident ValueEntry
  , types :: Map TyName TypeEntry
  , effects :: Map EffName EffectEntry
  , operators :: Map OperatorName OperatorEntry
  , attributes :: Map Ident AttributeEntry
  }

-- | A name of the value namespace. A computation is a value whose scheme ends
-- | in `Computation`; a macro is a value carrying `Prim.macro`.
type ValueEntry =
  { sort :: ValueSort
  , scheme :: Scheme
  , attributes :: Array Attribute
  }

data ValueSort
  = SortValue
  | SortForeign Observation
  | SortHandler
  -- | A data constructor, and the type it builds.
  | SortConstructor (Qualified TyName)
  -- | An operation, and the effect declaring it.
  | SortOperation (Qualified EffName)

type TypeEntry =
  { kind :: KindScheme
  , sort :: TypeSort
  , attributes :: Array Attribute
  }

data TypeSort
  -- | A data type or a newtype, its constructors in the order of their tags.
  = DataType
      { params :: Array TyBinder
      , constructors :: Array ConstructorEntry
      , isNewtype :: Boolean
      }
  -- | A type synonym, expanded where it is used; its body mentions no synonym.
  | Synonym
      { params :: Array TyBinder
      , body :: Type
      }
  -- | `foreign type T :: κ`.
  | ForeignType
  -- | A type no declaration produces, and the canonical class of its values.
  | Intrinsic CanonicalClass

-- | A constructor, with its fields written in terms of the type's parameters.
type ConstructorEntry =
  { name :: Ident
  , fields :: Array Type
  }

type EffectEntry =
  { params :: Array TyBinder
  , operations :: Array OperationEntry
  , attributes :: Array Attribute
  }

-- | An operation as its effect declares it: its own type variables, its
-- | arguments, and the type its continuation resumes with (D21).
type OperationEntry =
  { name :: Ident
  , binders :: Array TyBinder
  , arguments :: Array Type
  , resumesWith :: Type
  }

-- | `infixl 6 add as +`: what the operator is another name for, and how it
-- | binds.
type OperatorEntry =
  { associativity :: Associativity
  , precedence :: Int
  , target :: FixityTarget
  }

-- | An attribute declaration: the types of its positional parameters and its
-- | keyword parameters, each with its default where it has one.
type AttributeEntry =
  { positional :: Array Type
  , keyword :: Array KeywordParameterEntry
  }

type KeywordParameterEntry =
  { label :: String
  , type :: Type
  , default :: Maybe Constant
  }

-- | An attribute attached to a declaration, its arguments normalized: every
-- | positional argument, and every keyword argument in the order its
-- | declaration gives them, a default standing for one left out.
type Attribute =
  { name :: Qualified Ident
  , positional :: Array Constant
  , keyword :: Array { label :: String, value :: Constant }
  }

-- | An argument of an attribute.
data Constant
  = ConstantLiteral Literal
  | ConstantValue (Qualified Ident)
  | ConstantConstructor (Qualified Ident) (Array Constant)
  | ConstantRecord (Array { label :: Symbol, value :: Constant })

-- | An implicit handler, as insertion reads it: the element it handles and the
-- | elements it performs in its place.
type ImplicitHandler =
  { handler :: Ident
  , source :: RowEntry
  , targets :: Array RowEntry
  }

-- | What an optimizer reads of a foreign
-- | ([Interface](../../../../docs/technical-references/05-Backend/03-Interface.md)).
type ForeignSummary =
  { observation :: Observation
  , returnsIO :: Boolean
  }

emptyExports :: Exports
emptyExports =
  { values: Map.empty
  , types: Map.empty
  , operators: Map.empty
  , macros: Map.empty
  , attributes: Map.empty
  , modules: []
  }

emptyDeclarations :: Declarations
emptyDeclarations =
  { values: Map.empty
  , types: Map.empty
  , effects: Map.empty
  , operators: Map.empty
  , attributes: Map.empty
  }

-- | Whether a scheme is a computation's: its spine ends in a computation type.
isComputation :: Scheme -> Boolean
isComputation s = go s.body
  where
  go = case _ of
    Computation _ _ -> true
    Forall _ _ body -> go body
    Constrained _ body -> go body
    Synthesized _ body -> go body
    Plain _ -> false

-- | The summary of a foreign entry. Whether it returns `IO` is read off the
-- | result its declared type ends in.
foreignSummary :: ValueEntry -> Maybe ForeignSummary
foreignSummary entry = case entry.sort of
  SortForeign observation -> Just { observation, returnsIO: returnsIO (coreBody entry.scheme.body) }
  _ -> Nothing
  where
  returnsIO = case _ of
    TForall _ _ body -> returnsIO body
    TConstrained _ body -> returnsIO body
    t -> case asFunction t of
      Just f -> returnsIO f.result
      Nothing -> case t of
        TApp (TCon name _) _ -> name == ioTy
        _ -> false

-- | The part of an interface a translation reads: the arity of each value the
-- | module declares and exports, under its own name. A name it re-exports is
-- | another module's, and has no entry here whatever the table holds. The
-- | interface is read as built, its export table saying which names the module
-- | declares; checking that against its declarations is not this function's.
dmiOf :: ModuleInterface -> Dmi
dmiOf i = { name: i.name, arities: Map.filterKeys ownExport i.arities }
  where
  ownExport name = case Map.lookup (unwrapIdent name) i.exports.values of
    Just { entity: Qualified m n, via: Declared } -> m == i.name && n == name
    _ -> false
  unwrapIdent (Ident s) = s

derive instance Eq TypeEntity
derive instance Ord TypeEntity
derive instance Generic TypeEntity _

instance Show TypeEntity where
  show = genericShow

derive instance Eq Via
derive instance Generic Via _

instance Show Via where
  show = genericShow

derive instance Eq ValueSort
derive instance Generic ValueSort _

instance Show ValueSort where
  show = genericShow

derive instance Eq TypeSort
derive instance Generic TypeSort _

instance Show TypeSort where
  show = genericShow

derive instance Eq Constant
derive instance Generic Constant _

instance Show Constant where
  show x = genericShow x
