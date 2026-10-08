-- | The `.dmo` module object.
-- |
-- | A `.dmo` is what a consumer outside this compiler reads: the lowered form,
-- | with erasure, A-normal form, spine folding, explicit closures, and disjoint
-- | decision trees already done (D34). Its sections are the module's tables and
-- | the code of its functions.
-- |
-- | This is the structured form. **Byte encoding is a separate concern**: what
-- | the container fixes is which sections there are and what each holds, and a
-- | reader of this type has all of it. Nothing here commits to a layout.
module Stella.Compiler.Bytecode.Module
  ( Constant(..)
  , Key(..)
  , CtorEntry
  , EffectEntry
  , ForeignEntry
  , CalleeEntry(..)
  , HandlerEntry
  , ClauseEntry
  , RegionEntry
  , GlobalEntry
  , GlobalInit(..)
  , Dmo
  , Debug
  , FunctionDebug
  , abiVersion
  , formatVersion
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Primitive (PrimOp)
import Stella.Compiler.Bytecode.Instr (FuncIx, Function, KeyIx, OpIx, Reg)
import Stella.Compiler.MiddleEnd.IR (ClauseForm)
import Stella.Compiler.TypedCore.Domain (ScalarString, ScalarValue, compareNumber, sameNumber)
import Stella.Compiler.TypedCore.Name (EffName, Ident, ModuleName, OpName, Qualified, Symbol, Tag, TyName)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)

-- | The version of this container's layout.
formatVersion :: P.Int
formatVersion = 0

-- | The runtime contract a module was compiled against.
abiVersion :: P.String
abiVersion = "stella-base-0.1"

-- | The literal pool. Every domain is fixed: an `Int` is a 32-bit signed
-- | integer, a `Number` is IEEE 754 binary64, a `Char` is a Unicode scalar
-- | value, and a `String` is a sequence of those (D27, D37). How a backend holds
-- | one is its own choice, which is what `Rep` leaves it.
data Constant
  = CInt P.Int
  | CNumber P.Number
  | CString ScalarString
  | CChar ScalarValue
  | CBoolean P.Boolean

-- | A row key. **Keys are compared for equality and for nothing else**, so a
-- | machine interns one on load and compares integers thereafter.
data Key
  = KSymbol Symbol
  | KTag Tag
  | KPosition P.Int
  | KEffect (Qualified EffName)

-- | `isNewtype` is carried because nothing else recovers it: a `newtype` and a
-- | data type of one constructor with one field have the same shape here.
type CtorEntry =
  { name :: Qualified Ident
  , owner :: Qualified TyName
  , tag :: P.Int
  , arity :: P.Int
  , isNewtype :: P.Boolean
  }

type EffectEntry =
  { name :: Qualified EffName
  , ops :: P.Array OpName
  }

type ForeignEntry =
  { name :: Qualified Ident
  , arity :: P.Int
  }

-- | What a partial application is waiting to become.
-- |
-- | The arity is not here: a callee may belong to another module, and a machine
-- | resolves the name against the module it comes from, which the imports name.
-- |
-- | **An operation stays an operation through a partial application**, so
-- | saturating one carries the operation out rather than calling an
-- | implementation of a name. It carries no name of its own: the `Base` entry it
-- | realizes is derived from the operation at the ABI version the header names,
-- | so an entry naming one operation and one unrelated entry is not a value this
-- | type has.
data CalleeEntry
  = CalleeValue (Qualified Ident)
  | CalleeForeign (Qualified Ident)
  | CalleeCtor (Qualified Ident)
  | CalleePrim PrimOp

-- | A handler's key, and per clause the operation and its form. The clauses'
-- | closures are supplied in registers at the instruction, so nothing here
-- | carries a capture list.
type HandlerEntry =
  { key :: KeyIx
  , opClauses :: P.Array ClauseEntry
  }

type ClauseEntry =
  { op :: OpIx
  , form :: ClauseForm
  }

-- | A region's cells, by their keys in the order the layout writes them. A cell
-- | is reached by its position, so the keys say how many cells there are and,
-- | to a reader showing the module, which is which; nothing a machine does
-- | compares them. **No region key appears here**: a region's own key is not one
-- | a term carries.
type RegionEntry =
  { cells :: P.Array KeyIx
  }

-- | How initialization installs a top-level value.
data GlobalInit
  -- | Evaluate a function of no parameters once and store the result.
  = GRun FuncIx
  -- | Install a closure over an empty capture list, evaluating nothing.
  | GFunc FuncIx

type GlobalEntry =
  { name :: Qualified Ident
  , init :: GlobalInit
  }

-- | What the `DEBUG` section holds, keyed by what a `.dmo` names things by.
-- |
-- | It is the one part a consumer may discard, and nothing else depends on it.
-- | What it holds is what translation recorded, under the indices this container
-- | names things by ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)).
type Debug ann =
  { functions :: Map FuncIx (FunctionDebug ann)
  , locals :: Map FuncIx (Map Reg Ident)
  }

type FunctionDebug ann =
  { name :: Maybe (Qualified Ident)
  , source :: Maybe ann
  }

-- | `globals` is in the dependency order Core required, and initialization runs
-- | it in that order.
-- |
-- | Nothing here is resolved against a closed set of modules: a `.dmo` names
-- | what it imports and refers to another module's globals by qualified name,
-- | which is what lets modules arrive one at a time.
type Dmo =
  { formatVersion :: P.Int
  , abiVersion :: P.String
  , name :: ModuleName
  , imports :: P.Array ModuleName
  , constants :: P.Array Constant
  , keys :: P.Array Key
  , ops :: P.Array OpName
  -- the declarations this module contributes
  , ctors :: P.Array CtorEntry
  , effects :: P.Array EffectEntry
  , foreigns :: P.Array ForeignEntry
  -- the names this module's code refers to, its own and those of the modules it
  -- imports. A reference is by qualified name, resolved where the module it
  -- belongs to is loaded
  , ctorRefs :: P.Array (Qualified Ident)
  , foreignRefs :: P.Array (Qualified Ident)
  , globalRefs :: P.Array (Qualified Ident)
  , callees :: P.Array CalleeEntry
  -- | The operations the module carries out, saturated or waiting in a partial
  -- | application. **What each realizes is derived from the ABI version**, which
  -- | the header carries, so nothing here can disagree with it — target
  -- | validation and a machine read one thing.
  , prims :: P.Array PrimOp
  , handlers :: P.Array HandlerEntry
  , regions :: P.Array RegionEntry
  , functions :: P.Array Function
  , globals :: P.Array GlobalEntry
  , exports :: P.Array (Qualified Ident)
  }

-- | Literal identity, as Core decides it (D37): a `Number` is compared by its
-- | bit pattern with all NaNs taken as one, which is not IEEE equality, so the
-- | instances are written out rather than derived
-- | ([Domain](../TypedCore/Domain.purs)).
-- |
-- | What reads them is interning: one entry of the constant pool means one
-- | literal, and a pool that merged `0.0` with `-0.0`, or held two NaNs apart,
-- | would decide a `switchLit` the module did not write.
instance Eq Constant where
  eq = case _, _ of
    CInt a, CInt b -> a == b
    CNumber a, CNumber b -> sameNumber a b
    CString a, CString b -> a == b
    CChar a, CChar b -> a == b
    CBoolean a, CBoolean b -> a == b
    _, _ -> false

instance Ord Constant where
  compare = case _, _ of
    CInt a, CInt b -> compare a b
    CNumber a, CNumber b -> compareNumber a b
    CString a, CString b -> compare a b
    CChar a, CChar b -> compare a b
    CBoolean a, CBoolean b -> compare a b
    a, b -> compare (rank a) (rank b)
    where
    rank = case _ of
      CInt _ -> 0
      CNumber _ -> 1
      CString _ -> 2
      CChar _ -> 3
      CBoolean _ -> 4

derive instance Generic Constant _

instance Show Constant where
  show = genericShow

derive instance Eq Key
derive instance Ord Key
derive instance Generic Key _

instance Show Key where
  show = genericShow

derive instance Eq CalleeEntry
derive instance Ord CalleeEntry
derive instance Generic CalleeEntry _

instance Show CalleeEntry where
  show = genericShow

derive instance Eq GlobalInit
derive instance Generic GlobalInit _

instance Show GlobalInit where
  show = genericShow
