-- | The Middle-end IR.
-- |
-- | Mid IR is an A-normal form: every intermediate result is named by a
-- | binding, every argument is an atom, and every control construct stands in
-- | tail position. It has no nested function — a lambda, the body of a
-- | `handle` or of a `region`, and every handler clause is an entry of the
-- | module's function table, over an explicit capture list.
-- |
-- | Types are gone. What survives of them is a `Rep` on each binding.
module Stella.Compiler.MiddleEnd.IR
  ( Local(..)
  , JoinId(..)
  , FuncId(..)
  , Binder
  , Atom(..)
  , Callee(..)
  , Comp(..)
  , Expr(..)
  , CtorBranch
  , LitBranch
  , KeyBranch
  , Handler
  , ClauseRef
  , ClauseForm(..)
  , OpClauseRef
  , Function
  , RecBinding
  , CtorEntry
  , EffectEntry
  , ForeignEntry
  , GlobalInit(..)
  , GlobalEntry
  , Module
  , Debug
  , FunctionDebug
  , emptyDebug
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Primitive (PrimOp)
import Stella.Compiler.MiddleEnd.Rep (Rep)
import Stella.Compiler.TypedCore.Name (EffName, Ident, ModuleName, OpName, Qualified, TyName)
import Stella.Compiler.TypedCore.Term (Literal)
import Stella.Compiler.TypedCore.Type (RowKey)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)

-- | A binding within one function. Locals are unique within a function rather
-- | than globally, so a backend may lay a function's out as a flat frame.
newtype Local = Local P.Int

-- | A join point, unique within the function that binds it.
newtype JoinId = JoinId P.Int

-- | An entry of the module's function table.
newtype FuncId = FuncId P.Int

type Binder =
  { local :: Local
  , rep :: Rep
  }

-- | A value denoted without computing, allocating, or performing anything.
data Atom
  = ALocal Local
  | ALit Literal
  -- | A top-level value, read from where initialization stored it. **A foreign
  -- | is never an atom**: one of arity 0 calls its implementation as soon as
  -- | its spine is formed, and one of greater arity is a partial application.
  | AGlobal (Qualified Ident)
  -- | A saturated constructor of arity 0, which allocates nothing new.
  | ACtor (Qualified Ident)

-- | What a partial application is waiting to become.
-- |
-- | **An operation stays an operation through a partial application.** A callee
-- | naming the foreign instead would leave a consumer recognizing a qualified
-- | name to find out what saturating it runs, which is what naming the operation
-- | exists to avoid, and would leave the use unrecorded.
data Callee
  = CalleeValue (Qualified Ident)
  | CalleeForeign (Qualified Ident)
  | CalleeCtor (Qualified Ident)
  | CalleePrim PrimOp

-- | A computation, bound by a `let` or standing in tail position. The only
-- | place an effect, an allocation, or a call occurs.
data Comp
  = CPure Atom
  -- | A call to a top-level value whose definitional arity the arguments match.
  | CCallKnown (Qualified Ident) (P.Array Atom)
  -- | A call whose callee is not known statically. Under- and over-application
  -- | are resolved here.
  | CCallUnknown Atom (P.Array Atom)
  -- | A saturated `Base` ABI operation, which the ABI fixes the meaning of. A
  -- | consumer carries one out directly rather than calling an implementation a
  -- | backend supplied. **May fault**: which entries do is the ABI
  -- | specification's to say.
  | CPrim PrimOp (P.Array Atom)
  -- | A saturated foreign: an implementation a backend supplies, named. **May
  -- | fault.**
  | CForeign (Qualified Ident) (P.Array Atom)
  | CCtor (Qualified Ident) (P.Array Atom)
  -- | Fewer arguments than the callee's arity. The result is a value.
  | CPap Callee (P.Array Atom)
  | CClosure FuncId (P.Array Atom)
  | CField Atom (Qualified Ident) P.Int
  | CPayload RowKey Atom
  | CRecordEmpty
  | CRecordExtend RowKey Atom Atom
  | CRecordSelect RowKey Atom
  | CRecordRestrict RowKey Atom
  -- | The record first and the value second, as Core writes it. `CRecordExtend`
  -- | writes them the other way about.
  | CRecordUpdate RowKey Atom Atom
  | CRecordMerge Atom Atom
  | CInject RowKey Atom
  | CAbsurd Atom
  | CPerform RowKey OpName Atom
  -- | Install a handler and call the body, which is a function of no
  -- | parameters, over the captures given. The value is what the return clause
  -- | produces, so a `let` binds it like any other computation.
  | CHandle Handler FuncId (P.Array Atom)
  -- | Open a region of cells and call the body, a function of one parameter,
  -- | with the region's **identity**: a value telling this opening of the
  -- | region from every other, the copies a continuation makes of it aside.
  -- | The value is the body's.
  -- |
  -- | The keys are the region's layout in the order it is written, which is what
  -- | positions the cells; they say nothing a read or a write uses. The first
  -- | array is what the body captures and the second the initial value of each
  -- | cell, in the same order. **The two are separate because they are neither
  -- | the same values nor evaluated at the same time**: a capture list holds what
  -- | the body names, and the initial values are evaluated before the region
  -- | opens.
  | CRegion (P.Array RowKey) FuncId (P.Array Atom) (P.Array Atom)
  -- | The cell at that position of the region whose identity the atom holds.
  -- | The identity is an ordinary value, so a function using a region's cells
  -- | captures it like any other.
  | CReadCell Atom P.Int
  -- | Replace what that cell holds. The value is `Prim.Unit`, a write being done
  -- | for its effect on the region rather than for a result of its own.
  | CWriteCell Atom P.Int Atom

-- | The body of a function, of a join point, or of a branch.
data Expr
  = ERet Atom
  | ELet Local Rep Comp Expr
  -- | A group of closures that may capture one another. Every closure of the
  -- | group is allocated before any capture list is filled, which guardedness
  -- | (D14) is what makes safe.
  | ELetRec (P.Array RecBinding) Expr
  | ELetJoin JoinId (P.Array Binder) Expr Expr
  | EJump JoinId (P.Array Atom)
  -- | A computation in tail position, which a backend reads as an obligation to
  -- | transfer control rather than to push a frame.
  -- |
  -- | It carries no `Rep`. A call returns its value rather than binding one and
  -- | wants none; a computation that is not a call takes a register on the way to
  -- | returning, and the class of that register is unknown for want of one here.
  | ETail Comp
  | ESwitchCtor Atom (P.Array CtorBranch) (Maybe Expr)
  -- | Literals cannot be exhausted, so the default is not optional.
  | ESwitchLit Atom (P.Array LitBranch) Expr
  | ESwitchKey Atom (P.Array KeyBranch) (Maybe Expr)
  | EIf Atom Expr Expr

type RecBinding =
  { local :: Local
  , rep :: Rep
  , func :: FuncId
  , captures :: P.Array Atom
  }

type CtorBranch =
  { ctor :: Qualified Ident
  , body :: Expr
  }

type LitBranch =
  { lit :: Literal
  , body :: Expr
  }

type KeyBranch =
  { key :: RowKey
  , body :: Expr
  }

-- | A handler carries the key of the element it removes and nothing else of
-- | that element: typing needed the payload to say which operations the clauses
-- | exhaust, and that is settled before this stage.
type Handler =
  { key :: RowKey
  , returnClause :: ClauseRef
  , opClauses :: P.Array OpClauseRef
  }

type ClauseRef =
  { func :: FuncId
  , captures :: P.Array Atom
  }

-- | Which reduction a clause takes, written on every clause as Core writes it
-- | (D28). A `fast` clause constructs no continuation, so a backend lowers the
-- | two differently.
data ClauseForm
  = ClauseFull
  | ClauseFast

type OpClauseRef =
  { op :: OpName
  , form :: ClauseForm
  , clause :: ClauseRef
  }

type Function =
  { id :: FuncId
  , params :: P.Array Binder
  , captures :: P.Array Binder
  , body :: Expr
  }

-- | What survives of a data declaration. `isNewtype` is carried because nothing
-- | else recovers it: a `newtype` and a data type of one constructor with one
-- | field have the same shape here.
type CtorEntry =
  { ref :: Qualified Ident
  , owner :: Qualified TyName
  , tag :: P.Int
  , arity :: P.Int
  , isNewtype :: P.Boolean
  }

type EffectEntry =
  { ref :: Qualified EffName
  , ops :: P.Array OpName
  }

type ForeignEntry =
  { ref :: Qualified Ident
  , arity :: P.Int
  }

-- | How initialization installs a top-level value, which **the shape of the
-- | right-hand side decides and not the form of the declaration**.
data GlobalInit
  -- | A right-hand side that is not a lambda: evaluate a function of no
  -- | parameters once and store the result. Evaluating eagerly in declaration
  -- | order is observable.
  = GRun FuncId
  -- | A right-hand side that is a lambda once erasure has looked through the
  -- | wrappers: install a closure over an empty capture list, evaluating
  -- | nothing. At the top level every free name is a global, so there is
  -- | nothing to capture.
  -- |
  -- | This is the same test the definitional arity is read by, so a global a
  -- | `callk` reaches holds a function of the arity that call supplied.
  | GFunc FuncId

type GlobalEntry =
  { ref :: Qualified Ident
  , init :: GlobalInit
  }

-- | `globals` is in the dependency order Core required of value declarations,
-- | preserved rather than recomputed.
type Module =
  { name :: ModuleName
  , imports :: P.Array ModuleName
  , ctors :: P.Array CtorEntry
  , effects :: P.Array EffectEntry
  , foreigns :: P.Array ForeignEntry
  , functions :: P.Array Function
  , globals :: P.Array GlobalEntry
  , exports :: P.Array (Qualified Ident)
  }

-- | What a `.dmo` fills its `DEBUG` section from, and the one part of Mid IR a
-- | consumer may discard.
-- |
-- | It is a **side table** rather than an annotation on the terms. A Mid IR node
-- | has no identity of its own, and most nodes come from no single Core node —
-- | one application folds a whole spine, and a projection is emitted where a
-- | branch first needs it. What does have an identity is a function and a local,
-- | and those are what can be named.
-- |
-- | A span finer than a function therefore has nowhere to go. Giving Mid IR
-- | nodes identities would be what a source map at instruction granularity
-- | needs, and nothing here provides one.
type Debug ann =
  { functions :: Map FuncId (FunctionDebug ann)
  -- | The Core name a local was created for, where it had one, **per function**.
  -- | A `Local` is unique within a function and not beyond one, so nothing but a
  -- | function and a local together identifies a binding.
  -- |
  -- | A local holding an intermediate result of a spine, a projection no
  -- | pattern gave a name to, or a region's identity was created for no name
  -- | and appears in neither map.
  , locals :: Map FuncId (Map Local Ident)
  }

type FunctionDebug ann =
  -- | The global this function defines, where it defines one. A lambda lifted
  -- | out of a body defines none.
  { name :: Maybe (Qualified Ident)
  , source :: Maybe ann
  }

emptyDebug :: forall ann. Debug ann
emptyDebug = { functions: Map.empty, locals: Map.empty }

derive instance Eq Local
derive instance Ord Local
derive newtype instance Show Local

derive instance Eq JoinId
derive instance Ord JoinId
derive newtype instance Show JoinId

derive instance Eq FuncId
derive instance Ord FuncId
derive newtype instance Show FuncId

derive instance Eq Atom
derive instance Generic Atom _

instance Show Atom where
  show x = genericShow x

derive instance Eq Callee
derive instance Generic Callee _

instance Show Callee where
  show x = genericShow x

derive instance Eq ClauseForm
derive instance Ord ClauseForm
derive instance Generic ClauseForm _

instance Show ClauseForm where
  show = genericShow

derive instance Eq Comp
derive instance Generic Comp _

instance Show Comp where
  show x = genericShow x

derive instance Eq Expr
derive instance Generic Expr _

instance Show Expr where
  show x = genericShow x

derive instance Eq GlobalInit
derive instance Generic GlobalInit _

instance Show GlobalInit where
  show = genericShow
