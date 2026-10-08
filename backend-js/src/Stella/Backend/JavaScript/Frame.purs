-- | Frame IR: the lower IR of the frame strategy.
-- |
-- | Under this strategy an activation is a frame on a stack of the runtime's own,
-- | and a Stella function is a set of **segments**: its entry, and one for what
-- | follows each non-tail call, perform, handler installation, and region opening. A segment runs
-- | straight to the next transfer and says what the run loop does next, so the
-- | host's call stack never holds more than one of them, which is how a tail call
-- | pushes nothing and a deep recursion runs in bounded host stack
-- | ([JavaScript](../../../../../docs/technical-references/05-Backend/05-JavaScript.md)).
-- |
-- | Everything a segment names is resolved already: a register is a slot of the
-- | frame, a constructor and a global are references the emitter turns into
-- | bindings, a key is its canonical string, and an operation is its name.
module Stella.Backend.JavaScript.Frame
  ( SegmentId(..)
  , GlobalRef(..)
  , CtorRef(..)
  , IOEntry(..)
  , ForeignRef(..)
  , Callee(..)
  , Target(..)
  , Literal(..)
  , Expr(..)
  , Stmt(..)
  , Block
  , Exit(..)
  , HandleOperands
  , Handler
  , OpenOperands
  , Region
  , Segment
  , FrameFunction
  ) where

import Prelude

import Prim as P

import Data.Maybe (Maybe)
import Data.Tuple (Tuple)
import Stella.Compiler.Primitive (PrimOp)
import Stella.Compiler.TypedCore.Domain (ScalarString)
import Stella.Compiler.TypedCore.Name (Ident, ModuleName)

-- | A segment, named by the function it belongs to and its place among that
-- | function's segments.
newtype SegmentId = SegmentId { func :: P.Int, index :: P.Int }

derive instance Eq SegmentId
derive instance Ord SegmentId

-- | A top-level value: one this module declares, by its place in `GLOBALS`, or one
-- | an imported module exports.
data GlobalRef
  = OwnGlobal P.Int
  | ImportedGlobal ModuleName Ident

-- | A constructor: one this module declares, by its place in `CTORS`, one an
-- | imported module declares, or `Prim.Unit`, which no module declares.
data CtorRef
  = OwnCtor P.Int
  | ImportedCtor ModuleName Ident
  | PrimUnit

-- | One of the two `Base.IO` entries, which the runtime carries out itself.
data IOEntry
  = IOPure
  | IOBind

derive instance Eq IOEntry

-- | A foreign, as what carries it out: an operation of the ABI, a `Base.IO` entry,
-- | or a host implementation, reached through the declaring module — this one, by
-- | its place in `FOREIGNS`, or an imported one, which exports it.
data ForeignRef
  = ForeignOperation PrimOp
  | ForeignIO IOEntry
  | OwnForeign P.Int
  | ImportedForeign ModuleName Ident

data Callee
  = CalleeGlobal GlobalRef
  | CalleeCtor CtorRef
  -- | An operation, by its place in the module's `PRIMS`.
  | CalleePrim P.Int
  | CalleeForeign ForeignRef

-- | What a call transfers to: a global, which `CALLK` names, or the value in a
-- | register, which `CALLU` applies.
data Target
  = TargetGlobal GlobalRef
  | TargetReg P.Int

data Literal
  = LitInt P.Int
  | LitNumber P.Number
  | LitString ScalarString
  | LitChar P.Int
  | LitBoolean P.Boolean

-- | What an instruction computes. Every operand is a register.
data Expr
  = Reg P.Int
  | Capture P.Int
  | Lit Literal
  | Global GlobalRef
  -- | The one value of a constructor of arity 0.
  | CtorValue CtorRef
  | Closure P.Int (P.Array P.Int)
  -- | A closure whose capture slots are filled afterwards.
  | OpenClosure P.Int P.Int
  | Pap Callee (P.Array P.Int)
  | Construct CtorRef (P.Array P.Int)
  | Field P.Int CtorRef P.Int
  | RecordEmpty
  | RecordExtend P.String P.Int P.Int
  | RecordSelect P.String P.Int
  | RecordRestrict P.String P.Int
  | RecordUpdate P.String P.Int P.Int
  | RecordMerge P.Int P.Int
  | Inject P.String P.Int
  | Payload P.String P.Int
  | Prim PrimOp (P.Array P.Int)
  -- | A foreign called with all its arguments. Its body is synchronous and applies no
  -- | Stella function, so the call cuts no segment.
  | CallForeign ForeignRef (P.Array P.Int)
  -- | What the cell at that position holds, of the region whose identity the
  -- | register holds.
  | CellGet P.Int P.Int
  -- | Replace what that cell holds with the last register's value, giving
  -- | `Prim.Unit`.
  | CellSet P.Int P.Int P.Int

data Stmt
  = Set P.Int Expr
  | SetCapture P.Int P.Int P.Int
  -- | A point no well-formed module reaches.
  | Unreachable P.String

type Block =
  { stmts :: P.Array Stmt
  , exit :: Exit
  }

-- | How a segment's straight run ends.
data Exit
  = Return P.Int
  -- | Return what calling the foreign gives, a foreign in tail position.
  | ReturnCall ForeignRef (P.Array P.Int)
  -- | A non-tail call. What follows it is segment `resume`, which the value
  -- | reaches in register `dest`.
  | Call { target :: Target, args :: P.Array P.Int, dest :: P.Int, resume :: SegmentId }
  -- | A tail call, replacing the frame.
  | TailCall { target :: Target, args :: P.Array P.Int }
  -- | Enter a join point, moving the arguments into its parameter registers as
  -- | one parallel move.
  | Jump { join :: SegmentId, moves :: P.Array (Tuple P.Int P.Int) }
  | If P.Int Block Block
  | SwitchCtor P.Int (P.Array { ctor :: CtorRef, body :: Block }) (Maybe Block)
  | SwitchLit P.Int (P.Array { lit :: Literal, body :: Block }) Block
  | SwitchKey P.Int (P.Array { key :: P.String, body :: Block }) (Maybe Block)
  -- | Perform operation `op` of the effect keyed `key` with the argument in `arg`.
  -- | What the operation gives reaches register `dest`, and what follows is
  -- | segment `resume`, as after a call.
  | Perform { key :: P.String, op :: P.String, arg :: P.Int, dest :: P.Int, resume :: SegmentId }
  -- | Install the `handler`-th handler of the table over the clauses in those
  -- | registers, and call the body. Its answer reaches `dest`
  -- | and what follows is segment `resume`, as after a call.
  | Handle { handler :: P.Int, operands :: HandleOperands, dest :: P.Int, resume :: SegmentId }
  -- | The same in tail position, replacing the frame.
  | TailHandle { handler :: P.Int, operands :: HandleOperands }
  -- | Open the `region`-th region of the table over the initial values in those
  -- | registers, and call the body with its identity. The body's value reaches
  -- | `dest` and what follows is segment `resume`, as after a call.
  | Open { region :: P.Int, operands :: OpenOperands, dest :: P.Int, resume :: SegmentId }
  -- | The same in tail position, replacing the frame.
  | TailOpen { region :: P.Int, operands :: OpenOperands }

-- | What installing a handler takes: the body, the return clause, and a clause per
-- | operation in the order the handler table lists them.
type HandleOperands =
  { body :: P.Int
  , ret :: P.Int
  , clauses :: P.Array P.Int
  }

-- | A handler of the table: the key of the effect it answers, and the operation
-- | each clause answers with whether that clause is `fast`.
type Handler =
  { key :: P.String
  , clauses :: P.Array { op :: P.String, fast :: P.Boolean }
  }

-- | What opening a region takes: the body, and a value per cell.
type OpenOperands =
  { body :: P.Int
  , initial :: P.Array P.Int
  }

-- | A region of the table: the key of each cell, in the order of their positions.
type Region =
  { cells :: P.Array P.String
  }

type Segment =
  { id :: SegmentId
  , body :: Block
  }

-- | A function of the function table.
type FrameFunction =
  { index :: P.Int
  , name :: Maybe P.String
  , arity :: P.Int
  , registers :: P.Int
  , entry :: SegmentId
  , segments :: P.Array Segment
  }
