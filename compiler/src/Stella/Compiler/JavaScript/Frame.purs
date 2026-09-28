-- | Frame IR: the lower IR of the frame strategy.
-- |
-- | Under this strategy an activation is a frame on a stack of the runtime's own,
-- | and a Stella function is a set of **segments**: its entry, and one for what
-- | follows each non-tail call. A segment runs straight to the next transfer and
-- | says what the run loop does next, so the host's call stack never holds more
-- | than one of them, which is how a tail call pushes nothing and a deep recursion
-- | runs in bounded host stack
-- | ([JavaScript](../../../../../docs/technical-references/05-Backend/05-JavaScript.md)).
-- |
-- | Everything a segment names is resolved already: a register is a slot of the
-- | frame, a constructor and a global are references the emitter turns into
-- | bindings, and a key is its canonical string.
module Stella.Compiler.JavaScript.Frame
  ( SegmentId(..)
  , GlobalRef(..)
  , CtorRef(..)
  , Callee(..)
  , Target(..)
  , Literal(..)
  , Expr(..)
  , Stmt(..)
  , Block
  , Exit(..)
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

data Callee
  = CalleeGlobal GlobalRef
  | CalleeCtor CtorRef
  -- | An operation, by its place in the module's `PRIMS`.
  | CalleePrim P.Int

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
