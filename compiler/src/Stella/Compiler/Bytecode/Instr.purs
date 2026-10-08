-- | The instruction set.
-- |
-- | Code is linear within a straight run of instructions and structured above
-- | it: a function is a tree of instruction sequences whose edges name their
-- | destinations. A transfer to a join point names it, and a decision tree nests
-- | as a tree, so a consumer generating structured control flow walks this form
-- | rather than reconstructing it (D32).
-- |
-- | Every operand that names something outside the function is an index into one
-- | of the module's tables.
module Stella.Compiler.Bytecode.Instr
  ( Reg(..)
  , ConstIx(..)
  , KeyIx(..)
  , OpIx(..)
  , CtorIx(..)
  , GlobalIx(..)
  , ForeignIx(..)
  , CalleeIx(..)
  , PrimIx(..)
  , FuncIx(..)
  , HandlerIx(..)
  , RegionIx(..)
  , JoinName(..)
  , Instr(..)
  , Tail(..)
  , Node
  , Join
  , CtorCase
  , LitCase
  , KeyCase
  , Function
  ) where

import Prelude

import Prim as P

import Stella.Compiler.MiddleEnd.Rep (Rep)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)

-- | A slot of the current activation's flat register file.
newtype Reg = Reg P.Int

newtype ConstIx = ConstIx P.Int
newtype KeyIx = KeyIx P.Int
newtype OpIx = OpIx P.Int
newtype CtorIx = CtorIx P.Int
newtype GlobalIx = GlobalIx P.Int
newtype ForeignIx = ForeignIx P.Int
newtype CalleeIx = CalleeIx P.Int
newtype PrimIx = PrimIx P.Int
newtype FuncIx = FuncIx P.Int
newtype HandlerIx = HandlerIx P.Int
newtype RegionIx = RegionIx P.Int

-- | A join point's name. **A transfer names its destination and is never an
-- | offset**, so that the structure survives the format.
newtype JoinName = JoinName P.Int

data Instr
  = LOADK Reg ConstIx
  | LOADG Reg GlobalIx
  -- | A constructor of arity 0, which allocates nothing new.
  | LOADC Reg CtorIx
  | MOVE Reg Reg
  -- | Capture `i` of the current activation's closure. **Captures are not
  -- | registers**; this is what brings one into the file.
  | CAPT Reg P.Int
  | CLOS Reg FuncIx (P.Array Reg)
  -- | A closure whose capture slots are left unfilled, for a recursive group:
  -- | every member is allocated before any capture list is filled.
  | CLOSN Reg FuncIx P.Int
  | SETCAP Reg P.Int Reg
  | PAP Reg CalleeIx (P.Array Reg)
  | CTOR Reg CtorIx (P.Array Reg)
  | CALLK Reg GlobalIx (P.Array Reg)
  -- | Under- and over-application are resolved here. Applying a continuation is
  -- | an ordinary one of these.
  | CALLU Reg Reg (P.Array Reg)
  -- | **May fault.**
  | FFI Reg ForeignIx (P.Array Reg)
  | FIELD Reg Reg CtorIx P.Int
  | RNEW Reg
  | REXT Reg KeyIx Reg Reg
  | RSEL Reg KeyIx Reg
  | RRES Reg KeyIx Reg
  -- | The record first and the value second, as Core writes it.
  | RUPD Reg KeyIx Reg Reg
  | RMRG Reg Reg Reg
  | VINJ Reg KeyIx Reg
  | VPAY Reg KeyIx Reg
  -- | Never reached: the operand's type is uninhabited.
  | VABS Reg Reg
  -- | A `Base` ABI operation, carried out directly. **May fault**: which entries
  -- | do, and on which inputs, is the ABI specification's to say and not this
  -- | stage's.
  | PRIM Reg PrimIx (P.Array Reg)
  | PERF Reg KeyIx OpIx Reg
  -- | Install the handler and call the body. The marker stands between the
  -- | calling activation and the body's, so what the return clause gives arrives
  -- | in the destination by the ordinary route a call's value arrives by.
  -- |
  -- | The two registers are the body and the return clause, and the array the
  -- | operation clauses in the order the handler table lists them. Every closure
  -- | is built by an ordinary `CLOS`, so none of them carries a capture list here.
  | HNDL Reg HandlerIx Reg Reg (P.Array Reg)
  -- | Open a region and call the body, a closure of one parameter, with the
  -- | region's identity: a value telling this opening from every other, the
  -- | copies a continuation makes of it aside. The region frame stands between
  -- | the calling activation and the body's, so the body's value arrives in the
  -- | destination as a call's does.
  -- |
  -- | The register is the body and the array the initial value of each cell, one
  -- | per cell of the region's entry and in that order.
  | RGN Reg RegionIx Reg (P.Array Reg)
  -- | The cell at that position of the region whose identity the register holds.
  | CGET Reg Reg P.Int
  -- | Replace what that cell holds. The destination receives `Prim.Unit`, a
  -- | write having no result of its own; reading back what was set takes a `CGET`.
  | CSET Reg Reg P.Int Reg

-- | What ends a `Node`. A `Node` held inline is what keeps a decision tree a
-- | tree; a `JoinName` is what a shared branch is reached by.
data Tail
  = RET Reg
  | TAILK GlobalIx (P.Array Reg)
  | TAILU Reg (P.Array Reg)
  | TAILFFI ForeignIx (P.Array Reg)
  | JMP JoinName (P.Array Reg)
  | BRIF Reg Node Node
  | BRC Reg (P.Array CtorCase) (Maybe Node)
  -- | Literals cannot be exhausted, so the default is not optional.
  | BRL Reg (P.Array LitCase) Node
  | BRK Reg (P.Array KeyCase) (Maybe Node)
  | TAILHNDL HandlerIx Reg Reg (P.Array Reg)
  | TAILRGN RegionIx Reg (P.Array Reg)

-- | A straight run of instructions ending in exactly one `Tail`.
type Node =
  { code :: P.Array Instr
  , tail :: Tail
  }

type CtorCase = { ctor :: CtorIx, body :: Node }
type LitCase = { lit :: ConstIx, body :: Node }
type KeyCase = { key :: KeyIx, body :: Node }

-- | A join point, and the registers it takes its arguments in. A consumer that
-- | did not know which they were could not perform the transfer.
type Join =
  { name :: JoinName
  , params :: P.Array Reg
  , body :: Node
  }

-- | `regs` carries one `Rep` per register, the first `nparams` of them the
-- | parameters; `captures` one per capture slot.
type Function =
  { nparams :: P.Int
  , regs :: P.Array Rep
  , captures :: P.Array Rep
  , joins :: P.Array Join
  , body :: Node
  }

derive instance Eq Reg
derive instance Ord Reg
derive newtype instance Show Reg

derive instance Eq ConstIx
derive instance Ord ConstIx
derive newtype instance Show ConstIx

derive instance Eq KeyIx
derive instance Ord KeyIx
derive newtype instance Show KeyIx

derive instance Eq OpIx
derive instance Ord OpIx
derive newtype instance Show OpIx

derive instance Eq CtorIx
derive instance Ord CtorIx
derive newtype instance Show CtorIx

derive instance Eq GlobalIx
derive instance Ord GlobalIx
derive newtype instance Show GlobalIx

derive instance Eq ForeignIx
derive instance Ord ForeignIx
derive newtype instance Show ForeignIx

derive instance Eq CalleeIx
derive instance Ord CalleeIx
derive newtype instance Show CalleeIx

derive instance Eq PrimIx
derive instance Ord PrimIx
derive newtype instance Show PrimIx

derive instance Eq FuncIx
derive instance Ord FuncIx
derive newtype instance Show FuncIx

derive instance Eq HandlerIx
derive instance Ord HandlerIx
derive newtype instance Show HandlerIx

derive instance Eq RegionIx
derive instance Ord RegionIx
derive newtype instance Show RegionIx

derive instance Eq JoinName
derive instance Ord JoinName
derive newtype instance Show JoinName

derive instance Eq Instr
derive instance Generic Instr _

instance Show Instr where
  show x = genericShow x

derive instance Eq Tail
derive instance Generic Tail _

instance Show Tail where
  show x = genericShow x
