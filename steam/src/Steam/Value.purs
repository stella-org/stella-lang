-- | What the interpreter holds while a program runs
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | **This is an internal representation and not a published ABI.** No `.dmo`
-- | depends on it, and a foreign implementation reaches it only through the
-- | adapter boundary. `Rep` plays no part: every value is held one way, whatever
-- | a `.dmo` says about the slot it flows through (D31).
-- |
-- | The values and the stack are one module because they refer to each other: a
-- | continuation is a value, and what it holds is a run of stack entries whose
-- | activations hold values.
-- |
-- | **An identity is assigned when a module is loaded.** A `KEYS`, `OPS`, or
-- | `CTORS` index is the file's own, so two modules may write one key at
-- | different indices; what a running program compares is the identity the
-- | registry assigned, one per key, operation name, and constructor across
-- | everything loaded.
module Steam.Value
  ( ModuleId(..)
  , CtorId(..)
  , KeyId(..)
  , OpId(..)
  , Foreign(..)
  , ForeignBody
  , ForeignOutcome(..)
  , FuncRef
  , Value(..)
  , Opaque
  , IOValue(..)
  , NativeAction
  , ActionOutcome(..)
  , IOEntry(..)
  , entryOfIO
  , arityOfIO
  , ioEntries
  , Closure
  , Callee(..)
  , Pap
  , Continuation(..)
  , Activation
  , StackEntry(..)
  , Root
  , Marker
  , MarkerKind(..)
  , Clause
  , Region
  , Cell
  , valueOfConstant
  , matchesConstant
  , reinstate
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Uncurried (EffectFn1)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Data.Traversable (traverse)
import Stella.Compiler.Bytecode.Instr (FuncIx, Node, Reg)
import Stella.Compiler.Bytecode.Module (Constant(..))
import Stella.Compiler.MiddleEnd.IR (ClauseForm)
import Stella.Compiler.Primitive (PrimOp)
import Stella.Compiler.TypedCore.Domain (ScalarString, ScalarValue, sameNumber, textOf)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))

-- Identities --------------------------------------------------------------------

-- | A module in the registry.
newtype ModuleId = ModuleId P.Int

-- | A constructor, of whichever module declares it. A data value carries one, so
-- | a dispatch in one module reaches values another module built.
newtype CtorId = CtorId P.Int

-- | A row key: a record's field, a variant's tag, a handler's effect, or a cell
-- | of a region. Equality is the whole of what a key is for.
newtype KeyId = KeyId P.Int

-- | An operation name, which is what a clause of a handler is found by.
newtype OpId = OpId P.Int

-- | What a foreign entry is carried out by.
-- |
-- | A `Base` ABI entry the interpreter claims is carried out by the interpreter
-- | itself: its meaning is one for every backend and what it computes over is this
-- | representation ([Op](Op.purs)). Everything else is the host's, and what stands
-- | here is the body itself: **resolution happens at load**, so nothing is looked
-- | up while a program runs ([Foreign](Foreign.purs)).
-- |
-- | A hosted entry carries the name it was resolved for because a fault names the
-- | entry that produced it, and a body is a host function that says nothing about
-- | where it came from.
data Foreign
  = ForeignOperation PrimOp
  -- | `Base.IO.pure` or `Base.IO.bind`, which the interpreter claims like an
  -- | operation and which is not one: each returns `IO`, so a call of it is an
  -- | `FFI` rather than a `PRIM` and no operation code stands for it.
  | ForeignIO IOEntry
  | ForeignHosted (Qualified Ident) ForeignBody

-- | The two entries of `core-runtime`.
-- |
-- | **Each constructs and executes nothing** (D25). What is reserved to the
-- | interpreter is the structure — `IOPure` and `IOBind` are the two shapes the
-- | drive loop is written against ([Drive](Drive.purs)) — and not the building of
-- | `IO` values as such: a hosted entry returning `IO` builds an `IONative` and
-- | does so all the time.
data IOEntry
  = IOPureEntry
  | IOBindEntry

-- | The `Base` name each realizes, and how many arguments saturate it. Both are the
-- | ABI's ([Prim and Base](../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)),
-- | and each is written once so that a loader and a reader cannot disagree.
entryOfIO :: IOEntry -> Qualified Ident
entryOfIO = case _ of
  IOPureEntry -> Qualified (ModuleName "Base.IO") (Ident "pure")
  IOBindEntry -> Qualified (ModuleName "Base.IO") (Ident "bind")

arityOfIO :: IOEntry -> P.Int
arityOfIO = case _ of
  IOPureEntry -> 1
  IOBindEntry -> 2

-- | The entries of `core-runtime`, which every interpreter claims.
ioEntries :: P.Array IOEntry
ioEntries = [ IOPureEntry, IOBindEntry ]

-- | A host implementation, as the interpreter calls it.
-- |
-- | **Uncurried and synchronous.** A saturated call hands it every argument at
-- | once, which is what the `FFI` instruction does; currying belongs to the
-- | declared type, and a partial application is the interpreter's to hold. A native
-- | action it returns is called later, by the drive loop, and synchronously there
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | It is an `EffectFn1` and not `Array Value -> Effect ForeignOutcome`, and the
-- | difference is the exception boundary rather than a matter of style. **A host
-- | function is what this holds, and applying one is already running it**: an
-- | implementation may throw where it is applied, not only where an effect it
-- | returned is performed. The curried form applies the function first and hands
-- | what comes back to whatever runs it, so a throw at application escapes ahead of
-- | anything that could catch it. This form makes the two one moment, which the
-- | call site then has inside its own `try` ([Eval](Eval.purs)).
-- |
-- | The effect is the host's own: a body may read and write hidden state, which is
-- | a conforming implementation and not a breach (D41).
type ForeignBody = EffectFn1 (P.Array Value) ForeignOutcome

-- | What a body answers with. A refusal is a fault, and the reason is what a report
-- | carries; **an exception is not one of these**, and what the interpreter does
-- | with one that escapes is in [Eval](Eval.purs).
data ForeignOutcome
  = Produced Value
  | Refused P.String
  -- | The host value is not what the result's kind says, as a description of what
  -- | was owed and what came back. **A breach of the contract by the
  -- | implementation**, which is a fault naming the entry: letting the value through
  -- | would put something no Stella type describes into a register.
  | Breached P.String
  -- | The argument at that position is not of the kind the signature gives it. The
  -- | values are the interpreter's own, so this is a state no `.dmo` admits rather
  -- | than anything the implementation did.
  | ArgumentNotOfKind P.Int

-- | A function table entry of a loaded module.
type FuncRef =
  { module :: ModuleId
  , func :: FuncIx
  }

-- Values ------------------------------------------------------------------------

-- | A value only a foreign observes. Nothing in the interpreter takes one apart,
-- | and neither does any instruction: it is carried, returned, and handed back to a
-- | foreign, and that is all.
foreign import data Opaque :: P.Type

-- | An action of the host, which is what a target entry constructs. Performing one
-- | is the drive loop's, and what it does belongs to the host.
-- |
-- | **An `Effect` is a host function of no arguments**, so performing one is calling
-- | it and there is no earlier moment at which it could throw outside what catches
-- | — the same property `ForeignBody` needs an `EffectFn1` to get.
type NativeAction = Effect ActionOutcome

-- | What performing an action answers with.
-- |
-- | **Performing an action returns, and nothing here waits.** Stella fixes no
-- | meaning for asynchrony, so there is no form that asks the loop to wait and
-- | nothing tests for a thenable: a promise a host hands back is an opaque value
-- | like any other
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md),
-- | [Open Questions](../../../docs/technical-references/99-Open-Questions/01-Open-Questions.md)).
data ActionOutcome
  = ActionProduced Value
  | ActionRefused P.String
  -- | What the action produced is not what the kind it was declared with says, as
  -- | the entry that returned the action and a description of what was wrong. The
  -- | same breach `Breached` is for a foreign's own result.
  | ActionBreached (Qualified Ident) P.String

data Value
  -- | Always an int32 (D37).
  = VInt P.Int
  -- | IEEE 754 binary64 (D37).
  | VNumber P.Number
  -- | A Unicode scalar value, and a string a sequence of those (D27).
  | VChar ScalarValue
  | VString ScalarString
  | VBoolean P.Boolean
  -- | A constructor and the fields it was applied to. A constructor of no fields
  -- | is this with an empty array.
  | VData CtorId (P.Array Value)
  | VRecord (Map KeyId Value)
  | VVariant KeyId Value
  | VClos Closure
  | VPap Pap
  | VCont Continuation
  -- | An `IO` value. **Opaque to the instruction set and not to the interpreter**:
  -- | no instruction examines one (D25), and the drive loop that executes one takes
  -- | it apart.
  | VIO IOValue
  | VOpaque Opaque

-- | What an `IO` value holds, which is what the runtime ABI builds: `Base.IO.pure`
-- | and `Base.IO.bind` construct the first two and a target entry the third.
-- |
-- | Reduction halts once it has constructed one of these (D25). Executing it is
-- | the drive loop's: a `Bind` executes what it holds and applies the function to
-- | the value that comes out, which is the one place the host side enters the
-- | interpreter.
-- |
-- | The function of a `Bind` is a value rather than a closure, a function value
-- | being a closure, a partial application, or a continuation alike.
data IOValue
  = IOPure Value
  | IOBind IOValue Value
  | IONative NativeAction

-- | A function entry together with what it closed over.
-- |
-- | **The capture slots are mutable and are filled once.** A recursive group
-- | allocates every member before any capture list is filled, which is what a
-- | guarded `letrec` needs (D14): `CLOSN` allocates the slots and `SETCAP` fills
-- | them. A slot still unfilled when `CAPT` reads it is an interpreter bug, not a
-- | value, which is why the map holds what is filled rather than a placeholder.
type Closure =
  { func :: FuncRef
  , captures :: Ref (Map P.Int Value)
  }

-- | What a partial application is waiting to apply. A constructor and a foreign
-- | are callable only through one, and an operation likewise: each takes a fixed
-- | number of arguments and is carried out when the last arrives.
-- |
-- | A constructor's and a foreign's arity is what the declaring module stated and
-- | the loader resolved, so it is carried here. An operation's is the ABI's, with
-- | one definition in `arityOfOp`, so it is derived rather than carried: an arity
-- | written twice is an arity that can disagree.
data Callee
  = CalleeClosure Closure
  | CalleeCtor CtorId P.Int
  | CalleeForeign Foreign P.Int
  | CalleePrim PrimOp

-- | A callee and the arguments supplied so far, which are always fewer than the
-- | callee takes.
type Pap =
  { callee :: Callee
  , args :: P.Array Value
  }

-- | A captured run of stack entries, from the activation that performed the
-- | operation up to and including the marker that answered it.
-- |
-- | **The last entry is the top**, as it is on the stack itself, so the entry at
-- | index zero is the marker the capture ended at and re-pushing a segment appends
-- | it in the order it stands.
-- |
-- | **A continuation takes one argument.** Applying one to more is ordinary: the
-- | answer type may be a function type, so the first argument is what the
-- | resumption resumes with and the rest is work pending on what comes back.
newtype Continuation = Continuation (P.Array StackEntry)

-- The stack ---------------------------------------------------------------------

-- | What one call is running.
-- |
-- | `regs` is one map rather than an array of slots so that a register holding
-- | nothing is not a value: reading one is an interpreter bug rather than a
-- | placeholder. **The map is mutable and is not shared between applications of a
-- | continuation**, which is what `reinstate` sees to.
-- |
-- | `node` and `ip` are **where the activation resumes**, and are written where it
-- | is suspended: the `Node` it stands in and the instruction of that node's code
-- | to continue at.
type Activation =
  { func :: FuncRef
  , closure :: Closure
  , regs :: Ref (Map Reg Value)
  , node :: Node
  , ip :: P.Int
  }

-- | An entry of the stack. **Each says what it does with a value that reaches
-- | it**, which is what makes a return, a resumption, and a handler's answer one
-- | path.
data StackEntry
  -- | Write the value into that register of the activation and continue it. This
  -- | is the only entry carrying a destination, and a tail call pushes none.
  = Resume Activation Reg
  -- | Apply the value to these arguments, what that produces reaching the entry
  -- | below. An over-application leaves one behind, and so does a continuation
  -- | applied to more than one argument.
  | ApplyRemaining (P.Array Value)
  | HandlerMarker Marker
  | RegionFrame Region
  -- | Where a `fast` clause's body begins. Core binds that body outside the
  -- | handler that answered and outside everything between that handler and the
  -- | `perform` (D28), so a search for a marker or a cell that reaches this entry
  -- | continues directly below that handler's marker, which stands this many
  -- | entries further down. What the body itself installs stands above and is
  -- | found as usual.
  -- |
  -- | **The distance is relative, not a position.** A `full` operation the body
  -- | performs may capture a segment holding this entry and re-push it anywhere,
  -- | any number of times; the handler's marker travels in the same segment, so the
  -- | distance between the two survives where a position would not.
  -- |
  -- | A value reaching it passes down unchanged, to the `Resume` of the `PERF`
  -- | below it.
  | ClauseBoundary P.Int
  -- | The bottom of an invocation a host answers the operations of one key for. A
  -- | `perform` whose search reaches it asks the host rather than running a clause,
  -- | and the run stops there until the host answers ([Eval](Eval.purs)). **It is
  -- | no handler**: it has no return clause, opens no region, and a continuation
  -- | never holds it, a `full` clause capturing only what stands above its own
  -- | marker. A value reaching it passes down unchanged and is what the run
  -- | produces.
  | RootBoundary Root
  -- | The bottom of a closed invocation, which nothing outside answers. A
  -- | `perform` whose search reaches it ends the run, as the key performed
  -- | ([Eval](Eval.purs)). Like a root boundary it is no handler, and a value
  -- | reaching it passes down unchanged and is what the run produces.
  | ClosedBoundary

-- | The key a root boundary answers, and the one operation of it.
type Root =
  { key :: KeyId
  , op :: OpId
  }

-- | An installed handler: the key it answers, a clause per operation, and the
-- | return clause every value passes through.
type Marker =
  { kind :: MarkerKind
  -- | Whether the frame directly below it is the region this marker opened. An
  -- | owner closes that frame before its return clause runs; a reinstatement owns
  -- | nothing, the frame it stands in belonging to whoever opened it.
  , ownsRegion :: P.Boolean
  , key :: KeyId
  , clauses :: P.Array Clause
  , returnClause :: Value
  }

-- | Which reduction a marker takes when a value reaches it.
-- |
-- | Nothing in a `.dmo` carries this: installing a handler produces an owner, and
-- | applying a continuation produces a reinstatement at the bottom of the segment
-- | it re-pushes. An owner closes the region below it before its return clause
-- | runs; a reinstatement leaves that region to whoever opened it.
data MarkerKind
  = Owner
  | Reinstatement

-- | A clause and the form it was declared in. A `fast` clause is called with the
-- | operation's argument and captures nothing; a `full` clause is called with the
-- | argument and the continuation (D28).
type Clause =
  { op :: OpId
  , form :: ClauseForm
  , clause :: Value
  }

-- | A region of cells, which stands below the marker of the handler owning it.
-- | It is part of the stack and not a store, so a captured segment carries the
-- | values its cells held at the capture (D36).
type Region =
  { cells :: P.Array Cell
  }

type Cell =
  { key :: KeyId
  , value :: Ref Value
  }

-- Applying a continuation ------------------------------------------------------

-- | The entries one application of a continuation pushes.
-- |
-- | **A continuation may be applied any number of times, and each application
-- | proceeds from the state that was captured** (D33). What a segment holds that
-- | an application can change is the register map of each activation in it and the
-- | cell of each region frame, so this allocates a fresh reference for each,
-- | holding what it held at the capture. Copying the array alone would leave every
-- | application sharing those references, and the second would begin where the
-- | first stopped.
-- |
-- | **Every application clones, the first one included.** The captured segment is
-- | the record of the capture and is never the thing that runs.
-- |
-- | What is shared rather than copied is every value those references hold: what
-- | is copied is the holder of the control state, not what it holds, so a value
-- | keeps its identity across applications, and a value written into in place, such
-- | as an array, is one value before the capture and after. A closure's capture
-- | slots are shared too — they are filled once, where the closure is built, and a
-- | segment carries closures rather than building them.
-- |
-- | **The marker at the bottom is a reinstatement, whichever kind was captured
-- | there.** It owns no frame: the frame its `handle` opened stayed behind when the
-- | segment was split, and closing it belongs to whoever holds it now. Every other
-- | marker returns as what it was, an owner among them carrying the frame it owns
-- | along with it. This is why one operation both copies and marks: an application
-- | that skipped the marking would take the owner's completion path and close a
-- | region it does not own.
-- |
-- | The bottom of a captured segment is the marker that answered the operation. One
-- | whose bottom is something else is a segment no capture produces, and nothing
-- | here invents an answer for it.
reinstate :: Continuation -> Effect (P.Array StackEntry)
reinstate (Continuation entries) = traverse entry (reinstated entries)
  where
  entry = case _ of
    Resume activation dest -> do
      regs <- Ref.read activation.regs >>= Ref.new
      pure (Resume (activation { regs = regs }) dest)
    RegionFrame region -> do
      cells <- traverse cell region.cells
      pure (RegionFrame { cells })
    other -> pure other

  cell c = do
    value <- Ref.read c.value >>= Ref.new
    pure { key: c.key, value }

-- | The segment with its bottom marker standing as a reinstatement.
reinstated :: P.Array StackEntry -> P.Array StackEntry
reinstated entries = case Array.head entries of
  Just (HandlerMarker marker) ->
    Array.updateAtIndices
      [ Tuple 0 (HandlerMarker (marker { kind = Reinstatement, ownsRegion = false })) ]
      entries
  _ -> entries

-- Constants ---------------------------------------------------------------------

-- | The value a constant of the pool stands for.
valueOfConstant :: Constant -> Value
valueOfConstant = case _ of
  CInt n -> VInt n
  CNumber n -> VNumber n
  CString s -> VString s
  CChar c -> VChar c
  CBoolean b -> VBoolean b

-- | Whether a value is the constant, which is what dispatch on a literal
-- | compares.
-- |
-- | **Identity is equality of the value, and for a `Number` it is equality of the
-- | bit pattern with all NaNs taken as one** (D37): `0.0` and `-0.0` are
-- | different literals, and a NaN is one literal. The host's `==` decides neither,
-- | identifying the two zeros and separating a NaN from itself.
-- |
-- | A value of another class is not the constant. Dispatch on a literal reaches
-- | only a register the lowering gave that class, so a mismatch here is a
-- | question that is never asked rather than a falsehood.
matchesConstant :: Value -> Constant -> P.Boolean
matchesConstant value constant = case value, constant of
  VInt a, CInt b -> a == b
  VNumber a, CNumber b -> sameNumber a b
  VString a, CString b -> textOf a == textOf b
  VChar a, CChar b -> a == b
  VBoolean a, CBoolean b -> a == b
  _, _ -> false

derive instance Eq ModuleId
derive instance Ord ModuleId
derive newtype instance Show ModuleId

derive instance Eq CtorId
derive instance Ord CtorId
derive newtype instance Show CtorId

derive instance Eq KeyId
derive instance Ord KeyId
derive newtype instance Show KeyId

derive instance Eq OpId
derive instance Ord OpId
derive newtype instance Show OpId

derive instance Eq IOEntry
derive instance Ord IOEntry
derive instance Generic IOEntry _

instance Show IOEntry where
  show = genericShow

-- | **Two foreigns are equal when they are carried out by the same thing**, and a
-- | hosted entry is compared by the name it was resolved for: a body is a host
-- | function, which nothing compares.
instance Eq Foreign where
  eq (ForeignOperation a) (ForeignOperation b) = a == b
  eq (ForeignIO a) (ForeignIO b) = a == b
  eq (ForeignHosted a _) (ForeignHosted b _) = a == b
  eq _ _ = false

derive instance Eq MarkerKind
derive instance Generic MarkerKind _

instance Show MarkerKind where
  show = genericShow
