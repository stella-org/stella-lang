-- | Running a program
-- | ([Bytecode](../../../docs/technical-references/05-Backend/01-Bytecode.md),
-- | [Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | The interpreter holds a **stack** of its own, and every entry of it says what
-- | it does with a value that reaches it. A call pushes a `Resume` carrying the
-- | activation and the register its value belongs in; a tail call pushes nothing,
-- | which is the whole of what makes it a tail call.
-- |
-- | **A branch is not a call.** `BRIF`, `BRC`, `BRL`, and `BRK` select a `Node` of
-- | the activation they stand in, and so does a `JMP` once it has written its
-- | arguments into the join point's registers.
-- |
-- | **A known call and an unknown call are different transfers.** `CALLK` and
-- | `TAILK` name a function entry whose arity is settled, so the closure a global
-- | slot holds is entered with exactly the arguments it takes and nothing about the
-- | call is resolved while it runs (D30). `CALLU` and `TAILU` are where under- and
-- | over-application are resolved: too few arguments build a partial application
-- | over the callee, whatever kind it is, and too many call it and apply the rest
-- | to what comes back. **Applying a continuation is an ordinary `CALLU`**, a
-- | continuation being a function value of one argument.
-- |
-- | A run reaches several modules: a closure names the module its function belongs
-- | to, and an activation runs against the tables of that module, so what resolves
-- | either is the registry.
module Steam.Eval
  ( Class(..)
  , Bug(..)
  , Failure(..)
  , EVAL
  , enter
  , enterClosed
  , applyFunction
  , Outcome(..)
  , Halt(..)
  , Suspension
  , Pause
  , Slice
  , invoke
  , invokeClosed
  , resumeWith
  , resumePaused
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (traverse_)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Exception (message, try)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Uncurried (runEffectFn1)
import Run (EFFECT, Run, liftEffect)
import Run.Except (EXCEPT)
import Run.Except as Except
import Steam.Fault (Fault(..))
import Steam.Module (CalleeTarget(..), CtorRef, ForeignRef, GlobalSlot, HandlerRef, Loaded, Prepared, RegionRef, Registry)
import Steam.Op as Op
import Steam.Region as Region
import Steam.Value (Activation, Callee(..), Clause, Closure, Continuation(..), CtorId, Foreign(..), ForeignOutcome(..), IOEntry(..), IOValue(..), KeyId, Marker, ModuleId, OpId, Root, StackEntry(..), Value(..), matchesConstant, reinstate, valueOfConstant)
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ConstIx(..), CtorIx(..), ForeignIx(..), FuncIx(..), GlobalIx(..), HandlerIx(..), Instr(..), Join, JoinName, KeyIx(..), OpIx(..), PrimIx(..), Reg(..), RegionIx(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Constant)
import Stella.Compiler.MiddleEnd.IR (ClauseForm(..))
import Stella.Compiler.Primitive (InClosedRun(..), PrimOp, arityOfOp, inClosedRunOf)
import Steam.Array (Owned)
import Steam.Array as Arr
import Stella.Compiler.TypedCore.Name (Ident, Qualified)
import Type.Row (type (+))

-- | What an instruction expected of a register it read. The class of every value
-- | is settled before a `.dmo` exists, so a mismatch here is not a program's
-- | error but a defect above it.
data Class
  = ABoolean
  | AConstructorValue
  | ARecord
  | AVariant
  | AClosure
  | ACallable
  -- | An `IO` value, which `Base.IO.bind` takes as its first argument.
  | AnIO

-- | A state no `.dmo` admits. Reaching one is a defect in the interpreter, in
-- | lowering, or in a check a loader owes.
data Bug
  -- | A register or a capture slot read before anything was written into it.
  = RegisterHoldsNothing Reg
  | CaptureHoldsNothing P.Int
  -- | A global slot read before its module was initialized.
  | GlobalHoldsNothing GlobalIx
  -- | An index naming nothing in the table it stands in.
  | NoSuchConstant ConstIx
  | NoSuchKey KeyIx
  | NoSuchCtor CtorIx
  | NoSuchCallee CalleeIx
  | NoSuchGlobal GlobalIx
  | NoSuchFunction FuncIx
  | NoSuchJoin JoinName
  -- | A value of the wrong class in a register an instruction reads.
  | NotOfClass Class
  -- | A module the registry does not hold, which a closure or an activation
  -- | named.
  | NoSuchModule ModuleId
  -- | A closure built with a number of capture slots the function it runs does not
  -- | have, as the count declared and the count given.
  | WrongCaptureCount FuncIx P.Int P.Int
  -- | A capture slot outside what the closure has.
  | CaptureOutOfRange FuncIx P.Int
  -- | A capture slot filled twice. Each is filled once, where the group it belongs
  -- | to is built.
  | CaptureAlreadyFilled P.Int
  -- | A number of arguments the callee does not take, as the arity and the count.
  | WrongArgumentCount FuncIx P.Int P.Int
  | WrongCtorArity CtorId P.Int P.Int
  | WrongJumpArity JoinName P.Int P.Int
  -- | A partial application that is not partial, as the arity and the count.
  | PapNotBelowArity P.Int P.Int
  -- | Operands an operation does not take, by the operation.
  | WrongOperands PrimOp
  -- | An index naming nothing in the module's `PRIMS`.
  | NoSuchPrim PrimIx
  | NoSuchForeign ForeignIx
  | NoSuchHandler HandlerIx
  -- | A `PERF` for which no marker of that key is installed, which effect safety
  -- | rules out: a handler of the key encloses every `perform` of it.
  | NoHandlerInstalled KeyId
  -- | An operation nothing that answers its key answers: a marker of the key holding
  -- | no clause for it, which a handler removing the effect cannot be, or a root
  -- | boundary of the key answering another operation, which an invocation whose
  -- | root names the one operation of its effect cannot reach.
  | NoClauseForOperation OpIx
  | NoSuchRegion RegionIx
  -- | A `CGET` or `CSET` through a value that is no region's identity.
  | NotARegion
  -- | A `CGET` or `CSET` of a region no visible frame of the stack holds, which
  -- | typing rules out: a function reaching a region's cells runs where the region
  -- | is open.
  | RegionNotOpen
  -- | A cell position the region does not have.
  | NoSuchCell P.Int
  -- | A handler installed with a number of clauses its table does not state, or a
  -- | region opened with a number of initial values. Loading refuses such an
  -- | instruction, so a loaded module never reaches this.
  | WrongHandlerShape HandlerIx
  | WrongRegionShape RegionIx
  -- | A `Base.IO` entry applied to a count it does not take, as the entry and the
  -- | count. Its arity is the ABI's and a loader checked it, so this is what a
  -- | `.dmo` that got past that would produce.
  | WrongIOArity IOEntry P.Int
  -- | An application supplying no argument, which nothing produces.
  | NoArgument
  -- | A field of a constructor value the constructor does not have.
  | NoSuchField CtorId P.Int
  -- | A `FIELD` whose constructor is not the one the value carries, which the
  -- | branch that selected it would have settled.
  | CtorMismatch CtorId CtorId
  -- | A key an operation found present where rows make it absent, or absent where
  -- | they make it present (D4).
  | KeyPresent KeyId
  | KeyAbsent KeyId
  -- | A dispatch none of whose cases matched, where it carries no default. A
  -- | dispatch whose cases exhaust needs none, and one whose cases do not was
  -- | given one.
  | NoBranchTaken
  -- | A registry holding no module, which a run has nothing to be against: even
  -- | the one `Prim.Unit` every module carries is not there to be taken.
  | RegistryEmpty
  -- | A `Bind` whose function returned what is not an `IO`. Its type says it does,
  -- | and a `.dmo` carries no type: the culprit is a lowering or an adapter in
  -- | breach, and the machine cannot tell which.
  | NotAnIOFromContinuation
  -- | A hosted foreign handed an argument not of the kind its signature gives that
  -- | position, as the entry and the position. The values are the interpreter's
  -- | own, so what put it there is a lowering or a signature that does not belong
  -- | to the declaration.
  | ForeignArgumentNotOfKind (Qualified Ident) P.Int
  -- | `VABS`, whose operand's type is uninhabited, so nothing reaches it.
  | Unreachable
  -- | A suspension resumed after it already was. Each is resumed once: what it
  -- | holds is the one run it stopped, and that run has gone on.
  | SuspensionAlreadyResumed
  -- | A `perform` answered by a root boundary in a run no invocation began, which
  -- | pushes none: nothing a run of its own holds can carry one.
  | AskedOutsideInvocation
  -- | A run that is not closed halted as only a closed one does: only
  -- | `invokeClosed` begins one.
  | HaltedOutsideClosedRun

-- | What ends a run before its value.
data Failure
  = Bug Bug
  -- | An operation or a foreign failing as the ABI says it may. Nothing catches one
  -- | ([Bytecode](../../../docs/technical-references/05-Backend/01-Bytecode.md)).
  | Faults Fault
  -- | An instruction outside what this interpreter carries out, by its mnemonic.
  | Unimplemented P.String

-- | Running a program reads and writes references, and ends either in a value or
-- | in a failure.
type EVAL r = (EXCEPT Failure + EFFECT + r)

-- | The modules a run may reach, and the stack under whatever is running.
type Machine =
  { registry :: Registry
  , stack :: Ref (P.Array StackEntry)
  -- | `Prim.Unit`, which a write to a cell and a write to an array both answer
  -- | with. The identity is the registry's, assigned once across everything
  -- | loaded, so one value serves whichever module is running.
  , unit :: Value
  -- | The arrays a closed run made, where the run is one.
  , owned :: Maybe Owned
  }

-- | How a closed run reached outside it: an effect no handler of it answers, a
-- | foreign the host carries out, state the run did not make, or an operation no
-- | closed run carries out.
data Halt
  = EffectPerformed KeyId
  | HostForeignCalled (Qualified Ident)
  | StateNotOwned PrimOp
  | OperationWithheld PrimOp

derive instance Eq Halt
derive instance Generic Halt _
instance Show Halt where
  show = genericShow

-- | Where a run stands: inside an activation, carrying a value to whatever takes
-- | it, or done.
data State
  = Running Activation
  | Returning Value
  | Finished Value
  -- | Stopped at a `perform` a root boundary answers: the activation, already at
  -- | the instruction after the `PERF`, the register the answer belongs in, and
  -- | the argument the host is asked with.
  | Asking Activation Reg Value
  -- | Stopped where a closed run reached outside it, as how.
  | Halting Halt

-- | What executing one instruction leaves the machine to do.
data Next
  = Advance
  -- | A call to a function whose entry and arity are both settled: the activation
  -- | to enter, with the register the value it produces belongs in. Nothing about
  -- | it is resolved at run time (D30).
  | Known Reg Activation
  -- | A call to a value: the callee and its arguments, with the register the value
  -- | belongs in. This is where under- and over-application are resolved.
  | Unknown Reg Value (P.Array Value)
  -- | Installing a handler or opening a region: the entries to push under the body,
  -- | the body to enter, and what it is applied to. The calling activation's
  -- | `Resume` goes below them, so the marker or the frame stands between it and
  -- | the body.
  | Install Reg (P.Array StackEntry) Value (P.Array Value)
  -- | A `fast` clause answering a `PERF`: the clause, its argument, and where the
  -- | answering handler's marker stands, with the register the clause's value
  -- | belongs in. The calling activation's `Resume` goes below a `ClauseBoundary`,
  -- | so the body runs where Core binds it — outside that handler and outside what
  -- | stands between it and the `perform` — and its value still reaches the `PERF`.
  | Fast Reg Value Value P.Int
  -- | The instruction moved control itself. A `full` clause's answer does not return
  -- | to the `PERF`, so nothing waits for it there.
  | Moved State
  -- | A `PERF` a root boundary answers: the register the answer belongs in, and
  -- | the argument.
  | Ask Reg Value
  -- | A `PERF` that reached the bottom of a closed run, as the key it performs.
  | Escape KeyId

-- Registers, captures, and tables -------------------------------------------------

readReg :: forall r. Activation -> Reg -> Run (EVAL r) Value
readReg activation reg = do
  regs <- liftEffect (Ref.read activation.regs)
  case Map.lookup reg regs of
    Just value -> pure value
    Nothing -> bug (RegisterHoldsNothing reg)

writeReg :: forall r. Activation -> Reg -> Value -> Run (EVAL r) Unit
writeReg activation reg value =
  liftEffect (Ref.modify_ (Map.insert reg value) activation.regs)

-- | A capture of the closure the activation was entered through. **Captures are
-- | not registers**, and a slot is filled where the closure is built.
readCapture :: forall r. Activation -> P.Int -> Run (EVAL r) Value
readCapture activation i = do
  captures <- liftEffect (Ref.read activation.closure.captures)
  case Map.lookup i captures of
    Just value -> pure value
    Nothing -> bug (CaptureHoldsNothing i)

constantAt :: forall r. Loaded -> ConstIx -> Run (EVAL r) Constant
constantAt loaded ix@(ConstIx i) = case Array.index loaded.constants i of
  Just constant -> pure constant
  Nothing -> bug (NoSuchConstant ix)

keyAt :: forall r. Loaded -> KeyIx -> Run (EVAL r) KeyId
keyAt loaded ix@(KeyIx i) = case Array.index loaded.keys i of
  Just key -> pure key
  Nothing -> bug (NoSuchKey ix)

ctorAt :: forall r. Loaded -> CtorIx -> Run (EVAL r) CtorRef
ctorAt loaded ix@(CtorIx i) = case Array.index loaded.ctors i of
  Just ctor -> pure ctor
  Nothing -> bug (NoSuchCtor ix)

calleeAt :: forall r. Loaded -> CalleeIx -> Run (EVAL r) CalleeTarget
calleeAt loaded ix@(CalleeIx i) = case Array.index loaded.callees i of
  Just callee -> pure callee
  Nothing -> bug (NoSuchCallee ix)

functionAt :: forall r. Loaded -> FuncIx -> Run (EVAL r) Prepared
functionAt loaded ix@(FuncIx i) = case Array.index loaded.functions i of
  Just function -> pure function
  Nothing -> bug (NoSuchFunction ix)

-- | What a global slot holds. A module's imports are initialized before it is and
-- | its own globals in declaration order, so nothing reads a slot still empty.
globalAt :: forall r. Loaded -> GlobalIx -> Run (EVAL r) Value
globalAt loaded ix@(GlobalIx i) = case Array.index loaded.globals i of
  Nothing -> bug (NoSuchGlobal ix)
  Just slot -> readSlot ix slot

readSlot :: forall r. GlobalIx -> GlobalSlot -> Run (EVAL r) Value
readSlot ix slot = do
  held <- liftEffect (Ref.read slot)
  case held of
    Just value -> pure value
    Nothing -> bug (GlobalHoldsNothing ix)

-- | The module a closure or an activation names.
loadedOf :: forall r. Machine -> ModuleId -> Run (EVAL r) Loaded
loadedOf machine moduleId = case Map.lookup moduleId machine.registry of
  Just loaded -> pure loaded
  Nothing -> bug (NoSuchModule moduleId)

-- | The join point a transfer names, from the table loading built. Nothing here
-- | searches the function's join points.
joinAt :: forall r. Prepared -> JoinName -> Run (EVAL r) Join
joinAt function name = case Map.lookup name function.joins of
  Just join -> pure join
  Nothing -> bug (NoSuchJoin name)

bug :: forall r a. Bug -> Run (EVAL r) a
bug = Except.throw <<< Bug

unimplemented :: forall r a. P.String -> Run (EVAL r) a
unimplemented = Except.throw <<< Unimplemented

-- | A fault discards the stack and ends the run.
fault :: forall r a. Fault -> Run (EVAL r) a
fault = Except.throw <<< Faults

handlerAt :: forall r. Loaded -> HandlerIx -> Run (EVAL r) HandlerRef
handlerAt loaded ix@(HandlerIx i) = case Array.index loaded.handlers i of
  Just entry -> pure entry
  Nothing -> bug (NoSuchHandler ix)

regionAt :: forall r. Loaded -> RegionIx -> Run (EVAL r) RegionRef
regionAt loaded ix@(RegionIx i) = case Array.index loaded.regions i of
  Just entry -> pure entry
  Nothing -> bug (NoSuchRegion ix)

foreignAt :: forall r. Loaded -> ForeignIx -> Run (EVAL r) ForeignRef
foreignAt loaded ix@(ForeignIx i) = case Array.index loaded.foreigns i of
  Just entry -> pure entry
  Nothing -> bug (NoSuchForeign ix)

primAt :: forall r. Loaded -> PrimIx -> Run (EVAL r) PrimOp
primAt loaded ix@(PrimIx i) = case Array.index loaded.prims i of
  Just op -> pure op
  Nothing -> bug (NoSuchPrim ix)

-- The stack ------------------------------------------------------------------------

-- | The last entry is the top, so pushing appends and a segment is re-pushed in
-- | the order it stands.
push :: forall r. Machine -> StackEntry -> Run (EVAL r) Unit
push machine entry =
  liftEffect (Ref.modify_ (\stack -> Array.snoc stack entry) machine.stack)

pushAll :: forall r. Machine -> P.Array StackEntry -> Run (EVAL r) Unit
pushAll machine entries =
  liftEffect (Ref.modify_ (\stack -> stack <> entries) machine.stack)

pop :: forall r. Machine -> Run (EVAL r) (Maybe StackEntry)
pop machine = do
  stack <- liftEffect (Ref.read machine.stack)
  case Array.unsnoc stack of
    Just { init, last } -> do
      liftEffect (Ref.write init machine.stack)
      pure (Just last)
    Nothing -> pure Nothing

-- | The first entry, from the top down, at which `found` answers, with where it
-- | stands.
-- |
-- | **A `ClauseBoundary` is jumped over, together with everything below it down to
-- | and including the marker of the handler whose `fast` clause is running**: the
-- | walk continues directly below that marker, so what stood between the handler
-- | and the `perform` is not seen, while what stands below the marker is. A marker
-- | search and a region search read the stack by this one walk, which is what keeps
-- | `PERF`, `CGET`, and `CSET` reaching the same context.
visible :: forall a. P.Array StackEntry -> (StackEntry -> Maybe a) -> Maybe { at :: P.Int, found :: a }
visible stack found = go (Array.length stack - 1)
  where
  go i
    | i < 0 = Nothing
    | otherwise = case Array.index stack i of
        Just (ClauseBoundary toMarker) -> go (i - toMarker - 1)
        Just entry -> case found entry of
          Just a -> Just { at: i, found: a }
          Nothing -> go (i - 1)
        Nothing -> Nothing

-- | What answers a `perform` of that key: the innermost visible marker of it, and
-- | where it stands.
-- |
-- | **The innermost wins**, which is what makes handlers deep: a function handling
-- | an effect internally is pure to its caller, so two markers of one key may stand
-- | on the stack at once.
-- |
-- | A root boundary of the key answers where no marker above it does, and is found
-- | by the same walk: a handler the program installs is inner to it, and so is
-- | what a `fast` clause's boundary jumps over.
answererOf :: forall r. Machine -> KeyId -> Run (EVAL r) Answerer
answererOf machine key = do
  stack <- liftEffect (Ref.read machine.stack)
  case visible stack answering of
    Just { at, found: Left marker } -> pure (AtMarker at marker)
    Just { found: Right (Just root) } -> pure (AtRoot root)
    Just { found: Right Nothing } -> pure AtClosed
    Nothing -> bug (NoHandlerInstalled key)
  where
  answering = case _ of
    HandlerMarker marker | marker.key == key -> Just (Left marker)
    RootBoundary root | root.key == key -> Just (Right (Just root))
    ClosedBoundary -> Just (Right Nothing)
    _ -> Nothing

-- | What answers a `perform`: a handler's marker and where it stands, the root
-- | boundary, or the bottom of a closed run, which answers by ending it.
data Answerer
  = AtMarker P.Int Marker
  | AtRoot Root
  | AtClosed

-- | The cell at that position of the region whose identity the value is: the
-- | innermost visible frame of the identity, found by the walk `PERF` finds a
-- | marker by. **Copies of one opening share its identity**, and the innermost is
-- | the one the running code belongs to.
cellOf :: forall r. Machine -> Value -> P.Int -> Run (EVAL r) (Ref Value)
cellOf machine value index = case value of
  VOpaque o | Just identity <- Region.fromOpaque o -> do
    stack <- liftEffect (Ref.read machine.stack)
    case visible stack (frameOf identity) of
      Nothing -> bug RegionNotOpen
      Just { found } -> case Array.index found.cells index of
        Just cell -> pure cell
        Nothing -> bug (NoSuchCell index)
  _ -> bug NotARegion
  where
  frameOf identity = case _ of
    RegionFrame region | Region.same region.identity identity -> Just region
    _ -> Nothing

-- | Take everything from that entry upwards off the stack, which is what a `full`
-- | clause's continuation is made of.
splitAt :: forall r. Machine -> P.Int -> Run (EVAL r) (P.Array StackEntry)
splitAt machine at = do
  stack <- liftEffect (Ref.read machine.stack)
  liftEffect (Ref.write (Array.take at stack) machine.stack)
  pure (Array.drop at stack)

-- Entering and applying ------------------------------------------------------------

-- | Run a closure with its arguments to the value it returns.
-- |
-- | **The closure says which function runs**, so the code that runs and the
-- | captures `CAPT` reads cannot come from two different functions.
enter :: forall r. Registry -> Closure -> P.Array Value -> Run (EVAL r) Value
enter registry closure args = do
  -- the identity `Prim.Unit` was interned under, which every loaded module holds
  unit <- case Map.lookup closure.func.module registry of
    Just loaded -> pure loaded.unit
    Nothing -> bug (NoSuchModule closure.func.module)
  stack <- liftEffect (Ref.new [])
  let machine = { registry, stack, unit, owned: Nothing }
  activation <- activationOf machine closure args
  loop machine (Running activation)

-- | Run a closure with its arguments as a closed run, to the value it returns or
-- | to where it halted. **The arrays it may reach are those in `owned`**, which the
-- | caller hands over: one set may serve several runs that are to share what they
-- | make, as the initializers of one module do. Nothing bounds the run.
enterClosed :: forall r. Registry -> Owned -> Closure -> P.Array Value -> Run (EVAL r) (Either Halt Value)
enterClosed registry owned closure args = do
  unit <- case Map.lookup closure.func.module registry of
    Just loaded -> pure loaded.unit
    Nothing -> bug (NoSuchModule closure.func.module)
  stack <- liftEffect (Ref.new [ ClosedBoundary ])
  let machine = { registry, stack, unit, owned: Just owned }
  activation <- activationOf machine closure args
  go machine (Running activation)
  where
  go machine state = case state of
    Finished value -> pure (Right value)
    Halting halt -> pure (Left halt)
    Asking _ _ _ -> bug AskedOutsideInvocation
    _ -> step machine state >>= go machine

-- | Apply a function value to arguments, as a run of its own.
-- |
-- | **This is what the drive loop does with the function a `Bind` holds**
-- | ([Drive](Drive.purs)), and it is the only way the host side enters the
-- | interpreter. A run of its own means a stack of its own: the application makes
-- | one, finishes with it, and the loop goes round again — the two never interleave.
-- |
-- | The callee is a function value rather than a closure in particular, `a -> IO b`
-- | admitting a closure, a partial application, and a continuation alike.
applyFunction :: forall r. Registry -> Value -> P.Array Value -> Run (EVAL r) Value
applyFunction registry callee args = do
  machine <- machineOver registry []
  state <- applyTo machine callee args
  loop machine state

-- | A machine over the registry, its stack holding these entries.
machineOver :: forall r. Registry -> P.Array StackEntry -> Run (EVAL r) Machine
machineOver registry entries = do
  -- every loaded module holds the one `Prim.Unit` the registry assigned, so which
  -- of them it is taken from does not matter
  unit <- case Map.findMin registry of
    Just { value: loaded } -> pure loaded.unit
    Nothing -> bug RegistryEmpty
  stack <- liftEffect (Ref.new entries)
  pure { registry, stack, unit, owned: Nothing }

-- | A run no invocation began, to its value. It holds no root boundary, so no
-- | `perform` of it stops.
loop :: forall r. Machine -> State -> Run (EVAL r) Value
loop = drive

-- Invocations -------------------------------------------------------------------------

-- | How an invocation, or the part of it since it was last resumed, ended.
data Outcome
  = Done Value
  -- | Stopped at a `perform` the root boundary answers, with its argument. The run
  -- | goes on only where the suspension is resumed with the answer.
  | Asked Value Suspension
  -- | Stopped where a closed run reached outside it, as how. The run does not go
  -- | on.
  | Halted Halt
  -- | Stopped because the steps this part was allowed ran out, the run needing
  -- | another. It goes on only where the pause is resumed.
  | Paused Pause

-- | A part of an invocation: how it ended, and how many steps of the machine it
-- | took. **A step is one call of the machine's step**, an administrative
-- | transition — a return reaching an entry, a handler installed — counting as
-- | one like an instruction does. A part allowed `n` steps that reaches its value
-- | or a `perform` at its `n`th has it; one that would need another pauses.
type Slice = { spent :: P.Int, outcome :: Outcome }

-- | A run paused between two steps: the machine and where it stands. Resumed once,
-- | as a suspension is.
newtype Pause = Pause
  { machine :: Machine
  , state :: State
  , resumed :: Ref P.Boolean
  }

-- | A run stopped at a `perform`: the machine, the activation at the instruction
-- | after the `PERF`, and the register the answer belongs in.
-- |
-- | **Nothing but a continuation of the machine is held**, not a continuation
-- | value: the stack is the one the run stopped with, and resuming carries on with
-- | it. So a suspension is resumed once, and a second attempt is refused before it
-- | touches anything. Dropping one abandons the run: the stack and the cells of its
-- | regions become unreachable. **What ran before the stop stays done** — a
-- | foreign's effect on the host is not the machine's to take back.
newtype Suspension = Suspension
  { machine :: Machine
  , activation :: Activation
  , dest :: Reg
  , resumed :: Ref P.Boolean
  }

-- | Apply a function value to arguments, as a run whose root boundary answers the
-- | one operation of `root.key` by stopping.
-- |
-- | The boundary stands below everything the run pushes, so a handler the program
-- | installs for the key answers first, and a `fast` clause's body, which runs
-- | outside the handler that answered, reaches it.
-- |
-- | It runs at most `allowed` steps before it pauses.
invoke :: forall r. Registry -> Root -> P.Int -> Value -> P.Array Value -> Run (EVAL r) Slice
invoke registry root allowed callee args = do
  machine <- machineOver registry [ RootBoundary root ]
  state <- applyTo machine callee args
  driveFor allowed machine state

-- | Apply a function value to arguments, as a run that reaches nothing outside
-- | it. It halts, before anything is carried out, at a `perform` no handler of
-- | the run answers, at a call of a foreign the host carries out, and at an
-- | operation on state the run did not make; an effect it handles itself is not
-- | seen. **The arrays it may reach are those it made**, recorded with the
-- | machine, so a pause and its resumption keep them and the run's end drops them.
-- |
-- | It runs at most `allowed` steps before it pauses.
invokeClosed :: forall r. Registry -> P.Int -> Value -> P.Array Value -> Run (EVAL r) Slice
invokeClosed registry allowed callee args = do
  open <- machineOver registry [ ClosedBoundary ]
  owned <- liftEffect Arr.newOwned
  let machine = open { owned = Just owned }
  state <- applyTo machine callee args
  driveFor allowed machine state

-- | Go on with a stopped run, the answer written where the `PERF` put its value,
-- | for at most `allowed` steps.
resumeWith :: forall r. P.Int -> Suspension -> Value -> Run (EVAL r) Slice
resumeWith allowed (Suspension suspended) answer = do
  once suspended.resumed
  writeReg suspended.activation suspended.dest answer
  driveFor allowed suspended.machine (Running suspended.activation)

-- | Go on with a paused run where it stands, for at most `allowed` steps.
resumePaused :: forall r. P.Int -> Pause -> Run (EVAL r) Slice
resumePaused allowed (Pause paused) = do
  once paused.resumed
  driveFor allowed paused.machine paused.state

-- | That a stopped run goes on for the first time, marked before anything else
-- | is touched.
once :: forall r. Ref P.Boolean -> Run (EVAL r) Unit
once resumed = do
  already <- liftEffect (Ref.read resumed)
  when already (bug SuspensionAlreadyResumed)
  liftEffect (Ref.write true resumed)

-- | Step the machine until the run produces its value, stops at the root, or has
-- | taken `allowed` steps and needs another.
driveFor :: forall r. P.Int -> Machine -> State -> Run (EVAL r) Slice
driveFor allowed machine = go 0
  where
  go spent state = case state of
    Finished value -> pure { spent, outcome: Done value }
    Asking activation dest argument -> do
      resumed <- liftEffect (Ref.new false)
      pure { spent, outcome: Asked argument (Suspension { machine, activation, dest, resumed }) }
    Halting halt -> pure { spent, outcome: Halted halt }
    _
      | spent >= allowed -> do
          resumed <- liftEffect (Ref.new false)
          pure { spent, outcome: Paused (Pause { machine, state, resumed }) }
      | otherwise -> step machine state >>= go (spent + 1)

-- | Step a run no invocation began until it produces its value. Nothing bounds
-- | it, and a root boundary it cannot hold is a defect.
drive :: forall r. Machine -> State -> Run (EVAL r) Value
drive machine state = case state of
  Finished value -> pure value
  Asking _ _ _ -> bug AskedOutsideInvocation
  Halting _ -> bug HaltedOutsideClosedRun
  _ -> step machine state >>= drive machine

-- | One step of the machine.
step :: forall r. Machine -> State -> Run (EVAL r) State
step machine = case _ of
  Finished value -> pure (Finished value)
  -- a stop is the driver's to answer, and a step leaves it where it is
  Asking activation dest argument -> pure (Asking activation dest argument)
  Halting halt -> pure (Halting halt)

  -- a value reaching the bottom of the stack is what the run produces
  Returning value -> do
    entry <- pop machine
    case entry of
      Nothing -> pure (Finished value)
      Just (Resume activation dest) -> do
        writeReg activation dest value
        pure (Running activation)
      Just (ApplyRemaining args) -> applyTo machine value args
      Just (HandlerMarker marker) -> applyTo machine marker.returnClause [ value ]
      -- a region closes as the value passes it
      Just (RegionFrame _) -> pure (Returning value)
      -- a `fast` clause has finished, and its value goes on to the `PERF` below
      Just (ClauseBoundary _) -> pure (Returning value)
      -- the bottom of an invocation, which the value passes on its way out
      Just (RootBoundary _) -> pure (Returning value)
      Just ClosedBoundary -> pure (Returning value)

  -- an activation runs against the tables of its own module, which is the one its
  -- function belongs to
  Running activation -> do
    loaded <- loadedOf machine activation.func.module
    case Array.index activation.node.code activation.ip of
      Just instruction -> do
        next <- exec machine loaded activation instruction
        case next of
          Advance -> pure (Running (resuming activation))
          -- the activation is suspended at the instruction after the call, which
          -- is where the value the call produces is written
          Known dest entered -> do
            push machine (Resume (resuming activation) dest)
            pure (Running entered)
          Unknown dest callee args -> do
            push machine (Resume (resuming activation) dest)
            applyTo machine callee args
          Install dest entries body args -> do
            push machine (Resume (resuming activation) dest)
            pushAll machine entries
            applyTo machine body args
          -- the boundary is measured from where it will stand, the `Resume` below it
          -- being pushed first
          Fast dest clause argument markerAt -> do
            push machine (Resume (resuming activation) dest)
            stack <- liftEffect (Ref.read machine.stack)
            push machine (ClauseBoundary (Array.length stack - markerAt))
            applyTo machine clause [ argument ]
          Moved state -> pure state
          Ask dest argument -> pure (Asking (resuming activation) dest argument)
          Escape key -> pure (Halting (EffectPerformed key))
      Nothing -> transfer machine loaded activation
  where
  resuming activation = activation { ip = activation.ip + 1 }

-- | Apply a value to arguments.
-- |
-- | Every application takes this path: a call instruction, the rest of an
-- | over-application, and a continuation alike.
applyTo :: forall r. Machine -> Value -> P.Array Value -> Run (EVAL r) State
applyTo machine callee args = case callee of
  VClos closure -> applyCallee machine (CalleeClosure closure) args
  -- the arguments a partial application holds stand before the ones it is given
  VPap pap -> applyCallee machine pap.callee (pap.args <> args)
  VCont continuation -> resume machine continuation args
  _ -> bug (NotOfClass ACallable)

-- | Apply a callee to arguments, whichever kind it is.
-- |
-- | **The count decides before the kind does.** Too few arguments build a partial
-- | application over that callee, whatever it is — a foreign and an operation
-- | included, neither of which is carried out until the last argument arrives. Too
-- | many call it with the arity it takes and leave the rest for what comes back.
applyCallee :: forall r. Machine -> Callee -> P.Array Value -> Run (EVAL r) State
applyCallee machine callee args = do
  resolved <- resolve machine callee
  let arity = arityOf resolved
  case compare (Array.length args) arity of
    LT -> pure (Returning (VPap { callee, args }))
    EQ -> saturated machine resolved args
    GT -> do
      push machine (ApplyRemaining (Array.drop arity args))
      saturated machine resolved (Array.take arity args)

-- | A callee with what applying it takes to hand: how many arguments it takes, and
-- | where it is a closure, the function entering it runs. The callee is resolved
-- | once, so a saturated application enters the body without looking it up again.
data Resolved
  = ResolvedClosure Closure Prepared
  | ResolvedCtor CtorId P.Int
  | ResolvedForeign Foreign P.Int
  | ResolvedPrim PrimOp P.Int

resolve :: forall r. Machine -> Callee -> Run (EVAL r) Resolved
resolve machine = case _ of
  CalleeClosure closure -> map (ResolvedClosure closure) (functionOf machine closure)
  CalleeCtor ctor arity -> pure (ResolvedCtor ctor arity)
  CalleeForeign carriedOutBy arity -> pure (ResolvedForeign carriedOutBy arity)
  CalleePrim op -> pure (ResolvedPrim op (arityOfOp op))

arityOf :: Resolved -> P.Int
arityOf = case _ of
  ResolvedClosure _ function -> function.nparams
  ResolvedCtor _ arity -> arity
  ResolvedForeign _ arity -> arity
  ResolvedPrim _ arity -> arity

-- | Carry out a callee that has every argument it takes.
-- |
-- | **A closure is entered directly**: no partial application and no intermediate
-- | function value is built, and nothing stands between the call and the body. What
-- | entering does make is the activation and the registers it runs in, which a call
-- | needs of its own since the caller's are still live under it.
saturated :: forall r. Machine -> Resolved -> P.Array Value -> Run (EVAL r) State
saturated machine resolved args = case resolved of
  ResolvedClosure closure function -> map Running (activationIn closure function args)
  ResolvedCtor ctor _ -> pure (Returning (VData ctor args))
  ResolvedForeign carriedOutBy _ -> carryOutForeign machine carriedOutBy args
  ResolvedPrim op _ -> carryOutOp machine op args

-- | Apply a continuation, which takes one argument.
-- |
-- | The segment is re-pushed and the argument reaches its top, which is the
-- | activation that performed the operation. Arguments past the first are work
-- | pending on what the segment returns, so they stand below it.
resume :: forall r. Machine -> Continuation -> P.Array Value -> Run (EVAL r) State
resume machine continuation args = case Array.uncons args of
  Nothing -> bug NoArgument
  Just { head, tail: rest } -> do
    when (not (Array.null rest)) (push machine (ApplyRemaining rest))
    segment <- liftEffect (reinstate continuation)
    pushAll machine segment
    pure (Returning head)

-- | The function a closure runs.
functionOf :: forall r. Machine -> Closure -> Run (EVAL r) Prepared
functionOf machine closure = do
  loaded <- loadedOf machine closure.func.module
  functionAt loaded closure.func.func

-- | The activation entering a closure makes, resolving the function it runs.
activationOf :: forall r. Machine -> Closure -> P.Array Value -> Run (EVAL r) Activation
activationOf machine closure args = do
  function <- functionOf machine closure
  activationIn closure function args

-- | The same, where the function is already to hand. The arguments occupy the
-- | first `nparams` registers, which is where the function's code reads them.
activationIn :: forall r. Closure -> Prepared -> P.Array Value -> Run (EVAL r) Activation
activationIn closure function args = do
  let given = Array.length args
  when (given /= function.nparams)
    (bug (WrongArgumentCount closure.func.func function.nparams given))
  regs <- liftEffect (Ref.new (Map.fromFoldable (Array.mapWithIndex parameter args)))
  pure
    { func: closure.func
    , closure
    , regs
    , node: function.body
    , ip: 0
    }
  where
  parameter i value = Tuple (Reg i) value

-- | What installing a handler pushes, and the body it then enters.
install
  :: forall r
   . Loaded
  -> Activation
  -> HandlerIx
  -> Reg
  -> Reg
  -> P.Array Reg
  -> Run (EVAL r) { entries :: P.Array StackEntry, body :: Value }
install loaded activation ix body ret clauses = do
  entry <- handlerAt loaded ix
  bodyValue <- readReg activation body
  returnClause <- readReg activation ret
  clauseValues <- traverse (readReg activation) clauses
  when (Array.length clauseValues /= Array.length entry.opClauses)
    (bug (WrongHandlerShape ix))
  let
    marker = HandlerMarker
      { key: entry.key
      , clauses: Array.zipWith clauseOf entry.opClauses clauseValues
      , returnClause
      }
  pure { entries: [ marker ], body: bodyValue }
  where
  clauseOf stated value = { op: stated.op, form: stated.form, clause: value }

-- | What opening a region pushes, the body it then enters, and the identity the
-- | body is applied to: one no other opening has had.
openRegion
  :: forall r
   . Loaded
  -> Activation
  -> RegionIx
  -> Reg
  -> P.Array Reg
  -> Run (EVAL r) { entries :: P.Array StackEntry, body :: Value, identity :: Value }
openRegion loaded activation ix body initial = do
  entry <- regionAt loaded ix
  bodyValue <- readReg activation body
  values <- traverse (readReg activation) initial
  when (Array.length values /= Array.length entry.cells) (bug (WrongRegionShape ix))
  identity <- liftEffect Region.fresh
  cells <- liftEffect (traverse Ref.new values)
  pure
    { entries: [ RegionFrame { identity, cells } ]
    , body: bodyValue
    , identity: VOpaque (Region.toOpaque identity)
    }

-- | The operation an index of the module's `OPS` names.
opAt :: forall r. Loaded -> OpIx -> Run (EVAL r) OpId
opAt loaded ix@(OpIx i) = case Array.index loaded.ops i of
  Just op -> pure op
  Nothing -> bug (NoClauseForOperation ix)

-- | The clause a marker holds for that operation. A handler removing an effect has
-- | one per operation of it, which is what checking a handler establishes.
clauseFor :: forall r. Loaded -> Marker -> OpIx -> Run (EVAL r) Clause
clauseFor loaded marker ix@(OpIx i) = case Array.index loaded.ops i of
  Nothing -> bug (NoClauseForOperation ix)
  Just op -> case Array.find (\clause -> clause.op == op) marker.clauses of
    Just clause -> pure clause
    Nothing -> bug (NoClauseForOperation ix)

-- Tails -----------------------------------------------------------------------------

-- | What ends the node an activation stands in.
transfer :: forall r. Machine -> Loaded -> Activation -> Run (EVAL r) State
transfer machine loaded activation = do
  function <- functionOf machine activation.closure
  case activation.node.tail of
    RET s -> map Returning (readReg activation s)

    BRIF s whenTrue whenFalse -> do
      value <- readReg activation s
      case value of
        VBoolean true -> pure (enters whenTrue)
        VBoolean false -> pure (enters whenFalse)
        _ -> bug (NotOfClass ABoolean)

    -- a constructor value carries the identity the loader resolved, so a dispatch
    -- here reaches values another module built
    BRC s cases fallback -> do
      value <- readReg activation s
      case value of
        VData ctor _ -> do
          selected <- traverse (\one -> map { ctor: _, body: one.body } (ctorAt loaded one.ctor)) cases
          branch (map _.body (Array.find (\one -> one.ctor.id == ctor) selected)) fallback
        _ -> bug (NotOfClass AConstructorValue)

    -- identity of a literal is equality of the value, a `Number`'s bit pattern
    -- deciding and all NaNs taken as one (D37)
    BRL s cases fallback -> do
      value <- readReg activation s
      selected <- traverse (\one -> map { lit: _, body: one.body } (constantAt loaded one.lit)) cases
      case Array.find (\one -> matchesConstant value one.lit) selected of
        Just one -> pure (enters one.body)
        Nothing -> pure (enters fallback)

    BRK s cases fallback -> do
      value <- readReg activation s
      case value of
        VVariant key _ -> do
          selected <- traverse (\one -> map { key: _, body: one.body } (keyAt loaded one.key)) cases
          branch (map _.body (Array.find (\one -> one.key == key) selected)) fallback
        _ -> bug (NotOfClass AVariant)

    -- the writes are a parallel move: every argument is read before any parameter
    -- is written, an argument register being a parameter of the join point it
    -- enters
    JMP name args -> do
      values <- traverse (readReg activation) args
      join <- joinAt function name
      let given = Array.length values
      when (given /= Array.length join.params)
        (bug (WrongJumpArity name (Array.length join.params) given))
      traverse_ (\(Tuple param value) -> writeReg activation param value)
        (Array.zip join.params values)
      pure (enters join.body)

    -- a tail call pushes nothing, so the value the callee returns reaches
    -- whatever this activation's own return would have reached
    TAILK global args -> do
      values <- traverse (readReg activation) args
      map Running (known machine loaded global values)

    TAILU s args -> do
      callee <- readReg activation s
      values <- traverse (readReg activation) args
      applyTo machine callee values

    TAILFFI ix args -> do
      entry <- foreignAt loaded ix
      values <- traverse (readReg activation) args
      carryOutForeign machine entry.carriedOutBy values
    -- in tail position nothing waits for the return clause's value, so no `Resume`
    -- stands below the marker
    TAILHNDL ix body ret clauses -> do
      installed <- install loaded activation ix body ret clauses
      pushAll machine installed.entries
      applyTo machine installed.body []

    TAILRGN ix body initial -> do
      opened <- openRegion loaded activation ix body initial
      pushAll machine opened.entries
      applyTo machine opened.body [ opened.identity ]
  where
  enters node = Running (activation { node = node, ip = 0 })

  branch selected fallback = case selected, fallback of
    Just body, _ -> pure (enters body)
    Nothing, Just body -> pure (enters body)
    Nothing, Nothing -> bug NoBranchTaken

-- Instructions -----------------------------------------------------------------------

exec :: forall r. Machine -> Loaded -> Activation -> Instr -> Run (EVAL r) Next
exec machine loaded activation = case _ of
  LOADK d ix -> do
    constant <- constantAt loaded ix
    advance (writeReg activation d (valueOfConstant constant))

  -- the constructor of a `LOADC` takes no fields, so the value is complete as it
  -- stands
  LOADC d ix -> do
    ctor <- ctorAt loaded ix
    when (ctor.arity /= 0) (bug (WrongCtorArity ctor.id ctor.arity 0))
    advance (writeReg activation d (VData ctor.id []))

  LOADG d ix -> do
    value <- globalAt loaded ix
    advance (writeReg activation d value)

  MOVE d s -> advance (readReg activation s >>= writeReg activation d)

  CAPT d i -> advance (readCapture activation i >>= writeReg activation d)

  -- the closure belongs to the module whose code builds it, and carries the
  -- capture slots that module's function declares
  CLOS d func captured -> do
    values <- traverse (readReg activation) captured
    expectCaptures loaded func (Array.length values)
    captures <- liftEffect (Ref.new (Map.fromFoldable (Array.mapWithIndex Tuple values)))
    advance (writeReg activation d (VClos { func: { module: loaded.id, func }, captures }))

  -- a recursive group allocates every member before any capture list is filled,
  -- which is what a guarded `letrec` needs (D14)
  CLOSN d func slots -> do
    expectCaptures loaded func slots
    captures <- liftEffect (Ref.new Map.empty)
    advance (writeReg activation d (VClos { func: { module: loaded.id, func }, captures }))

  -- a slot is filled once: what a group's members capture of each other is
  -- settled where the group is built
  SETCAP s i source -> do
    closure <- readClosure activation s
    function <- functionOf machine closure
    when (i < 0 || i >= function.ncaptures)
      (bug (CaptureOutOfRange closure.func.func i))
    value <- readReg activation source
    filled <- liftEffect (Ref.read closure.captures)
    when (Map.member i filled) (bug (CaptureAlreadyFilled i))
    advance (liftEffect (Ref.modify_ (Map.insert i value) closure.captures))

  PAP d ix args -> do
    target <- calleeAt loaded ix
    values <- traverse (readReg activation) args
    callee <- calleeOf target
    arity <- map arityOf (resolve machine callee)
    let given = Array.length values
    when (given >= arity) (bug (PapNotBelowArity arity given))
    advance (writeReg activation d (VPap { callee, args: values }))

  CTOR d ix args -> do
    ctor <- ctorAt loaded ix
    values <- traverse (readReg activation) args
    let given = Array.length values
    when (given /= ctor.arity) (bug (WrongCtorArity ctor.id ctor.arity given))
    advance (writeReg activation d (VData ctor.id values))

  -- a known call names a function entry whose arity is settled, so nothing about
  -- it is resolved here: the closure a slot holds is entered with exactly the
  -- arguments it takes (D30)
  CALLK d global args -> do
    values <- traverse (readReg activation) args
    map (Known d) (known machine loaded global values)

  CALLU d s args -> do
    callee <- readReg activation s
    values <- traverse (readReg activation) args
    pure (Unknown d callee values)

  FIELD d s ix i -> do
    ctor <- ctorAt loaded ix
    value <- readReg activation s
    case value of
      VData held fields
        | held /= ctor.id -> bug (CtorMismatch ctor.id held)
        | otherwise -> case Array.index fields i of
            Just field -> advance (writeReg activation d field)
            Nothing -> bug (NoSuchField ctor.id i)
      _ -> bug (NotOfClass AConstructorValue)

  RNEW d -> advance (writeReg activation d (VRecord Map.empty))

  -- a row is sharp, so the key an extension adds is absent from the record it
  -- extends (D4)
  REXT d ix sv sr -> do
    key <- keyAt loaded ix
    value <- readReg activation sv
    record <- readRecord activation sr
    when (Map.member key record) (bug (KeyPresent key))
    advance (writeReg activation d (VRecord (Map.insert key value record)))

  RSEL d ix s -> do
    key <- keyAt loaded ix
    record <- readRecord activation s
    case Map.lookup key record of
      Just value -> advance (writeReg activation d value)
      Nothing -> bug (KeyAbsent key)

  RRES d ix s -> do
    key <- keyAt loaded ix
    record <- readRecord activation s
    when (not (Map.member key record)) (bug (KeyAbsent key))
    advance (writeReg activation d (VRecord (Map.delete key record)))

  RUPD d ix sr sv -> do
    key <- keyAt loaded ix
    record <- readRecord activation sr
    value <- readReg activation sv
    when (not (Map.member key record)) (bug (KeyAbsent key))
    advance (writeReg activation d (VRecord (Map.insert key value record)))

  -- the two rows are disjoint, which is what makes one union of them
  RMRG d s1 s2 -> do
    left <- readRecord activation s1
    right <- readRecord activation s2
    case Array.find (\key -> Map.member key right) (Array.fromFoldable (Map.keys left)) of
      Just key -> bug (KeyPresent key)
      Nothing -> advance (writeReg activation d (VRecord (Map.union left right)))

  VINJ d ix s -> do
    key <- keyAt loaded ix
    value <- readReg activation s
    advance (writeReg activation d (VVariant key value))

  VPAY d ix s -> do
    key <- keyAt loaded ix
    value <- readReg activation s
    case value of
      VVariant held payload
        | held == key -> advance (writeReg activation d payload)
        | otherwise -> bug (KeyAbsent key)
      _ -> bug (NotOfClass AVariant)

  VABS _ _ -> bug Unreachable

  -- a `Base` entry the interpreter claims is carried out by the interpreter, and
  -- what it means is the ABI's
  FFI d ix args -> do
    entry <- foreignAt loaded ix
    values <- traverse (readReg activation) args
    state <- carryOutForeign machine entry.carriedOutBy values
    case state of
      Returning value -> advance (writeReg activation d value)
      Halting halt -> pure (Moved (Halting halt))
      _ -> bug (NotOfClass ACallable)

  -- an operation is a `Base` entry this interpreter carries out itself, and what
  -- each one means is the ABI's ([Op](Op.purs))
  PRIM d ix args -> do
    op <- primAt loaded ix
    values <- traverse (readReg activation) args
    state <- carryOutOp machine op values
    case state of
      Returning value -> advance (writeReg activation d value)
      Halting halt -> pure (Moved (Halting halt))
      _ -> bug (NotOfClass ACallable)
  -- the innermost marker of the key answers, and which reduction applies is the
  -- clause's form (D28); where none does, the root boundary asks the host
  PERF d keyIx opIx s -> do
    key <- keyAt loaded keyIx
    argument <- readReg activation s
    answerer <- answererOf machine key
    case answerer of
      AtRoot root -> do
        op <- opAt loaded opIx
        if op == root.op then pure (Ask d argument) else bug (NoClauseForOperation opIx)
      AtClosed -> pure (Escape key)
      AtMarker at marker -> do
        clause <- clauseFor loaded marker opIx
        case clause.form of
          -- the clause returns to this instruction with its value, its body running
          -- outside the handler and outside what stands above it (D28)
          ClauseFast -> pure (Fast d clause.clause argument at)
          -- the continuation begins at the `perform` and not after it, so this
          -- activation is pushed before the split and is part of the segment
          ClauseFull -> do
            push machine (Resume (activation { ip = activation.ip + 1 }) d)
            segment <- splitAt machine at
            map Moved
              (applyTo machine clause.clause [ argument, VCont (Continuation segment) ])

  HNDL d ix body ret clauses -> do
    installed <- install loaded activation ix body ret clauses
    pure (Install d installed.entries installed.body [])

  RGN d ix body initial -> do
    opened <- openRegion loaded activation ix body initial
    pure (Install d opened.entries opened.body [ opened.identity ])

  CGET d region index -> do
    identity <- readReg activation region
    cell <- cellOf machine identity index
    value <- liftEffect (Ref.read cell)
    advance (writeReg activation d value)

  -- a write has no result of its own, so the destination takes `Prim.Unit`
  CSET d region index s -> do
    identity <- readReg activation region
    cell <- cellOf machine identity index
    value <- readReg activation s
    liftEffect (Ref.write value cell)
    advance (writeReg activation d loaded.unit)
  where
  advance = map (const Advance)

-- | The activation a known call enters. A global slot holds a closure, and the
-- | count of arguments is the arity that closure's function takes.
known :: forall r. Machine -> Loaded -> GlobalIx -> P.Array Value -> Run (EVAL r) Activation
known machine loaded global args = do
  value <- globalAt loaded global
  case value of
    VClos closure -> activationOf machine closure args
    _ -> bug (NotOfClass AClosure)

-- | That a closure carries the capture slots its function declares.
expectCaptures :: forall r. Loaded -> FuncIx -> P.Int -> Run (EVAL r) Unit
expectCaptures loaded func given = do
  function <- functionAt loaded func
  when (given /= function.ncaptures)
    (bug (WrongCaptureCount func function.ncaptures given))

-- | Carry out a foreign, which for a `Base` entry the interpreter claims is
-- | carrying out the operation it stands for, and for anything else is calling the
-- | body the host supplied.
-- |
-- | **Every route to a saturated foreign converges here** — an `FFI`, a `TAILFFI`,
-- | and a partial application whose last argument arrived — so a body is called in
-- | one place and with every argument at once.
-- |
-- | **A host exception is caught and becomes a fault of its own**, kept apart from
-- | a refusal. The two propagate alike, the continuation being discarded entire;
-- | letting one escape instead would end the run outside the fault path, with the
-- | stack undiscarded and a session's promise to outlive a failed entry unkept
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- | Only a throw at this moment is this boundary's: a native action a body returned
-- | is called later, and a throw there is the drive loop's to answer.
carryOutForeign :: forall r. Machine -> Foreign -> P.Array Value -> Run (EVAL r) State
carryOutForeign machine carriedOutBy args = case carriedOutBy of
  ForeignOperation op -> carryOutOp machine op args

  ForeignHosted name _ | Just _ <- machine.owned -> pure (Halting (HostForeignCalled name))
  ForeignHosted name body -> do
    outcome <- liftEffect (try (runEffectFn1 body args))
    case outcome of
      Right (Produced value) -> pure (Returning value)
      Right (Refused reason) -> fault (ForeignRefused name reason)
      Right (Breached what) -> fault (ForeignBreached name what)
      Right (ArgumentNotOfKind position) -> bug (ForeignArgumentNotOfKind name position)
      Left thrown -> fault (ForeignThrew name (message thrown))

  -- **constructing is all either does** (D25): neither performs anything, and the
  -- function a `Bind` holds is not applied here but by the drive loop
  ForeignIO IOPureEntry -> case args of
    [ value ] -> pure (Returning (VIO (IOPure value)))
    _ -> bug (WrongIOArity IOPureEntry (Array.length args))

  ForeignIO IOBindEntry -> case args of
    [ VIO io, k ] -> pure (Returning (VIO (IOBind io k)))
    -- a `.dmo` carries no type, and the first argument of a `bind` that is not an
    -- `IO` is a lowering or an adapter in breach — neither is a failure the ABI
    -- admits, so it is not a fault
    [ _, _ ] -> bug (NotOfClass AnIO)
    _ -> bug (WrongIOArity IOBindEntry (Array.length args))

-- | Carry out an operation, which is a `Base` entry the interpreter claims.
-- |
-- | **Every route to a saturated operation converges here** — a `PRIM`, a partial
-- | application whose last argument arrived, and a `FOREIGNREFS` entry the loader
-- | resolved to the interpreter itself.
-- |
-- | This reaches the host, which the `Base.Array` entries are why: one of them
-- | allocates, one writes, and two read ([Op](Op.purs)). **What it does not do is
-- | catch**, unlike the foreign boundary above: an operation is the interpreter's
-- | own code, so a throw from one is a defect here rather than a failure the ABI
-- | admits, and swallowing it would hide the defect.
carryOutOp :: forall r. Machine -> PrimOp -> P.Array Value -> Run (EVAL r) State
carryOutOp machine op args = case machine.owned, inClosedRunOf op of
  Nothing, _ -> carried
  Just _, Admitted -> carried
  Just _, Withheld -> pure (Halting (OperationWithheld op))
  Just owned, RunLocalState -> do
    reached <- liftEffect (traverse (ownedBy owned) args)
    if Array.all identity reached then do
      state <- carried
      case state of
        Returning (VOpaque o) | Just array <- Arr.fromOpaque o -> liftEffect (Arr.own owned array)
        _ -> pure unit
      pure state
    else pure (Halting (StateNotOwned op))
  where
  -- an array among the operands is one the run made
  ownedBy owned = case _ of
    VOpaque o | Just array <- Arr.fromOpaque o -> Arr.owns owned array
    _ -> pure true

  carried = do
    outcome <- liftEffect (Op.carryOut machine.unit op args)
    case outcome of
      Right value -> pure (Returning value)
      Left (Op.Faulted reason) -> fault reason
      Left Op.WrongOperands -> bug (WrongOperands op)
      Left (Op.NotImplemented _) -> unimplemented "an operation"

-- | The callee a `CALLEES` entry stands for.
calleeOf :: forall r. CalleeTarget -> Run (EVAL r) Callee
calleeOf = case _ of
  TargetGlobal slot -> do
    held <- liftEffect (Ref.read slot)
    case held of
      Just (VClos closure) -> pure (CalleeClosure closure)
      _ -> bug (NotOfClass AClosure)
  TargetCtor ctor arity -> pure (CalleeCtor ctor arity)
  TargetForeign carriedOutBy arity -> pure (CalleeForeign carriedOutBy arity)
  TargetPrim op -> pure (CalleePrim op)

readRecord :: forall r. Activation -> Reg -> Run (EVAL r) (Map.Map KeyId Value)
readRecord activation reg = do
  value <- readReg activation reg
  case value of
    VRecord record -> pure record
    _ -> bug (NotOfClass ARecord)

readClosure :: forall r. Activation -> Reg -> Run (EVAL r) Closure
readClosure activation reg = do
  value <- readReg activation reg
  case value of
    VClos closure -> pure closure
    _ -> bug (NotOfClass AClosure)

derive instance Eq Class
derive instance Generic Class _

instance Show Class where
  show = genericShow

derive instance Eq Bug
derive instance Generic Bug _

instance Show Bug where
  show = genericShow

derive instance Eq Failure
derive instance Generic Failure _

instance Show Failure where
  show = genericShow
