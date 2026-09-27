-- | Executing an `IO`
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | Reduction halts once it has constructed an `IO` value (D25), and this is what
-- | runs one. **It is a second entry point and not a step of evaluation**: nothing
-- | in the instruction set reaches it, an `FFI` constructing an `IO` writes that
-- | value into a register and the evaluation continues past it. Which of the two a
-- | mode uses is the mode's business.
-- |
-- | **Applying the function of a `Bind` is the one way the host side enters the
-- | interpreter**, and each application is a run of its own ([Eval](Eval.purs)).
module Steam.Drive
  ( DRIVE
  , execute
  ) where

import Prelude

import Prim as P

import Control.Promise (toAff)
import Data.Either (Either(..))
import Data.List (List(..), (:))
import Effect.Aff (attempt)
import Effect.Exception (message, try)
import Run (AFF, Run, liftAff, liftEffect)
import Steam.Eval (Bug(..), EVAL, Failure(..), applyFunction)
import Steam.Fault (Fault(..))
import Steam.Module (Registry)
import Steam.Value (ActionOutcome(..), IOValue(..), NativeAction, Value(..))
import Run.Except as Except
import Type.Row (type (+))

-- | Executing reaches the host and may wait, which evaluation never does.
type DRIVE r = (AFF + EVAL r)

-- | Run an `IO` value to the value it produces, or to what ended it.
-- |
-- | **The loop is iterative and holds its own stack of pending functions**, and
-- | this is an obligation rather than a preference. A `Bind` chain has no bound and
-- | the shape a program builds is the left-nested one — `m >>= f >>= g` is
-- | `Bind (Bind m f) g` — so executing the outermost descends through every one
-- | before anything runs. An executor written as a recursive function descends the
-- | host's own call stack and dies on a chain long enough, and every short chain
-- | passes.
-- |
-- | What the pending stack holds is functions and not activations: applying one
-- | enters the interpreter, which makes a stack of its own and has finished with it
-- | before the loop goes round again.
execute :: forall r. Registry -> IOValue -> Run (DRIVE r) Value
execute registry initial = descend Nil initial
  where
  -- push and go inward, which is where an executor holding its pending functions
  -- in host frames would have gone down the host's stack instead
  descend pending io = case io of
    IOBind inner k -> descend (k : pending) inner
    IOPure value -> deliver pending value
    IONative action -> perform action >>= deliver pending

  deliver pending value = case pending of
    -- nothing is waiting, so this is the answer
    Nil -> pure value
    k : rest -> do
      produced <- applyFunction registry k [ value ]
      case produced of
        VIO next -> descend rest next
        -- `k` has type `a -> IO b`, but a `.dmo` carries no type and a hosted
        -- foreign may be in breach of its own, so this is not assumed. The culprit
        -- is a lowering or an adapter and the machine cannot tell which, which is
        -- why it is the class that says the defect is above the interpreter rather
        -- than a fault
        _ -> Except.throw (Bug NotAnIOFromContinuation)

-- a cons list and not an array: a chain is descended one `Bind` at a time, and an
-- array would copy the whole of what is pending at every one of them

-- | Perform one action, awaiting it where it says it must be awaited.
-- |
-- | **Whether an action is asynchronous is the action's to say.** Nothing here asks
-- | whether what came back is thenable: such a test would misread a value the host
-- | gave a `then` field, and would make a synchronous action pay for an asynchrony
-- | it does not have.
-- |
-- | **A throw where the action is performed is caught**, as one from a foreign body
-- | is: letting it escape would end the run outside the fault path, with the stack
-- | undiscarded. Performing is calling, an `Effect` being a host function of no
-- | arguments, so the call itself is inside the `try`.
perform :: forall r. NativeAction -> Run (DRIVE r) Value
perform action = do
  outcome <- liftEffect (try action)
  case outcome of
    Left thrown -> faults (NativeThrew (message thrown))
    Right (ActionProduced value) -> pure value
    Right (ActionRefused reason) -> faults (NativeRefused reason)
    Right (ActionAwaiting promise) -> do
      resolved <- liftAff (attempt (toAff promise))
      case resolved of
        -- the asynchronous form of the same breach, reported apart from the throw
        Left rejected -> faults (NativeRejected (message rejected))
        Right (ActionProduced value) -> pure value
        Right (ActionRefused reason) -> faults (NativeRefused reason)
        -- a second wait is a body in breach rather than a chain to unroll
        Right (ActionAwaiting _) -> faults NativeAwaitedTwice
  where
  faults :: forall a. Fault -> Run (DRIVE r) a
  faults = Except.throw <<< Faults
