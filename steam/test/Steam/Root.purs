-- | An invocation's root boundary, written in bytecode by hand: a `perform` it
-- | answers stops the run, and resuming it goes on from the instruction after.
-- |
-- | | Function | What it is |
-- | | --- | --- |
-- | | 0 | asks with 1, asks again with the first answer, and returns the two answers added |
-- | | 1 | a return clause: it returns its argument |
-- | | 2 | a `fast` clause of the root's key: it answers its argument plus 100 |
-- | | 3 | that clause's handler over function 0 |
-- | | 4 | a `fast` clause of the root's key whose body performs the root's operation itself |
-- | | 5 | that clause's handler over function 0 |
-- | | 6 | a `full` clause of another key: it resumes once with its argument |
-- | | 7 | performs the other key's operation, then asks with what it gave |
-- | | 8 | function 6's handler over function 7 |
-- | | 9 | performs the root's key with an operation the root does not answer |
-- | | 10 | performs the other key with no handler of it installed |
-- | | 11 | returns 3 without asking |
module Test.Steam.Root (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Eval (Bug(..), Failure(..), Outcome(..), Pause, Slice, Suspension, applyFunction, invoke, resumePaused, resumeWith)
import Steam.Module (Loaded, Registry, prepare)
import Steam.Value (CtorId(..), KeyId(..), ModuleId(..), OpId(..), Root, Value(..))
import Stella.Compiler.Bytecode.Instr (ConstIx(..), FuncIx(..), Function, HandlerIx(..), Instr(..), KeyIx(..), Node, OpIx(..), PrimIx(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Module (Constant(..))
import Stella.Compiler.MiddleEnd.IR (ClauseForm(..))
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Stella.Compiler.Primitive (PrimOp(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- The fixture ----------------------------------------------------------------------

-- | The key the root answers, and its one operation.
rootKey :: KeyId
rootKey = KeyId 10

rootOp :: OpId
rootOp = OpId 20

-- | Another key, which a `full` handler answers.
otherKey :: KeyId
otherKey = KeyId 12

otherOp :: OpId
otherOp = OpId 21

-- | An operation of the root's key the root does not answer.
strayOp :: OpId
strayOp = OpId 22

root :: Root
root = { key: rootKey, op: rootOp }

returning :: P.Array Instr -> Reg -> Node
returning code reg = { code, tail: RET reg }

fn :: { nparams :: P.Int, nregs :: P.Int } -> Node -> Function
fn counts body =
  { nparams: counts.nparams
  , regs: Array.replicate counts.nregs RepVal
  , captures: []
  , joins: []
  , body
  }

plain :: P.Int -> Node -> Function
plain nregs = fn { nparams: 0, nregs }

-- | A handler of `handler` with the clause `clause` and function 1 for its return
-- | clause, over `body`.
installing :: P.Int -> P.Int -> P.Int -> Function
installing handler clause body = plain 4
  ( returning
      [ CLOS (Reg 0) (FuncIx body) []
      , CLOS (Reg 1) (FuncIx 1) []
      , CLOS (Reg 2) (FuncIx clause) []
      , HNDL (Reg 3) (HandlerIx handler) (Reg 0) (Reg 1) [ Reg 2 ] []
      ]
      (Reg 3)
  )

functions :: P.Array Function
functions =
  -- 0
  [ plain 4
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PERF (Reg 1) (KeyIx 0) (OpIx 0) (Reg 0)
          , PERF (Reg 2) (KeyIx 0) (OpIx 0) (Reg 1)
          , PRIM (Reg 3) (PrimIx 0) [ Reg 1, Reg 2 ]
          ]
          (Reg 3)
      )
  -- 1
  , fn { nparams: 1, nregs: 1 } (returning [] (Reg 0))
  -- 2
  , fn { nparams: 1, nregs: 3 }
      (returning [ LOADK (Reg 1) (ConstIx 1), PRIM (Reg 2) (PrimIx 0) [ Reg 0, Reg 1 ] ] (Reg 2))
  -- 3
  , installing 0 2 0
  -- 4
  , fn { nparams: 1, nregs: 2 } (returning [ PERF (Reg 1) (KeyIx 0) (OpIx 0) (Reg 0) ] (Reg 1))
  -- 5
  , installing 0 4 0
  -- 6
  , fn { nparams: 2, nregs: 3 } (returning [ CALLU (Reg 2) (Reg 1) [ Reg 0 ] ] (Reg 2))
  -- 7
  , plain 3
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PERF (Reg 1) (KeyIx 1) (OpIx 1) (Reg 0)
          , PERF (Reg 2) (KeyIx 0) (OpIx 0) (Reg 1)
          ]
          (Reg 2)
      )
  -- 8
  , installing 1 6 7
  -- 9
  , plain 2 (returning [ LOADK (Reg 0) (ConstIx 0), PERF (Reg 1) (KeyIx 0) (OpIx 2) (Reg 0) ] (Reg 1))
  -- 10
  , plain 2 (returning [ LOADK (Reg 0) (ConstIx 0), PERF (Reg 1) (KeyIx 1) (OpIx 1) (Reg 0) ] (Reg 1))
  -- 11
  , plain 1 (returning [ LOADK (Reg 0) (ConstIx 2) ] (Reg 0))
  ]

-- | The module, with its two handlers: 0 answers the root's key with one `fast`
-- | clause, 1 answers the other key with one `full` clause.
loaded :: Loaded
loaded =
  { id: ModuleId 0
  , constants: [ CInt 1, CInt 100, CInt 3 ]
  , keys: [ rootKey, otherKey ]
  , ops: [ rootOp, otherOp, strayOp ]
  , ctors: []
  , foreigns: []
  , globals: []
  , callees: []
  , prims: [ IntAdd ]
  , handlers:
      [ { key: rootKey, cells: [], opClauses: [ { op: rootOp, form: ClauseFast } ] }
      , { key: otherKey, cells: [], opClauses: [ { op: otherOp, form: ClauseFull } ] }
      ]
  , unit: VData (CtorId 999) []
  , functions: Array.mapMaybe prepared functions
  }
  where
  prepared function = case prepare function of
    Right p -> Just p
    Left _ -> Nothing

registry :: Registry
registry = Map.fromFoldable [ Tuple (ModuleId 0) loaded ]

-- Running --------------------------------------------------------------------------

closureAt :: P.Int -> Aff Value
closureAt i = liftEffect do
  captures <- Ref.new Map.empty
  pure (VClos { func: { module: ModuleId 0, func: FuncIx i }, captures })

-- | Steps enough for anything here to reach its value or a `perform`.
plenty :: P.Int
plenty = 1000000

invoking :: P.Int -> Aff (Either Failure Outcome)
invoking i = map _.outcome <$> invokingFor plenty i

invokingFor :: P.Int -> P.Int -> Aff (Either Failure Slice)
invokingFor allowed i = do
  callee <- closureAt i
  liftEffect (runBaseEffect (Except.runExcept (invoke registry root allowed callee [])))

resuming :: Suspension -> P.Int -> Aff (Either Failure Outcome)
resuming suspension answer = map _.outcome <$> resumingFor plenty suspension answer

resumingFor :: P.Int -> Suspension -> P.Int -> Aff (Either Failure Slice)
resumingFor allowed suspension answer =
  liftEffect (runBaseEffect (Except.runExcept (resumeWith allowed suspension (VInt answer))))

resumingPaused :: P.Int -> Pause -> Aff (Either Failure Slice)
resumingPaused allowed pause = liftEffect (runBaseEffect (Except.runExcept (resumePaused allowed pause)))

-- | Run function `i` in stretches of `quantum` steps, answering each `perform`
-- | with its argument plus 10: the arguments asked with, the value, and the steps
-- | taken in all.
stretched :: P.Int -> P.Int -> Aff { asked :: P.Array P.Int, value :: Seen, spent :: P.Int }
stretched quantum i = invokingFor quantum i >>= go { asked: [], spent: 0 }
  where
  go acc = case _ of
    Left failure -> pure { asked: acc.asked, value: Failed failure, spent: acc.spent }
    Right slice ->
      let
        spent = acc.spent + slice.spent
      in
        case slice.outcome of
          Done (VInt n) -> pure { asked: acc.asked, value: DoneWith n, spent }
          Done _ -> pure { asked: acc.asked, value: Elsewhere, spent }
          Asked (VInt n) suspension -> resumingFor quantum suspension (n + 10) >>= go { asked: Array.snoc acc.asked n, spent }
          Asked _ _ -> pure { asked: acc.asked, value: Elsewhere, spent }
          Paused pause -> resumingPaused quantum pause >>= go { asked: acc.asked, spent }
          Halted _ -> pure { asked: acc.asked, value: Elsewhere, spent }

-- | What an outcome was, as far as a test needs it.
data Seen
  = DoneWith P.Int
  | AskedWith P.Int
  | Failed Failure
  | Elsewhere

seen :: Either Failure Outcome -> Seen
seen = case _ of
  Left failure -> Failed failure
  Right (Done (VInt n)) -> DoneWith n
  Right (Asked (VInt n) _) -> AskedWith n
  Right _ -> Elsewhere

-- | The suspension an outcome stopped with, asked with that argument.
askedWith :: P.Int -> Either Failure Outcome -> Aff Suspension
askedWith wanted = case _ of
  Right (Asked (VInt n) suspension) | n == wanted -> pure suspension
  other -> liftEffect (throw ("stopped otherwise than asking with " <> show wanted <> ": " <> show (seen other)))

spec :: Spec Unit
spec = describe "Steam.Eval, an invocation's root boundary" do
  it "gives the run's value where nothing asks" do
    result <- invoking 11
    seen result `shouldEqual` DoneWith 3

  it "stops at each perform it answers, and goes on from the instruction after with the answer" do
    -- the second perform asks with the first answer, so its argument shows where
    -- the answer was written
    first <- invoking 0 >>= askedWith 1
    second <- resuming first 10 >>= askedWith 10
    result <- resuming second 5
    seen result `shouldEqual` DoneWith 15

  it "lets a handler of the key the program installs answer first" do
    result <- invoking 3
    -- 1 + 100, then 101 + 100
    seen result `shouldEqual` DoneWith 302

  it "is reached from the body of a fast clause, which runs outside the handler that answered" do
    -- the clause performs the operation it answers, which reaches past its own
    -- handler to the root; what the root answers is what the clause returns
    first <- invoking 5 >>= askedWith 1
    second <- resuming first 7 >>= askedWith 7
    result <- resuming second 8
    seen result `shouldEqual` DoneWith 15

  it "is reached from inside a continuation a full handler of another key resumed" do
    first <- invoking 8 >>= askedWith 1
    result <- resuming first 42
    seen result `shouldEqual` DoneWith 42

  it "is resumed once: resuming again after the run went on is refused and changes nothing" do
    first <- invoking 0 >>= askedWith 1
    second <- resuming first 10 >>= askedWith 10
    again <- resuming first 99
    seen again `shouldEqual` Failed (Bug SuspensionAlreadyResumed)
    -- the run is where the second stop left it: the first answer is still 10
    result <- resuming second 5
    seen result `shouldEqual` DoneWith 15

  it "leaves an invocation after an abandoned one untouched" do
    _ <- invoking 0 >>= askedWith 1
    first <- invoking 0 >>= askedWith 1
    second <- resuming first 2 >>= askedWith 2
    result <- resuming second 3
    seen result `shouldEqual` DoneWith 5

  describe "stretches of steps" do
    it "gives the same questions, value, and steps in all, whatever the stretch" do
      for_' [ 0, 5, 8, 11 ] \i -> do
        whole <- stretched plenty i
        for_' [ 1, 2, 3, 7 ] \q -> do
          cut <- stretched q i
          Tuple i cut `shouldEqual` Tuple i whole

    it "allows exactly the steps it is given, a value or a perform at the last one included" do
      whole <- stretched plenty 11
      invokingFor whole.spent 11 >>= \r -> seen (map _.outcome r) `shouldEqual` DoneWith 3
      invokingFor (whole.spent - 1) 11 >>= \r -> paused r `shouldEqual` true
      -- the first perform of function 0, reached after the steps its first stretch took
      first <- invokingFor plenty 0
      case first of
        Right slice -> do
          asked <- invokingFor slice.spent 0
          seen (map _.outcome asked) `shouldEqual` AskedWith 1
          short <- invokingFor (slice.spent - 1) 0
          paused short `shouldEqual` true
        Left failure -> fail (show failure)

    it "resumes a pause once, a second time refused" do
      invokingFor 1 0 >>= case _ of
        Right { outcome: Paused pause } -> do
          once <- resumingPaused plenty pause
          seen (map _.outcome once) `shouldEqual` AskedWith 1
          again <- resumingPaused plenty pause
          seen (map _.outcome again) `shouldEqual` Failed (Bug SuspensionAlreadyResumed)
        _ -> fail "the first stretch did not pause"

  describe "what no .dmo admits" do
    it "an operation of the root's key the root does not answer" do
      result <- invoking 9
      seen result `shouldEqual` Failed (Bug (NoClauseForOperation (OpIx 2)))

    it "a perform of another key with no handler of it installed" do
      result <- invoking 10
      seen result `shouldEqual` Failed (Bug (NoHandlerInstalled otherKey))

    it "a perform of the root's key in a run no invocation began" do
      callee <- closureAt 0
      result <- liftEffect (runBaseEffect (Except.runExcept (applyFunction registry callee [])))
      map (const unit) result `shouldEqual` Left (Bug (NoHandlerInstalled rootKey))

-- | Whether a stretch paused for want of steps.
paused :: Either Failure Slice -> P.Boolean
paused = case _ of
  Right { outcome: Paused _ } -> true
  _ -> false

for_' :: forall a. P.Array a -> (a -> Aff Unit) -> Aff Unit
for_' xs f = void (Array.foldM (\_ x -> f x) unit xs)

derive instance Eq Seen

instance Show Seen where
  show = case _ of
    DoneWith n -> "DoneWith " <> show n
    AskedWith n -> "AskedWith " <> show n
    Failed failure -> "Failed " <> show failure
    Elsewhere -> "Elsewhere"
