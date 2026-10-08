-- | `HNDL`, `PERF`, `RGN`, and the cells of a region, written in bytecode by hand.
-- |
-- | The fixture stands for one effect of one operation. Two handlers of it are
-- | written: one whose clause is `fast` and reads and writes a cell, and one whose
-- | clause is `full` and holds the continuation. A region of one cell is opened
-- | around a handler, and its body is applied to the region's identity, which every
-- | closure using the cell captures.
-- |
-- | | Function | What it is |
-- | | --- | --- |
-- | | 0 | a body that performs the operation once and returns what comes back |
-- | | 1 | a body that performs it twice and returns the second value |
-- | | 2 | the return clause: it returns its argument |
-- | | 3 | a `fast` clause: it reads the cell, writes the argument, and returns what it read |
-- | | 4 | a `full` clause: it applies the continuation once |
-- | | 5 | a `full` clause: it applies the continuation twice and returns the two answers added |
-- | | 6 | a `full` clause: it returns without resuming |
-- | | 7 | a return clause that reads the cell |
-- |
-- | The functions after those open the region, install one of the handlers over one
-- | of the bodies, or both.
module Test.Steam.Handlers (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Eval (Bug(..), Failure(..), enter)
import Steam.Module (Loaded, Registry, prepare)
import Steam.Value (Closure, CtorId(..), KeyId(..), ModuleId(..), OpId(..), Value(..))
import Stella.Compiler.Bytecode.Instr (ConstIx(..), FuncIx(..), Function, HandlerIx(..), Instr(..), KeyIx(..), Node, OpIx(..), PrimIx(..), Reg(..), RegionIx(..), Tail(..))
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.Bytecode.Module (Constant(..))
import Stella.Compiler.MiddleEnd.IR (ClauseForm(..))
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- The fixture ----------------------------------------------------------------------

-- | The key of the effect, and the key of the one cell the region has.
effectKey :: KeyId
effectKey = KeyId 10

cellKey :: KeyId
cellKey = KeyId 11

-- | The key of a second effect, which one handler of the fixture does not answer.
otherKey :: KeyId
otherKey = KeyId 12

nextOp :: OpId
nextOp = OpId 20

-- | The operation of that second effect.
stopOp :: OpId
stopOp = OpId 21

returning :: P.Array Instr -> Reg -> Node
returning code reg = { code, tail: RET reg }

fn :: { nparams :: P.Int, nregs :: P.Int, ncaptures :: P.Int } -> Node -> Function
fn counts body =
  { nparams: counts.nparams
  , regs: Array.replicate counts.nregs RepVal
  , captures: Array.replicate counts.ncaptures RepVal
  , joins: []
  , body
  }

plain :: P.Int -> Node -> Function
plain nregs = fn { nparams: 0, nregs, ncaptures: 0 }

-- | The body of a region: applied to the region's identity, it installs the
-- | handler given over the body given, the return clause and the clause closing
-- | over the identity where they read the cell.
installing :: { handler :: P.Int, body :: P.Int, returnClause :: P.Int, clause :: P.Int } -> Function
installing h = fn { nparams: 1, nregs: 5, ncaptures: 0 }
  ( returning
      [ CLOS (Reg 1) (FuncIx h.body) []
      , CLOS (Reg 2) (FuncIx h.returnClause) (overCell h.returnClause)
      , CLOS (Reg 3) (FuncIx h.clause) (overCell h.clause)
      , HNDL (Reg 4) (HandlerIx h.handler) (Reg 1) (Reg 2) [ Reg 3 ]
      ]
      (Reg 4)
  )
  where
  -- the clauses that read the cell, whose one capture is the identity
  overCell f = if Array.elem f [ 3, 7, 21 ] then [ Reg 0 ] else []

-- | A function opening the region, its cell holding the constant given, around the
-- | function given.
opening :: P.Int -> P.Int -> Function
opening initial body = plain 3
  ( returning
      [ CLOS (Reg 0) (FuncIx body) []
      , LOADK (Reg 1) (ConstIx initial)
      , RGN (Reg 2) (RegionIx 0) (Reg 0) [ Reg 1 ]
      ]
      (Reg 2)
  )

-- | A function installing the handler given, its return clause handing the answer
-- | back, over the function given.
handling :: P.Int -> P.Int -> P.Int -> Function
handling handler clause body = plain 4
  ( returning
      [ CLOS (Reg 0) (FuncIx body) []
      , CLOS (Reg 1) (FuncIx 2) []
      , CLOS (Reg 2) (FuncIx clause) []
      , HNDL (Reg 3) (HandlerIx handler) (Reg 0) (Reg 1) [ Reg 2 ]
      ]
      (Reg 3)
  )

functions :: P.Array Function
functions =
  -- 0: perform once, return what the operation gave
  [ plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PERF (Reg 1) (KeyIx 0) (OpIx 0) (Reg 0)
          ]
          (Reg 1)
      )

  -- 1: perform twice, return the second value
  , plain 3
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PERF (Reg 1) (KeyIx 0) (OpIx 0) (Reg 0)
          , PERF (Reg 2) (KeyIx 0) (OpIx 0) (Reg 0)
          ]
          (Reg 2)
      )

  -- 2: a return clause that hands back what reached it
  , fn { nparams: 1, nregs: 1, ncaptures: 0 } (returning [] (Reg 0))

  -- 3: a `fast` clause: what it returns is what the cell held, and the cell takes
  -- the operation's argument
  , fn { nparams: 1, nregs: 4, ncaptures: 1 }
      ( returning
          [ CAPT (Reg 1) 0
          , CGET (Reg 2) (Reg 1) 0
          , CSET (Reg 3) (Reg 1) 0 (Reg 0)
          ]
          (Reg 2)
      )

  -- 4: a `full` clause: the argument, then the continuation applied to it once
  , fn { nparams: 2, nregs: 3, ncaptures: 0 }
      (returning [ CALLU (Reg 2) (Reg 1) [ Reg 0 ] ] (Reg 2))

  -- 5: a `full` clause applying the continuation twice, with a different value each
  -- time, and returning the two answers added: what each application produced is
  -- what the body computed from the value that application resumed with
  , fn { nparams: 2, nregs: 6, ncaptures: 0 }
      ( returning
          [ CALLU (Reg 2) (Reg 1) [ Reg 0 ]
          , LOADK (Reg 3) (ConstIx 2)
          , CALLU (Reg 4) (Reg 1) [ Reg 3 ]
          , PRIM (Reg 5) (PrimIx 0) [ Reg 2, Reg 4 ]
          ]
          (Reg 5)
      )

  -- 6: a `full` clause that never resumes
  , fn { nparams: 2, nregs: 3, ncaptures: 0 }
      (returning [ LOADK (Reg 2) (ConstIx 2) ] (Reg 2))

  -- 7: a return clause whose answer is what the cell holds
  , fn { nparams: 1, nregs: 3, ncaptures: 1 }
      (returning [ CAPT (Reg 1) 0, CGET (Reg 2) (Reg 1) 0 ] (Reg 2))

  -- 8: the counting handler over the body that performs twice, the return clause
  -- reading the cell
  , installing { handler: 0, body: 1, returnClause: 7, clause: 3 }

  -- 9: the region around that, the cell starting at 0
  , opening 1 8

  -- 10: the counting handler over the body that performs twice, the return clause
  -- handing the body's value back
  , installing { handler: 0, body: 1, returnClause: 2, clause: 3 }

  -- 11: the region around that
  , opening 1 10

  -- 12: a handler whose clause is `full` and resumes once, over the body that
  -- performs once
  , handling 1 4 0

  -- 13: the same with the clause that resumes twice
  , handling 1 5 0

  -- 14: the same with the clause that never resumes
  , handling 1 6 0

  -- 15: the region opened in tail position around a body installing the counting
  -- handler in tail position, the return clause reading the cell
  , plain 2
      { code:
          [ CLOS (Reg 0) (FuncIx 16) []
          , LOADK (Reg 1) (ConstIx 1)
          ]
      , tail: TAILRGN (RegionIx 0) (Reg 0) [ Reg 1 ]
      }

  -- 16: that body
  , fn { nparams: 1, nregs: 4, ncaptures: 0 }
      { code:
          [ CLOS (Reg 1) (FuncIx 1) []
          , CLOS (Reg 2) (FuncIx 7) [ Reg 0 ]
          , CLOS (Reg 3) (FuncIx 3) [ Reg 0 ]
          ]
      , tail: TAILHNDL (HandlerIx 0) (Reg 1) (Reg 2) [ Reg 3 ]
      }

  -- 17: a `perform` with no handler of its key installed
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PERF (Reg 1) (KeyIx 0) (OpIx 0) (Reg 0)
          ]
          (Reg 1)
      )

  -- 18: a body that performs nothing
  , plain 1 (returning [ LOADK (Reg 0) (ConstIx 2) ] (Reg 0))

  -- 19: the counting handler over that, the return clause reading the cell
  , installing { handler: 0, body: 18, returnClause: 7, clause: 3 }

  -- 20: the region around that
  , opening 1 19

  -- 21: a `full` clause of a handler inside the region: it resumes, writes the cell,
  -- resumes again, and adds what the two applications produced
  , fn { nparams: 2, nregs: 8, ncaptures: 1 }
      ( returning
          [ CALLU (Reg 2) (Reg 1) [ Reg 0 ]
          , LOADK (Reg 3) (ConstIx 2)
          , CAPT (Reg 4) 0
          , CSET (Reg 5) (Reg 4) 0 (Reg 3)
          , CALLU (Reg 6) (Reg 1) [ Reg 0 ]
          , PRIM (Reg 7) (PrimIx 0) [ Reg 2, Reg 6 ]
          ]
          (Reg 7)
      )

  -- 22: that handler over the body that performs once, the return clause reading
  -- the cell
  , installing { handler: 1, body: 0, returnClause: 7, clause: 21 }

  -- 23: the region around that, the cell starting at 5
  , opening 3 22

  -- 24: the counting handler over the body that performs once, so that installed
  -- inside another handler of the key, two markers of one key stand on the stack
  , installing { handler: 0, body: 0, returnClause: 2, clause: 3 }

  -- 25: the region around that
  , opening 1 24

  -- 26: the `full` handler that answers 9 without resuming, installed over that:
  -- the inner handler is the one that answers, so this one never hears of it
  , handling 1 6 25

  -- 27: a body performing the operation of the second effect
  , plain 2
      ( returning
          [ LOADK (Reg 0) (ConstIx 0)
          , PERF (Reg 1) (KeyIx 2) (OpIx 1) (Reg 0)
          ]
          (Reg 1)
      )

  -- 28: the counting handler, which answers the first effect, over that
  , installing { handler: 0, body: 27, returnClause: 2, clause: 3 }

  -- 29: the region around that
  , opening 1 28

  -- 30: a handler of the second effect over that, which is where the operation the
  -- inner handler does not answer arrives
  , handling 2 6 29

  -- 31: the body of a region inside the handled computation: it performs, adds what
  -- came back to the cell, and returns what the cell then holds
  , fn { nparams: 1, nregs: 7, ncaptures: 0 }
      ( returning
          [ LOADK (Reg 1) (ConstIx 0)
          , PERF (Reg 2) (KeyIx 0) (OpIx 0) (Reg 1)
          , CGET (Reg 3) (Reg 0) 0
          , PRIM (Reg 4) (PrimIx 0) [ Reg 3, Reg 2 ]
          , CSET (Reg 5) (Reg 0) 0 (Reg 4)
          , CGET (Reg 6) (Reg 0) 0
          ]
          (Reg 6)
      )

  -- 32: the region around that, the cell starting at 10
  , opening 4 31

  -- 33: the `full` handler resuming twice, over that
  , handling 1 5 32
  ]

-- | The module, with the handlers its code installs and the one region it opens.
-- |
-- | | Handler | What it is |
-- | | --- | --- |
-- | | 0 | one `fast` clause |
-- | | 1 | one `full` clause |
-- | | 2 | one `full` clause of the second effect |
loaded :: Loaded
loaded =
  { id: ModuleId 0
  , constants: [ CInt 1, CInt 0, CInt 9, CInt 5, CInt 10 ]
  , keys: [ effectKey, cellKey, otherKey ]
  , ops: [ nextOp, stopOp ]
  , ctors: []
  , foreigns: []
  , globals: []
  , callees: []
  , prims: [ IntAdd ]
  , handlers:
      [ { key: effectKey, opClauses: [ { op: nextOp, form: ClauseFast } ] }
      , { key: effectKey, opClauses: [ { op: nextOp, form: ClauseFull } ] }
      , { key: otherKey, opClauses: [ { op: stopOp, form: ClauseFull } ] }
      ]
  , regions: [ { cells: [ cellKey ] } ]
  , unit: VData (CtorId 999) []
  , functions: Array.mapMaybe prepared functions
  }
  where
  prepared function = case prepare function of
    Right p -> Just p
    Left _ -> Nothing

registry :: Registry
registry = Map.fromFoldable [ Tuple (ModuleId 0) loaded ]

closureOf :: P.Int -> Effect Closure
closureOf i = do
  captures <- Ref.new Map.empty
  pure { func: { module: ModuleId 0, func: FuncIx i }, captures }

runs :: P.Int -> Aff (Either Failure Value)
runs i = liftEffect do
  closure <- closureOf i
  runBaseEffect (Except.runExcept (enter registry closure []))

-- | What a run produced, as far as a test needs it.
data Held
  = AnInt P.Int
  | Elsewhere

held :: Either Failure Value -> Either Failure Held
held = map case _ of
  VInt n -> AnInt n
  _ -> Elsewhere

spec :: Spec Unit
spec = describe "Steam.Handlers" do

  describe "a fast clause and a region of cells" do
    it "returns what the cell held, and the write is seen by the next perform" do
      -- the body performs twice with the argument 1; the cell starts at 0, so the
      -- first perform gives 0 and the second gives 1
      result <- runs 11
      held result `shouldEqual` Right (AnInt 1)

    it "leaves the region open while the return clause runs" do
      -- the region stands around the handler, so the return clause reads what the
      -- second perform left in the cell
      result <- runs 9
      held result `shouldEqual` Right (AnInt 1)

    it "leaves it open the same way where both stand in tail position" do
      result <- runs 15
      held result `shouldEqual` Right (AnInt 1)

    it "leaves it open where the body performs nothing" do
      result <- runs 20
      held result `shouldEqual` Right (AnInt 0)

  describe "a full clause" do
    it "resumes the computation the perform was in" do
      -- the clause applies the continuation to the operation's argument, so the
      -- body's `perform` gives 1 and the body returns it
      result <- runs 12
      held result `shouldEqual` Right (AnInt 1)

    it "resumes it as often as it applies the continuation, each from the capture" do
      -- the clause resumes with 1 and then with 9, and adds what the two
      -- applications produced: each ran the body from where the `perform` stood
      -- (D33)
      result <- runs 13
      held result `shouldEqual` Right (AnInt 10)

    it "may answer without resuming at all" do
      result <- runs 14
      held result `shouldEqual` Right (AnInt 9)

  describe "a full clause and a region" do
    it "reaches the one frame of a region around the handler from every application" do
      -- the frame stands below the marker, outside what the continuation holds: the
      -- clause writes 9 into the cell between the two resumptions, and the return
      -- clause each resumption reaches reads the cell — 5 the first time and 9 the
      -- second
      result <- runs 23
      held result `shouldEqual` Right (AnInt 14)

    it "gives each application a copy of a region inside the computation it resumes" do
      -- the region opened inside the handled computation is part of the segment, so
      -- each resumption starts from the cell as it was at the capture, 10: one adds
      -- 1 and the other 9, so 11 + 19. A region the two shared gives 11 + 20
      result <- runs 33
      held result `shouldEqual` Right (AnInt 30)

  describe "handlers that nest" do
    it "answers at the innermost marker of the key" do
      -- two markers of one key stand on the stack. The counting handler is the inner
      -- one, and its `fast` clause answers with what its cell held, which is 0; had
      -- the outer `full` clause answered, the run would have produced its 9
      result <- runs 26
      held result `shouldEqual` Right (AnInt 0)

    it "carries an operation the inner handler does not answer to the outer one" do
      -- the inner handler answers the first effect and the body performs the second,
      -- so the marker that answers is the outer one, which returns 9 without
      -- resuming
      result <- runs 30
      held result `shouldEqual` Right (AnInt 9)

  describe "what no .dmo admits" do
    it "a perform with no handler of its key installed" do
      -- effect safety rules this out: a handler of the key encloses every `perform`
      -- of it
      result <- runs 17
      held result `shouldEqual` Left (Bug (NoHandlerInstalled effectKey))

derive instance Eq Held

instance Show Held where
  show = case _ of
    AnInt n -> "AnInt " <> show n
    Elsewhere -> "Elsewhere"
