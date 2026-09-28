-- | A `.dmo` resolved and cut into segments: the frame strategy's lower IR.
-- |
-- | **Resolution** turns every index into what it names — a key into its
-- | canonical string, an operation into its name, a constructor or a global into a
-- | reference to this module's declaration or to an imported one — and checks what
-- | one module can decide on
-- | its own: that a reference names a module this one imports, that a reference
-- | into this module names a declaration of the kind its table calls for, and that
-- | every call, construction, and partial application of something this module
-- | declares supplies a count its callee admits. What another module declares is
-- | checked where the generated modules are loaded together.
-- |
-- | **Segmentation** cuts each function at its non-tail calls, its performs, and
-- | its handler installations: the run loop carries each out and then continues the
-- | frame at the segment after it ([Frame](Frame.purs)). A `JMP` targets a join
-- | point's own segment, so a loop written with join points runs through the run
-- | loop rather than the host's call stack.
module Stella.Backend.JavaScript.ToFrame
  ( Resolved
  , FrameModule
  , toFrame
  , keyString
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..), note)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ConstIx(..), CtorIx(..), FuncIx(..), GlobalIx(..), HandlerIx(..), Instr(..), JoinName(..), KeyIx(..), Node, OpIx(..), PrimIx(..), Tail(..))
import Stella.Compiler.Bytecode.Instr as B
import Stella.Compiler.Bytecode.Module (Constant(..), Dmo, GlobalInit(..), Key(..))
import Stella.Compiler.Bytecode.Module as M
import Stella.Backend.JavaScript.Error (JsError(..))
import Stella.Backend.JavaScript.Frame (Block, Callee(..), CtorRef(..), Exit(..), Expr(..), FrameFunction, GlobalRef(..), HandleOperands, Handler, Literal(..), Segment, SegmentId(..), Stmt(..), Target(..))
import Stella.Compiler.Primitive (PrimOp, arityOfOp, entryOfOp)
import Stella.Compiler.TypedCore.Domain (codePointOf)
import Stella.Compiler.MiddleEnd.IR (ClauseForm(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), OpName(..), Qualified(..), Symbol(..), Tag(..))

-- | Every index of the module turned into what it names.
type Resolved =
  { keys :: P.Array P.String
  , ctors :: P.Array CtorRef
  , globals :: P.Array GlobalRef
  , callees :: P.Array Callee
  , prims :: P.Array PrimOp
  , handlers :: P.Array Handler
  }

type FrameModule =
  { dmo :: Dmo
  , resolved :: Resolved
  , functions :: P.Array FrameFunction
  }

-- | A key's canonical string: its kind, then what distinguishes it within the
-- | kind. **Two keys are one key exactly where their strings are equal**, across
-- | every module, so a field and a tag of one spelling stay two keys (D16).
keyString :: Key -> P.String
keyString = case _ of
  KSymbol (Symbol s) -> "s:" <> s
  KTag (Tag t) -> "t:" <> t
  KPosition n -> "p:" <> show n
  KEffect (Qualified (ModuleName m) (EffName e)) -> "e:" <> m <> ":" <> e

toFrame :: Dmo -> Either JsError FrameModule
toFrame dmo = do
  resolved <- resolve dmo
  functions <- traverse (\(Tuple i f) -> frameFunction dmo resolved i f)
    (Array.mapWithIndex Tuple dmo.functions)
  pure { dmo, resolved, functions }

-- Resolution -------------------------------------------------------------------------

resolve :: Dmo -> Either JsError Resolved
resolve dmo = do
  ctors <- traverse ctorRef dmo.ctorRefs
  globals <- traverse globalRef dmo.globalRefs
  let
    prims = dmo.prims
    keys = map keyString dmo.keys
    resolvedSoFar = { keys, ctors, globals, callees: [], prims, handlers: [] }
  callees <- traverse (callee resolvedSoFar) dmo.callees
  handlers <- traverse (handler keys) dmo.handlers
  pure resolvedSoFar { callees = callees, handlers = handlers }
  where
  own (Qualified m _) = m == dmo.name

  imported q@(Qualified m _) =
    if Array.elem m dmo.imports then Right unit else Left (NotImported q)

  ctorRef q@(Qualified m name)
    | m == ModuleName "Prim" && name == Ident "Unit" = Right PrimUnit
    | own q = OwnCtor <$> note (NoSuchDeclaration q) (Array.findIndex (\c -> c.name == q) dmo.ctors)
    | otherwise = imported q $> ImportedCtor m name

  globalRef q@(Qualified m name)
    | own q = OwnGlobal <$> note (NoSuchDeclaration q) (Array.findIndex (\g -> g.name == q) dmo.globals)
    | otherwise = imported q $> ImportedGlobal m name

  callee soFar = case _ of
    M.CalleeValue q -> CalleeGlobal <$> globalRef q
    M.CalleeCtor q -> CalleeCtor <$> ctorRef q
    M.CalleeForeign q -> Left (Unsupported ("a partial application of the foreign " <> showName q))
    M.CalleePrim op -> case Array.elemIndex op soFar.prims of
      Just ix -> Right (CalleePrim ix)
      Nothing -> Left (NoSuchIndex "PRIMS" (-1))

  -- a key becomes its canonical string and an operation its name, which is what a
  -- clause is found by once the marker is found by its key
  handler keys entry = do
    key <- keyOf entry.key
    cells <- traverse keyOf entry.cells
    clauses <- traverse clause entry.opClauses
    pure { key, cells, clauses }
    where
    keyOf (KeyIx i) = at "KEYS" keys i

    clause c = do
      let OpIx i = c.op
      OpName op <- at "OPS" dmo.ops i
      pure { op, fast: c.form == ClauseFast }

showName :: Qualified Ident -> P.String
showName (Qualified (ModuleName m) (Ident x)) = m <> "." <> x

-- Arities one module decides ----------------------------------------------------------

-- | The definitional arity of a global this module declares: the parameter count
-- | of the function a `func` entry installs. A `run` entry has none.
ownArity :: Dmo -> P.Int -> Maybe P.Int
ownArity dmo ix = do
  g <- Array.index dmo.globals ix
  case g.init of
    GFunc (FuncIx f) -> _.nparams <$> Array.index dmo.functions f
    GRun _ -> Nothing

ownCtorArity :: Dmo -> P.Int -> Maybe P.Int
ownCtorArity dmo ix = _.arity <$> Array.index dmo.ctors ix

-- | A known call to a global this module declares supplies its definitional arity.
checkKnownCall :: Dmo -> GlobalRef -> P.Int -> Either JsError Unit
checkKnownCall dmo ref count = case ref of
  OwnGlobal ix -> case ownArity dmo ix of
    Just n | n == count -> Right unit
    arity -> Left (ArityMismatch (globalName dmo ix) (arityOr arity) count)
  ImportedGlobal _ _ -> Right unit

-- | A saturated construction supplies the constructor's arity.
checkConstruct :: Dmo -> CtorRef -> P.Int -> Either JsError Unit
checkConstruct dmo ref count = case ref of
  OwnCtor ix -> case ownCtorArity dmo ix of
    Just n | n == count -> Right unit
    arity -> Left (ArityMismatch (ctorName dmo ix) (arityOr arity) count)
  PrimUnit -> if count == 0 then Right unit else Left (ArityMismatch "Prim.Unit" 0 count)
  ImportedCtor _ _ -> Right unit

-- | A partial application supplies fewer arguments than its callee takes, whatever
-- | the callee is.
checkPartial :: Dmo -> Resolved -> Callee -> P.Int -> Either JsError Unit
checkPartial dmo resolved c count = case c of
  CalleeGlobal (OwnGlobal ix) -> case ownArity dmo ix of
    Just n | count < n -> Right unit
    arity -> Left (ArityMismatch (globalName dmo ix) (arityOr arity) count)
  CalleeCtor (OwnCtor ix) -> case ownCtorArity dmo ix of
    Just n | count < n -> Right unit
    arity -> Left (ArityMismatch (ctorName dmo ix) (arityOr arity) count)
  CalleeCtor PrimUnit -> Left (ArityMismatch "Prim.Unit" 0 count)
  CalleePrim ix -> case Array.index resolved.prims ix of
    Just op | count < arityOfOp op -> Right unit
    Just op -> Left (ArityMismatch (showName (entryOfOp op)) (arityOfOp op) count)
    Nothing -> Left (NoSuchIndex "PRIMS" ix)
  _ -> Right unit

arityOr :: Maybe P.Int -> P.Int
arityOr = case _ of
  Just n -> n
  Nothing -> 0

globalName :: Dmo -> P.Int -> P.String
globalName dmo ix = case Array.index dmo.globals ix of
  Just g -> showName g.name
  Nothing -> "global " <> show ix

ctorName :: Dmo -> P.Int -> P.String
ctorName dmo ix = case Array.index dmo.ctors ix of
  Just c -> showName c.name
  Nothing -> "constructor " <> show ix

-- Segmentation ---------------------------------------------------------------------------

type Scope =
  { dmo :: Dmo
  , resolved :: Resolved
  , func :: P.Int
  , joins :: Map P.Int { segment :: SegmentId, params :: P.Array P.Int }
  }

-- | What cutting a node produced: its block, the segments cut out of it, and the
-- | next free segment index.
type Cut =
  { block :: Block
  , segments :: P.Array Segment
  , next :: P.Int
  }

frameFunction :: Dmo -> Resolved -> P.Int -> B.Function -> Either JsError FrameFunction
frameFunction dmo resolved index f = do
  joins <- joinTable
  let
    scope = { dmo, resolved, func: index, joins }
    firstFree = 1 + Array.length f.joins
  entry <- cutNode scope firstFree f.body
  Tuple joinSegments _ <- cutJoins scope entry.next
  pure
    { index
    , name: installedName
    , arity: f.nparams
    , registers: Array.length f.regs
    , entry: segmentId 0
    , segments: [ { id: segmentId 0, body: entry.block } ] <> entry.segments <> joinSegments
    }
  where
  segmentId i = SegmentId { func: index, index: i }

  installedName = do
    g <- Array.find (\g -> initFunc g.init == index) dmo.globals
    pure (showName g.name)

  initFunc = case _ of
    GFunc (FuncIx i) -> i
    GRun (FuncIx i) -> i

  joinTable = Array.foldM addJoin Map.empty (Array.mapWithIndex Tuple f.joins)

  addJoin acc (Tuple i j) = do
    let JoinName name = j.name
    if Map.member name acc then Left (JoinTwice index name)
    else Right (Map.insert name { segment: segmentId (1 + i), params: map regIndex j.params } acc)

  cutJoins scope next0 =
    Array.foldM
      ( \(Tuple acc next) (Tuple i j) -> do
          cut <- cutNode scope next j.body
          pure (Tuple (acc <> [ { id: segmentId (1 + i), body: cut.block } ] <> cut.segments) cut.next)
      )
      (Tuple [] next0)
      (Array.mapWithIndex Tuple f.joins)

regIndex :: B.Reg -> P.Int
regIndex (B.Reg r) = r

regs :: P.Array B.Reg -> P.Array P.Int
regs = map regIndex

-- | Cut a node into the block that runs it, and the segments for what follows each
-- | non-tail call in it.
cutNode :: Scope -> P.Int -> Node -> Either JsError Cut
cutNode scope next0 node = go [] 0
  where
  go acc i = case Array.index node.code i of
    Nothing -> do
      tail <- cutTail scope next0 node.tail
      pure tail { block = tail.block { stmts = acc <> tail.block.stmts } }
    Just instr -> case instr of
      CALLK (B.Reg d) g args -> do
        target <- globalAt scope g
        checkKnownCall scope.dmo target (Array.length args)
        breakAt acc i (TargetGlobal target) (regs args) d
      CALLU (B.Reg d) (B.Reg s) args -> breakAt acc i (TargetReg s) (regs args) d
      PERF (B.Reg d) k op (B.Reg s) -> do
        key <- keyAt scope k
        opName <- opAt scope op
        cutAt acc i \resume -> Perform { key, op: opName, arg: s, dest: d, resume }
      HNDL (B.Reg d) h body ret clauses cells -> do
        handler <- handlerAt scope h
        cutAt acc i \resume -> Handle { handler, operands: handleOperands body ret clauses cells, dest: d, resume }
      _ -> do
        stmt <- instrStmt scope instr
        go (Array.snoc acc stmt) (i + 1)

  breakAt acc i target args dest = cutAt acc i \resume -> Call { target, args, dest, resume }

  -- the rest of the node, from the instruction after the transfer, is a segment of
  -- its own; the transfer ends this block and names it
  cutAt acc i exitTo = do
    let resume = SegmentId { func: scope.func, index: next0 }
    rest <- cutNode scope (next0 + 1) { code: Array.drop (i + 1) node.code, tail: node.tail }
    pure
      { block: { stmts: acc, exit: exitTo resume }
      , segments: [ { id: resume, body: rest.block } ] <> rest.segments
      , next: rest.next
      }

cutTail :: Scope -> P.Int -> Tail -> Either JsError Cut
cutTail scope next0 = case _ of
  RET (B.Reg s) -> leaf (Return s)
  TAILK g args -> do
    target <- globalAt scope g
    checkKnownCall scope.dmo target (Array.length args)
    leaf (TailCall { target: TargetGlobal target, args: regs args })
  TAILU (B.Reg s) args -> leaf (TailCall { target: TargetReg s, args: regs args })
  TAILFFI _ _ -> Left (Unsupported "a tail call to a foreign")
  TAILHNDL h body ret clauses cells -> do
    handler <- handlerAt scope h
    leaf (TailHandle { handler, operands: handleOperands body ret clauses cells })
  JMP (JoinName name) args -> case Map.lookup name scope.joins of
    Nothing -> Left (NoSuchJoin scope.func name)
    Just j ->
      if Array.length j.params /= Array.length args then Left (ArityMismatch ("join point " <> show name) (Array.length j.params) (Array.length args))
      else leaf (Jump { join: j.segment, moves: Array.zip j.params (regs args) })
  BRIF (B.Reg s) yes no -> do
    a <- cutNode scope next0 yes
    b <- cutNode scope a.next no
    pure { block: { stmts: [], exit: If s a.block b.block }, segments: a.segments <> b.segments, next: b.next }
  BRC (B.Reg s) cases default -> do
    Tuple branches acc <- branchesOf cases \c -> ctorAt scope c.ctor
    d <- defaultOf acc default
    pure { block: { stmts: [], exit: SwitchCtor s (map (\b -> { ctor: b.label, body: b.body }) branches) d.block }, segments: d.segments, next: d.next }
  BRL (B.Reg s) cases default -> do
    Tuple branches acc <- branchesOf cases \c -> literalAt scope c.lit
    d <- cutNode scope acc.next default
    pure { block: { stmts: [], exit: SwitchLit s (map (\b -> { lit: b.label, body: b.body }) branches) d.block }, segments: acc.segments <> d.segments, next: d.next }
  BRK (B.Reg s) cases default -> do
    Tuple branches acc <- branchesOf cases \c -> keyAt scope c.key
    d <- defaultOf acc default
    pure { block: { stmts: [], exit: SwitchKey s (map (\b -> { key: b.label, body: b.body }) branches) d.block }, segments: d.segments, next: d.next }
  where
  leaf exit = pure { block: { stmts: [], exit }, segments: [], next: next0 }

  branchesOf :: forall c l. P.Array { body :: Node | c } -> ({ body :: Node | c } -> Either JsError l) -> Either JsError (Tuple (P.Array { label :: l, body :: Block }) { segments :: P.Array Segment, next :: P.Int })
  branchesOf cases labelOf =
    Array.foldM
      ( \(Tuple bs acc) c -> do
          label <- labelOf c
          cut <- cutNode scope acc.next c.body
          pure (Tuple (Array.snoc bs { label, body: cut.block }) { segments: acc.segments <> cut.segments, next: cut.next })
      )
      (Tuple [] { segments: [], next: next0 })
      cases

  defaultOf acc = case _ of
    Nothing -> pure { block: Nothing, segments: acc.segments, next: acc.next }
    Just n -> do
      cut <- cutNode scope acc.next n
      pure { block: Just cut.block, segments: acc.segments <> cut.segments, next: cut.next }

instrStmt :: Scope -> Instr -> Either JsError Stmt
instrStmt scope = case _ of
  LOADK (B.Reg d) c -> Set d <<< Lit <$> literalAt scope c
  LOADG (B.Reg d) g -> Set d <<< Global <$> globalAt scope g
  LOADC (B.Reg d) c -> do
    ref <- ctorAt scope c
    checkConstruct scope.dmo ref 0
    pure (Set d (CtorValue ref))
  MOVE (B.Reg d) (B.Reg s) -> pure (Set d (Reg s))
  CAPT (B.Reg d) i -> pure (Set d (Capture i))
  CLOS (B.Reg d) f args -> do
    ix <- funcAt scope f
    pure (Set d (Closure ix (regs args)))
  CLOSN (B.Reg d) f n -> do
    ix <- funcAt scope f
    pure (Set d (OpenClosure ix n))
  SETCAP (B.Reg d) i (B.Reg s) -> pure (SetCapture d i s)
  PAP (B.Reg d) c args -> do
    target <- calleeAt scope c
    checkPartial scope.dmo scope.resolved target (Array.length args)
    pure (Set d (Pap target (regs args)))
  CTOR (B.Reg d) c args -> do
    ref <- ctorAt scope c
    checkConstruct scope.dmo ref (Array.length args)
    pure (Set d (Construct ref (regs args)))
  FIELD (B.Reg d) (B.Reg s) c j -> do
    ref <- ctorAt scope c
    pure (Set d (Field s ref j))
  RNEW (B.Reg d) -> pure (Set d RecordEmpty)
  REXT (B.Reg d) k (B.Reg v) (B.Reg r) -> do
    key <- keyAt scope k
    pure (Set d (RecordExtend key v r))
  RSEL (B.Reg d) k (B.Reg s) -> do
    key <- keyAt scope k
    pure (Set d (RecordSelect key s))
  RRES (B.Reg d) k (B.Reg s) -> do
    key <- keyAt scope k
    pure (Set d (RecordRestrict key s))
  RUPD (B.Reg d) k (B.Reg r) (B.Reg v) -> do
    key <- keyAt scope k
    pure (Set d (RecordUpdate key r v))
  RMRG (B.Reg d) (B.Reg a) (B.Reg b) -> pure (Set d (RecordMerge a b))
  VINJ (B.Reg d) k (B.Reg s) -> do
    key <- keyAt scope k
    pure (Set d (Inject key s))
  VPAY (B.Reg d) k (B.Reg s) -> do
    key <- keyAt scope k
    pure (Set d (Payload key s))
  VABS _ _ -> pure (Unreachable "absurd reached a value")
  PRIM (B.Reg d) p args -> do
    op <- primAt scope p
    when (Array.length args /= arityOfOp op)
      (Left (ArityMismatch (showName (entryOfOp op)) (arityOfOp op) (Array.length args)))
    pure (Set d (Prim op (regs args)))
  FFI _ _ _ -> Left (Unsupported "a foreign call")
  CGET (B.Reg d) k -> do
    key <- keyAt scope k
    pure (Set d (CellGet key))
  CSET (B.Reg d) k (B.Reg s) -> do
    key <- keyAt scope k
    pure (Set d (CellSet key s))
  CALLK _ _ _ -> Left (Unsupported "a call standing where no segment can be cut")
  CALLU _ _ _ -> Left (Unsupported "a call standing where no segment can be cut")
  PERF _ _ _ _ -> Left (Unsupported "a perform standing where no segment can be cut")
  HNDL _ _ _ _ _ _ -> Left (Unsupported "a handler standing where no segment can be cut")

handleOperands :: B.Reg -> B.Reg -> P.Array B.Reg -> P.Array B.Reg -> HandleOperands
handleOperands body ret clauses cells =
  { body: regIndex body, ret: regIndex ret, clauses: regs clauses, cells: regs cells }

-- Table lookups ----------------------------------------------------------------------------

at :: forall a. P.String -> P.Array a -> P.Int -> Either JsError a
at table xs i = note (NoSuchIndex table i) (Array.index xs i)

literalAt :: Scope -> ConstIx -> Either JsError Literal
literalAt scope (ConstIx i) = literalOf <$> at "CONSTANTS" scope.dmo.constants i
  where
  literalOf = case _ of
    CInt n -> LitInt n
    CNumber x -> LitNumber x
    CString s -> LitString s
    CChar c -> LitChar (codePointOf c)
    CBoolean b -> LitBoolean b

keyAt :: Scope -> KeyIx -> Either JsError P.String
keyAt scope (KeyIx i) = at "KEYS" scope.resolved.keys i

ctorAt :: Scope -> CtorIx -> Either JsError CtorRef
ctorAt scope (CtorIx i) = at "CTORREFS" scope.resolved.ctors i

globalAt :: Scope -> GlobalIx -> Either JsError GlobalRef
globalAt scope (GlobalIx i) = at "GLOBALREFS" scope.resolved.globals i

calleeAt :: Scope -> CalleeIx -> Either JsError Callee
calleeAt scope (CalleeIx i) = at "CALLEES" scope.resolved.callees i

opAt :: Scope -> OpIx -> Either JsError P.String
opAt scope (OpIx i) = do
  OpName op <- at "OPS" scope.dmo.ops i
  pure op

handlerAt :: Scope -> HandlerIx -> Either JsError P.Int
handlerAt scope (HandlerIx i) = at "HANDLERS" scope.resolved.handlers i $> i

primAt :: Scope -> PrimIx -> Either JsError PrimOp
primAt scope (PrimIx i) = at "PRIMS" scope.resolved.prims i

funcAt :: Scope -> FuncIx -> Either JsError P.Int
funcAt scope (FuncIx i) = at "FUNCTIONS" scope.dmo.functions i $> i
