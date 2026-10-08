-- | `lower`, from Mid IR to a `.dmo`.
-- |
-- | It assigns registers, interns what the instructions name into the module's
-- | tables, and turns each function into a tree of instruction sequences.
-- |
-- | **Nothing is optimized, allocated, or checked.** There is no inlining, no
-- | constant folding, and no register allocation: one slot per Mid IR local, and
-- | one more wherever an atom has to reach a register before an instruction can
-- | take it. Totality and arity were established before this stage, and `Rep` is
-- | carried through without being re-derived.
module Stella.Compiler.Bytecode.Lower
  ( LowerError(..)
  , lower
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Primitive (PrimOp)
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ConstIx(..), CtorIx(..), ForeignIx(..), FuncIx(..), GlobalIx(..), HandlerIx(..), Instr(..), Join, JoinName(..), KeyIx(..), Node, OpIx(..), PrimIx(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Instr as B
import Stella.Compiler.Bytecode.Module (CalleeEntry(..), Constant(..), Debug, Dmo, GlobalInit(..), HandlerEntry, Key(..), abiVersion, formatVersion)
import Stella.Compiler.Bytecode.Module as BM
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Stella.Compiler.MiddleEnd.IR as M
import Stella.Compiler.MiddleEnd.Verify (VerifyError, verify)
import Stella.Compiler.TypedCore.Name (Ident, OpName, Qualified)
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type (RowKey(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))

data LowerError
  -- | A Mid IR module that does not hold the invariants a lowering rests on.
  = Unverified VerifyError
  -- | A region key in a term. No erased term carries one.
  | RegionKeyInCode RowKey
  -- | A `region`, `readCell`, or `writeCell`, which this lowering does not
  -- | lower.
  | RegionNotLowered

derive instance Eq LowerError
derive instance Generic LowerError _

instance Show LowerError where
  show = genericShow

-- The state ------------------------------------------------------------------

-- | The tables are the module's and accumulate across it. The registers and the
-- | join points belong to one function and are reset at each.
type LState =
  { constants :: P.Array Constant
  , keys :: P.Array Key
  , ops :: P.Array OpName
  , ctorRefs :: P.Array (Qualified Ident)
  , foreignRefs :: P.Array (Qualified Ident)
  , globalRefs :: P.Array (Qualified Ident)
  , callees :: P.Array CalleeEntry
  , prims :: P.Array PrimOp
  , handlers :: P.Array HandlerEntry
  , nextReg :: P.Int
  , regs :: Map P.Int Rep
  , joins :: P.Array Join
  }

newtype L a = L (LState -> Either LowerError (Tuple a LState))

runL :: forall a. LState -> L a -> Either LowerError (Tuple a LState)
runL s (L f) = f s

instance Functor L where
  map f (L g) = L \s -> case g s of
    Left err -> Left err
    Right (Tuple a s') -> Right (Tuple (f a) s')

instance Apply L where
  apply (L g) (L h) = L \s -> case g s of
    Left err -> Left err
    Right (Tuple f s') -> case h s' of
      Left err -> Left err
      Right (Tuple a s'') -> Right (Tuple (f a) s'')

instance Applicative L where
  pure a = L \s -> Right (Tuple a s)

instance Bind L where
  bind (L g) f = L \s -> case g s of
    Left err -> Left err
    Right (Tuple a s') -> runL s' (f a)

instance Monad L

throw :: forall a. LowerError -> L a
throw err = L \_ -> Left err

-- | A register beyond the ones Mid IR's locals took, for an atom that has to
-- | reach one before an instruction can take it.
freshReg :: Rep -> L Reg
freshReg rep = L \s ->
  Right
    ( Tuple (Reg s.nextReg)
        (s { nextReg = s.nextReg + 1, regs = Map.insert s.nextReg rep s.regs })
    )

addJoin :: Join -> L Unit
addJoin j = L \s -> Right (Tuple unit (s { joins = Array.snoc s.joins j }))

-- | Append unless an equal entry is already there. A table is small and a
-- | reference to it is by index, so what matters is that one entry means one
-- | thing.
intern :: forall a. Eq a => (LState -> P.Array a) -> (P.Array a -> LState -> LState) -> a -> L P.Int
intern get set entry = L \s -> case Array.elemIndex entry (get s) of
  Just i -> Right (Tuple i s)
  Nothing ->
    let
      table = get s
    in
      Right (Tuple (Array.length table) (set (Array.snoc table entry) s))

internConst :: Literal -> L ConstIx
internConst lit = ConstIx <$> intern _.constants (\t s -> s { constants = t }) (constantOf lit)

internKey :: RowKey -> L KeyIx
internKey key = case keyOf key of
  Nothing -> throw (RegionKeyInCode key)
  Just k -> KeyIx <$> intern _.keys (\t s -> s { keys = t }) k

internCtor :: Qualified Ident -> L CtorIx
internCtor name = CtorIx <$> intern _.ctorRefs (\t s -> s { ctorRefs = t }) name

internForeign :: Qualified Ident -> L ForeignIx
internForeign name = ForeignIx <$> intern _.foreignRefs (\t s -> s { foreignRefs = t }) name

internGlobal :: Qualified Ident -> L GlobalIx
internGlobal name = GlobalIx <$> intern _.globalRefs (\t s -> s { globalRefs = t }) name

internCallee :: M.Callee -> L CalleeIx
internCallee callee = CalleeIx <$> intern _.callees (\t s -> s { callees = t }) (calleeOf callee)

internOp :: OpName -> L OpIx
internOp op = OpIx <$> intern _.ops (\t s -> s { ops = t }) op

-- | A handler's entry. Two handlers of one key, one region, and one set of
-- | clauses are one entry: the closures and the cells' initial values are
-- | supplied in registers at the instruction, so an entry holds nothing that
-- | tells two sites apart.
internHandler :: HandlerEntry -> L HandlerIx
internHandler entry = HandlerIx <$> intern _.handlers (\t s -> s { handlers = t }) entry

-- | Every operation the module carries out is recorded, **including one waiting
-- | in a partial application**: target validation reads this table as the use
-- | set, and a backend owes the entry whether the operation runs at once or
-- | after the rest of the arguments arrive.
internPrim :: PrimOp -> L PrimIx
internPrim op = PrimIx <$> intern _.prims (\t s -> s { prims = t }) op

constantOf :: Literal -> Constant
constantOf = case _ of
  LitInt n -> CInt n
  LitNumber n -> CNumber n
  LitString s -> CString s
  LitChar c -> CChar c
  LitBoolean b -> CBoolean b

-- | The key a `.dmo` holds, where the key is one a term carries.
-- |
-- | **A region key is not.** It identifies an element within a row, and erasure
-- | keeps no such element: a handler keeps the key of the element it removes,
-- | its cells keep their own keys, and `readCell` and `writeCell` name those
-- | ([Semantics](../../../../docs/technical-references/03-Typed-Core/06-Semantics.md)).
-- | Nothing reaching here produces one, and the container carries no case for
-- | it rather than a case nothing can be in.
keyOf :: RowKey -> Maybe Key
keyOf = case _ of
  SymbolKey s -> Just (KSymbol s)
  TagKey t -> Just (KTag t)
  PositionKey n -> Just (KPosition n)
  EffectKey e -> Just (KEffect e)
  RegionKey _ -> Nothing

calleeOf :: M.Callee -> CalleeEntry
calleeOf = case _ of
  M.CalleeValue name -> CalleeValue name
  M.CalleeForeign name -> CalleeForeign name
  M.CalleeCtor name -> CalleeCtor name
  M.CalleePrim op -> CalleePrim op

-- Registers ------------------------------------------------------------------

regOfLocal :: M.Local -> Reg
regOfLocal (M.Local n) = Reg n

joinNameOf :: M.JoinId -> JoinName
joinNameOf (M.JoinId n) = JoinName n

-- | What an atom needs before an instruction can take it.
-- |
-- | A local is already in a register. Everything else is loaded into one of its
-- | own, which is where the registers beyond Mid IR's locals come from.
atomReg :: M.Atom -> L { code :: P.Array Instr, reg :: Reg }
atomReg = case _ of
  M.ALocal local -> pure { code: [], reg: regOfLocal local }
  M.ALit lit -> do
    ix <- internConst lit
    reg <- freshReg (repOfLiteral lit)
    pure { code: [ LOADK reg ix ], reg }
  M.AGlobal name -> do
    ix <- internGlobal name
    reg <- freshReg RepVal
    pure { code: [ LOADG reg ix ], reg }
  M.ACtor name -> do
    ix <- internCtor name
    reg <- freshReg RepVal
    pure { code: [ LOADC reg ix ], reg }

repOfLiteral :: Literal -> Rep
repOfLiteral = case _ of
  LitInt _ -> RepInt
  LitNumber _ -> RepNumber
  LitString _ -> RepString
  LitChar _ -> RepChar
  LitBoolean _ -> RepBoolean

atomRegs :: P.Array M.Atom -> L { code :: P.Array Instr, regs :: P.Array Reg }
atomRegs atoms = do
  loaded <- traverse atomReg atoms
  pure { code: Array.concatMap _.code loaded, regs: map _.reg loaded }

-- Computations ---------------------------------------------------------------

-- | A computation, into a register.
comp :: Reg -> M.Comp -> L (P.Array Instr)
comp d = case _ of
  M.CPure atom -> do
    a <- atomReg atom
    pure (a.code <> [ MOVE d a.reg ])

  M.CCallKnown name atoms -> do
    ix <- internGlobal name
    a <- atomRegs atoms
    pure (a.code <> [ CALLK d ix a.regs ])

  M.CCallUnknown callee atoms -> do
    c <- atomReg callee
    a <- atomRegs atoms
    pure (c.code <> a.code <> [ CALLU d c.reg a.regs ])

  M.CPrim op atoms -> do
    ix <- internPrim op
    a <- atomRegs atoms
    pure (a.code <> [ PRIM d ix a.regs ])

  M.CForeign name atoms -> do
    ix <- internForeign name
    a <- atomRegs atoms
    pure (a.code <> [ FFI d ix a.regs ])

  M.CCtor name atoms -> do
    ix <- internCtor name
    a <- atomRegs atoms
    pure (a.code <> [ CTOR d ix a.regs ])

  M.CPap callee atoms -> do
    case callee of
      M.CalleePrim op -> void (internPrim op)
      _ -> pure unit
    ix <- internCallee callee
    a <- atomRegs atoms
    pure (a.code <> [ PAP d ix a.regs ])

  M.CClosure func atoms -> do
    a <- atomRegs atoms
    pure (a.code <> [ CLOS d (funcIxOf func) a.regs ])

  M.CField atom name index -> do
    a <- atomReg atom
    ix <- internCtor name
    pure (a.code <> [ FIELD d a.reg ix index ])

  M.CPayload key atom -> do
    ix <- internKey key
    a <- atomReg atom
    pure (a.code <> [ VPAY d ix a.reg ])

  M.CRecordEmpty -> pure [ RNEW d ]

  M.CRecordExtend key v r -> do
    ix <- internKey key
    a <- atomReg v
    b <- atomReg r
    pure (a.code <> b.code <> [ REXT d ix a.reg b.reg ])

  M.CRecordSelect key atom -> do
    ix <- internKey key
    a <- atomReg atom
    pure (a.code <> [ RSEL d ix a.reg ])

  M.CRecordRestrict key atom -> do
    ix <- internKey key
    a <- atomReg atom
    pure (a.code <> [ RRES d ix a.reg ])

  M.CRecordUpdate key r v -> do
    ix <- internKey key
    a <- atomReg r
    b <- atomReg v
    pure (a.code <> b.code <> [ RUPD d ix a.reg b.reg ])

  M.CRecordMerge l r -> do
    a <- atomReg l
    b <- atomReg r
    pure (a.code <> b.code <> [ RMRG d a.reg b.reg ])

  M.CInject key atom -> do
    ix <- internKey key
    a <- atomReg atom
    pure (a.code <> [ VINJ d ix a.reg ])

  M.CAbsurd atom -> do
    a <- atomReg atom
    pure (a.code <> [ VABS d a.reg ])

  M.CPerform key op atom -> do
    keyIx <- internKey key
    opIx <- internOp op
    a <- atomReg atom
    pure (a.code <> [ PERF d keyIx opIx a.reg ])

  M.CHandle handler func captures -> do
    o <- handlerOperands handler func captures
    pure (o.code <> [ HNDL d o.handler o.body o.returnClause o.opClauses [] ])

  M.CRegion _ _ _ _ -> throw RegionNotLowered

  M.CReadCell _ _ -> throw RegionNotLowered

  M.CWriteCell _ _ _ -> throw RegionNotLowered

-- | What a `HNDL` names: the handler's entry in the module's table, and the
-- | registers its functions arrive in.
-- |
-- | Every closure is built here by an ordinary `CLOS`, in the order the
-- | instruction takes them, so the entry carries no capture list of its own.
handlerOperands
  :: M.Handler
  -> M.FuncId
  -> P.Array M.Atom
  -> L
       { code :: P.Array Instr
       , handler :: HandlerIx
       , body :: Reg
       , returnClause :: Reg
       , opClauses :: P.Array Reg
       }
handlerOperands handler func captures = do
  key <- internKey handler.key
  ops <- traverse (internOp <<< _.op) handler.opClauses
  ix <- internHandler
    { key
    , cells: []
    , opClauses: Array.zipWith (\op oc -> { op, form: oc.form }) ops handler.opClauses
    }
  body <- closureReg func captures
  returnClause <- closureReg handler.returnClause.func handler.returnClause.captures
  clauses <- traverse (\oc -> closureReg oc.clause.func oc.clause.captures) handler.opClauses
  pure
    { code:
        body.code
          <> returnClause.code
          <> Array.concatMap _.code clauses
    , handler: ix
    , body: body.reg
    , returnClause: returnClause.reg
    , opClauses: map _.reg clauses
    }

-- | A closure into a register of its own, which is how a handler's functions
-- | reach the instruction that installs it.
closureReg :: M.FuncId -> P.Array M.Atom -> L { code :: P.Array Instr, reg :: Reg }
closureReg func captures = do
  loaded <- atomRegs captures
  reg <- freshReg RepClos
  pure { code: loaded.code <> [ CLOS reg (funcIxOf func) loaded.regs ], reg }

funcIxOf :: M.FuncId -> FuncIx
funcIxOf (M.FuncId n) = FuncIx n

-- | A computation in tail position.
-- |
-- | **Only a transfer of control has a `Tail` of its own**, a consumer having to
-- | be told not to push a frame for one: a call, and a `handle`, which calls its
-- | body. Everything else is the instruction followed by a `RET`.
-- |
-- | `rep` is the class of the register that holds the value on its way to being
-- | returned, which only the second case needs.
tailComp :: Rep -> M.Comp -> L Node
tailComp rep = case _ of
  M.CCallKnown name atoms -> do
    ix <- internGlobal name
    a <- atomRegs atoms
    pure { code: a.code, tail: TAILK ix a.regs }

  M.CCallUnknown callee atoms -> do
    c <- atomReg callee
    a <- atomRegs atoms
    pure { code: c.code <> a.code, tail: TAILU c.reg a.regs }

  M.CForeign name atoms -> do
    ix <- internForeign name
    a <- atomRegs atoms
    pure { code: a.code, tail: TAILFFI ix a.regs }

  M.CHandle handler func captures -> do
    o <- handlerOperands handler func captures
    pure
      { code: o.code
      , tail: TAILHNDL o.handler o.body o.returnClause o.opClauses []
      }

  other -> do
    d <- freshReg rep
    code <- comp d other
    pure { code, tail: RET d }

-- Expressions ----------------------------------------------------------------

expr :: M.Expr -> L Node
expr = case _ of
  M.ERet atom -> do
    a <- atomReg atom
    pure { code: a.code, tail: RET a.reg }

  M.ELet local _ c rest -> do
    code <- comp (regOfLocal local) c
    node <- expr rest
    pure (node { code = code <> node.code })

  -- every closure of the group is allocated before any capture list is filled,
  -- which is what a member capturing its neighbours requires
  M.ELetRec bindings rest -> do
    let allocate b = CLOSN (regOfLocal b.local) (funcIxOf b.func) (Array.length b.captures)
    fills <- traverse fillCaptures bindings
    node <- expr rest
    pure (node { code = map allocate bindings <> Array.concat fills <> node.code })

  M.ELetJoin joinId params body rest -> do
    definition <- expr body
    addJoin
      { name: joinNameOf joinId
      , params: map (regOfLocal <<< _.local) params
      , body: definition
      }
    expr rest

  M.EJump joinId atoms -> do
    a <- atomRegs atoms
    pure { code: a.code, tail: JMP (joinNameOf joinId) a.regs }

  -- `Val` because `ETail` carries no `Rep`: a call needs none, and a computation
  -- that is not a call takes a register whose class is then unknown
  M.ETail c -> tailComp RepVal c

  M.ESwitchCtor atom branches fallback -> do
    a <- atomReg atom
    cases <- traverse ctorCase branches
    def <- traverse expr fallback
    pure { code: a.code, tail: BRC a.reg cases def }

  M.ESwitchLit atom branches fallback -> do
    a <- atomReg atom
    cases <- traverse litCase branches
    def <- expr fallback
    pure { code: a.code, tail: BRL a.reg cases def }

  M.ESwitchKey atom branches fallback -> do
    a <- atomReg atom
    cases <- traverse keyCase branches
    def <- traverse expr fallback
    pure { code: a.code, tail: BRK a.reg cases def }

  M.EIf atom consequent alternative -> do
    a <- atomReg atom
    c <- expr consequent
    alt <- expr alternative
    pure { code: a.code, tail: BRIF a.reg c alt }

fillCaptures :: M.RecBinding -> L (P.Array Instr)
fillCaptures b = do
  loaded <- traverse atomReg b.captures
  let sets = Array.mapWithIndex (\i l -> SETCAP (regOfLocal b.local) i l.reg) loaded
  pure (Array.concatMap _.code loaded <> sets)

ctorCase :: M.CtorBranch -> L B.CtorCase
ctorCase branch = do
  ix <- internCtor branch.ctor
  body <- expr branch.body
  pure { ctor: ix, body }

litCase :: M.LitBranch -> L B.LitCase
litCase branch = do
  ix <- internConst branch.lit
  body <- expr branch.body
  pure { lit: ix, body }

keyCase :: M.KeyBranch -> L B.KeyCase
keyCase branch = do
  ix <- internKey branch.key
  body <- expr branch.body
  pure { key: ix, body }

-- Functions ------------------------------------------------------------------

-- | One function.
-- |
-- | Mid IR numbers a function's locals from zero, so a slot per local is already
-- | the assignment and nothing is allocated. **Captures are not registers**: one
-- | is read into the slot its local took by a `CAPT` at the head of the body.
function :: M.Function -> L B.Function
function f = L \s ->
  let
    declared = localReps f
    firstFresh = 1 + foldl max (-1) (Array.fromFoldable (Map.keys declared))
    entry = s { nextReg = firstFresh, regs = declared, joins = [] }
  in
    case runL entry (expr f.body) of
      Left err -> Left err
      Right (Tuple node final) ->
        Right
          ( Tuple
              { nparams: Array.length f.params
              , regs: regArray final.regs
              , captures: map _.rep f.captures
              , joins: final.joins
              , body: node { code = captureCode f <> node.code }
              }
              (final { nextReg = s.nextReg, regs = s.regs, joins = s.joins })
          )

captureCode :: M.Function -> P.Array Instr
captureCode f =
  Array.mapWithIndex (\i binder -> CAPT (regOfLocal binder.local) i) f.captures

-- | The `Rep` Mid IR wrote on every binding of a function, by register.
localReps :: M.Function -> Map P.Int Rep
localReps f =
  foldl binder (foldl binder Map.empty f.params) f.captures # \acc -> body acc f.body
  where
  binder acc b = case b.local of M.Local n -> Map.insert n b.rep acc

  body acc = case _ of
    M.ERet _ -> acc
    M.ELet (M.Local n) rep _ rest -> body (Map.insert n rep acc) rest
    M.ELetRec bindings rest ->
      body (foldl (\a b -> case b.local of M.Local n -> Map.insert n b.rep a) acc bindings) rest
    M.ELetJoin _ params definition rest ->
      body (body (foldl binder acc params) definition) rest
    M.EJump _ _ -> acc
    M.ETail _ -> acc
    M.ESwitchCtor _ branches fallback ->
      foldl body (foldl (\a br -> body a br.body) acc branches) (Array.fromFoldable fallback)
    M.ESwitchLit _ branches fallback ->
      body (foldl (\a br -> body a br.body) acc branches) fallback
    M.ESwitchKey _ branches fallback ->
      foldl body (foldl (\a br -> body a br.body) acc branches) (Array.fromFoldable fallback)
    M.EIf _ consequent alternative -> body (body acc consequent) alternative

-- | One `Rep` per register, in order. A slot nothing wrote a `Rep` for takes
-- | `RepVal`, which every consumer already handles.
regArray :: Map P.Int Rep -> P.Array Rep
regArray reps =
  Array.mapWithIndex (\i _ -> fromMaybe RepVal (Map.lookup i reps)) (Array.replicate size unit)
  where
  size = 1 + foldl max (-1) (Array.fromFoldable (Map.keys reps))

-- | The debug table under the bytecode's own indices. A `FuncId` numbers a
-- | function and a `Local` a register directly, so nothing is looked up here:
-- | the keys are rewritten and what they hold carried through.
debugOf :: forall ann. M.Debug ann -> Debug ann
debugOf d =
  { functions: rekey funcIxOf d.functions
  , locals: rekey funcIxOf (map (rekey regOfLocal) d.locals)
  }
  where
  rekey :: forall k l v. Ord k => Ord l => (k -> l) -> Map k v -> Map l v
  rekey f m =
    Map.fromFoldable
      (map (\(Tuple k v) -> Tuple (f k) v) (Map.toUnfoldable m :: P.Array (Tuple k v)))

-- Modules --------------------------------------------------------------------

-- | A Mid IR module and the debug table beside it, lowered to a `.dmo` and the
-- | same table under the indices a `.dmo` names things by.
-- |
-- | **The invariants a lowering rests on are verified first.** Taking a local's
-- | number for a register is only correct where the numbers are what Mid IR says
-- | they are, and filling a gap would put a caller's argument in one slot and
-- | the body's read in another ([Verify](../MidIR/Verify.purs)).
lower
  :: forall ann
   . { module :: M.Module, debug :: M.Debug ann }
  -> Either LowerError { dmo :: Dmo, debug :: Debug ann }
lower input = case verify m of
  Left err -> Left (Unverified err)
  Right _ -> case runL initial (traverse function m.functions) of
    Left err -> Left err
    Right (Tuple functions final) -> Right
      { dmo:
          { formatVersion
          , abiVersion
          , name: m.name
          , imports: m.imports
          , constants: final.constants
          , keys: final.keys
          , ops: final.ops
          , ctors: map ctorEntry m.ctors
          , effects: map effectEntry m.effects
          , foreigns: map foreignEntry m.foreigns
          , ctorRefs: final.ctorRefs
          , foreignRefs: final.foreignRefs
          , globalRefs: final.globalRefs
          , callees: final.callees
          , prims: final.prims
          , handlers: final.handlers
          , functions
          , globals: map globalEntry m.globals
          , exports: m.exports
          }
      , debug: debugOf input.debug
      }
  where
  m = input.module

  initial =
    { constants: []
    , keys: []
    , ops: []
    , ctorRefs: []
    , foreignRefs: []
    , globalRefs: []
    , callees: []
    , prims: []
    , handlers: []
    , nextReg: 0
    , regs: Map.empty
    , joins: []
    }

ctorEntry :: M.CtorEntry -> BM.CtorEntry
ctorEntry e =
  { name: e.ref, owner: e.owner, tag: e.tag, arity: e.arity, isNewtype: e.isNewtype }

effectEntry :: M.EffectEntry -> BM.EffectEntry
effectEntry e = { name: e.ref, ops: e.ops }

foreignEntry :: M.ForeignEntry -> BM.ForeignEntry
foreignEntry e = { name: e.ref, arity: e.arity }

globalEntry :: M.GlobalEntry -> BM.GlobalEntry
globalEntry e =
  { name: e.ref
  , init: case e.init of
      M.GRun func -> GRun (funcIxOf func)
      M.GFunc func -> GFunc (funcIxOf func)
  }
