-- | The invariants of Mid IR, checked.
-- |
-- | Translation is obliged to produce these and a later pass to preserve them.
-- | None of it re-derives anything the Core type checker established: what is
-- | checked here is what a consumer reads off the module without looking
-- | further, above all the **layout of a function's registers** and the **scope
-- | of every name**, which a lowering assigns and resolves by taking a number
-- | for a slot.
-- |
-- | Paving over a breach would be worse than reporting one. A parameter at local
-- | 2 with one parameter is not an imprecision: a caller places its argument in
-- | the first slot and the body reads the third, and the program computes
-- | something else.
-- |
-- | **What one module cannot decide is not decided here.** The arity of an
-- | imported constructor, foreign, or global belongs to the module that declares
-- | it, and a consumer checks it where the modules are together
-- | ([Bytecode](../../../../docs/technical-references/05-Backend/01-Bytecode.md)).
-- | Every reference this module does declare is checked.
module Stella.Compiler.MiddleEnd.Verify
  ( VerifyError(..)
  , verify
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Primitive (PrimOp, arityOfOp)
import Stella.Compiler.MiddleEnd.IR as M
import Stella.Compiler.TypedCore.Name (Ident, OpName, Qualified, TyName)
import Stella.Compiler.TypedCore.Type (RowKey)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl, traverse_)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))

data VerifyError
  -- | A function whose place in the table is not its identifier, as the place
  -- | and the identifier. A consumer reaches a function by index, so an entry
  -- | out of place is reached under another's name.
  = FunctionOutOfPlace P.Int M.FuncId
  -- | A global naming a function the table does not hold.
  | GlobalFunctionMissing (Qualified Ident) M.FuncId
  -- | A global whose function captures something. Initialization installs one
  -- | over an empty capture list, there being nothing yet to capture.
  | GlobalTakesCaptures (Qualified Ident) M.FuncId
  -- | A global evaluated at initialization whose function takes parameters.
  | RunTakesParameters (Qualified Ident) M.FuncId
  -- | A local bound twice in one function, which leaves one binding reading
  -- | what the other wrote.
  | DuplicateLocal M.FuncId M.Local
  -- | A function whose locals are not `0 … n-1`, naming the number missing. A
  -- | lowering takes a local's number for a register, so a gap displaces every
  -- | slot after it.
  | LocalsNotDense M.FuncId P.Int
  -- | A parameter outside the first slots, naming it. A caller places its
  -- | arguments in those and nowhere else.
  | ParameterOutOfPlace M.FuncId M.Local
  -- | A capture outside the slots after the parameters, naming it.
  | CaptureOutOfPlace M.FuncId M.Local
  -- | A local read where nothing binds it — never bound in the function, or
  -- | bound in a branch that does not enclose the read.
  | LocalNotInScope M.FuncId M.Local
  -- | A jump to a join point no enclosing scope declares.
  | JoinNotInScope M.FuncId M.JoinId
  -- | A jump supplying the wrong number of arguments, as the join point's and
  -- | the jump's.
  | JoinArity M.FuncId M.JoinId P.Int P.Int
  -- | A join point declared twice in one function. A lowering puts them in one
  -- | flat table, so the second leaves a jump with two destinations.
  | DuplicateJoin M.FuncId M.JoinId
  -- | A closure naming a function the table does not hold, as the site's
  -- | function and the one named.
  | UnknownFunction M.FuncId M.FuncId
  -- | A closure supplying a number of captures the function does not take, as
  -- | the function's and the site's.
  | CaptureCount M.FuncId M.FuncId P.Int P.Int
  -- | A function reached at an arity its form does not have, as the form's and
  -- | the function's: no parameters for the body of a `handle`, two for a
  -- | `full` clause, and one for a `fast` clause, for a return clause, and for
  -- | the body of a `region`.
  | ClauseArity M.FuncId M.FuncId P.Int P.Int
  -- | A handler naming one operation twice.
  | DuplicateOperation M.FuncId OpName
  -- | A region naming one cell key twice. A region's keys are distinct, and a
  -- | repeat leaves two cells where the layout declares one.
  | DuplicateCell M.FuncId RowKey
  -- | A region whose initial values do not match its keys, as the keys' count
  -- | and the values'. A cell takes the initial value at its own position, so a
  -- | disagreement leaves a cell with none or a value with no cell.
  | CellCount M.FuncId P.Int P.Int
  -- | A cell named by a negative position.
  | NegativeCell M.FuncId P.Int
  -- | A saturated call, constructor, foreign, or operation whose arguments do
  -- | not match the declared arity, as the declaration's and the site's.
  | CallArity M.FuncId (Qualified Ident) P.Int P.Int
  | CtorArity M.FuncId (Qualified Ident) P.Int P.Int
  | ForeignArity M.FuncId (Qualified Ident) P.Int P.Int
  | PrimArity M.FuncId PrimOp P.Int P.Int
  -- | A `callk` or a `pap` over a global that is evaluated at initialization
  -- | rather than installed as a function. Its definitional arity is absent,
  -- | and absent is not zero.
  | NoDefinitionalArity M.FuncId (Qualified Ident)
  -- | A partial application supplying the callee's arity or more, as the
  -- | arity and what was supplied. Saturating one is a call.
  | PapSaturated M.FuncId P.Int P.Int
  -- | A projection of a field the constructor does not have, naming the index.
  | FieldOutOfRange M.FuncId (Qualified Ident) P.Int
  -- | A dispatch whose branches name constructors of more than one type.
  | BranchOwnerMismatch M.FuncId (Qualified TyName)
  -- | A dispatch naming one constructor twice.
  | DuplicateBranch M.FuncId (Qualified Ident)
  -- | A dispatch with no default that leaves a constructor of the type with no
  -- | destination.
  | BranchesNotExhaustive M.FuncId (Qualified TyName)

derive instance Eq VerifyError
derive instance Generic VerifyError _

instance Show VerifyError where
  show = genericShow

-- | What the module declares, indexed as the walk reads it.
type Ctx =
  { functions :: Map M.FuncId M.Function
  , ctors :: Map (Qualified Ident) M.CtorEntry
  , owners :: Map (Qualified TyName) (Set (Qualified Ident))
  , foreigns :: Map (Qualified Ident) P.Int
  , globals :: Map (Qualified Ident) M.GlobalInit
  }

-- | What is in scope at a point in one function's body.
type Env =
  { func :: M.FuncId
  , locals :: Set P.Int
  , joins :: Map M.JoinId P.Int
  }

verify :: M.Module -> Either VerifyError Unit
verify m = do
  table m
  traverse_ (global ctx) m.globals
  traverse_ (function ctx) m.functions
  where
  ctx =
    { functions: Map.fromFoldable (map (\f -> Tuple f.id f) m.functions)
    , ctors: Map.fromFoldable (map (\c -> Tuple c.ref c) m.ctors)
    , owners: foldl owner Map.empty m.ctors
    , foreigns: Map.fromFoldable (map (\f -> Tuple f.ref f.arity) m.foreigns)
    , globals: Map.fromFoldable (map (\g -> Tuple g.ref g.init) m.globals)
    }

  owner acc c =
    Map.alter
      (Just <<< Set.insert c.ref <<< fromMaybeSet)
      c.owner
      acc

  fromMaybeSet = case _ of
    Just s -> s
    Nothing -> Set.empty

-- | A function's identifier is its place in the table, which is what lets a
-- | lowering number the two alike. Two functions of one identifier cannot both
-- | stand at it, so this rejects a repeat as well.
table :: M.Module -> Either VerifyError Unit
table m = traverse_ place (Array.mapWithIndex Tuple m.functions)
  where
  place (Tuple i f)
    | f.id == M.FuncId i = Right unit
    | otherwise = Left (FunctionOutOfPlace i f.id)

-- | Initialization reaches a function directly, so the entry it names exists
-- | and takes what initialization supplies: nothing.
global :: Ctx -> M.GlobalEntry -> Either VerifyError Unit
global ctx g = case g.init of
  M.GRun func -> do
    f <- named func
    parameterless f
    uncaptured f
  M.GFunc func -> named func >>= uncaptured
  where
  named func = case Map.lookup func ctx.functions of
    Nothing -> Left (GlobalFunctionMissing g.ref func)
    Just f -> Right f

  parameterless f
    | Array.null f.params = Right unit
    | otherwise = Left (RunTakesParameters g.ref f.id)

  uncaptured f
    | Array.null f.captures = Right unit
    | otherwise = Left (GlobalTakesCaptures g.ref f.id)

function :: Ctx -> M.Function -> Either VerifyError Unit
function ctx f = do
  bound <- collect f
  dense f bound
  placed f
  uniqueJoins f
  expr ctx { func: f.id, locals: declared, joins: Map.empty } f.body
  where
  declared = Set.fromFoldable (map (number <<< _.local) (f.params <> f.captures))

-- Layout -----------------------------------------------------------------------

-- | Every local a function binds, rejecting one bound twice.
collect :: M.Function -> Either VerifyError (P.Array P.Int)
collect f = do
  let declared = map (number <<< _.local) (f.params <> f.captures)
  inBody <- body f.body
  let all = declared <> inBody
  case duplicate all of
    Just n -> Left (DuplicateLocal f.id (M.Local n))
    Nothing -> Right all
  where
  body = case _ of
    M.ERet _ -> Right []
    M.ELet local _ _ rest -> map (Array.cons (number local)) (body rest)
    M.ELetRec bindings rest ->
      map (append (map (number <<< _.local) bindings)) (body rest)
    M.ELetJoin _ params definition rest -> do
      a <- body definition
      b <- body rest
      Right (map (number <<< _.local) params <> a <> b)
    M.EJump _ _ -> Right []
    M.ETail _ -> Right []
    M.ESwitchCtor _ branches fallback -> branches' (map _.body branches) fallback
    M.ESwitchLit _ branches fallback -> branches' (map _.body branches) (Just fallback)
    M.ESwitchKey _ branches fallback -> branches' (map _.body branches) fallback
    M.EIf _ consequent alternative -> branches' [ consequent ] (Just alternative)

  branches' bodies fallback =
    map Array.concat (traverse body (bodies <> Array.fromFoldable fallback))

-- | A join point is declared once in a function. Scope alone would let an inner
-- | `letjoin` shadow an outer one, but a lowering puts the join points of a
-- | function in one flat table, so the second declaration would leave a jump
-- | with two destinations. Nothing requires the numbering to be dense.
uniqueJoins :: M.Function -> Either VerifyError Unit
uniqueJoins f = case duplicate (body f.body) of
  Just j -> Left (DuplicateJoin f.id j)
  Nothing -> Right unit
  where
  body = case _ of
    M.ERet _ -> []
    M.ELet _ _ _ rest -> body rest
    M.ELetRec _ rest -> body rest
    M.ELetJoin j _ definition rest -> [ j ] <> body definition <> body rest
    M.EJump _ _ -> []
    M.ETail _ -> []
    M.ESwitchCtor _ branches fallback -> branches' (map _.body branches) fallback
    M.ESwitchLit _ branches fallback -> branches' (map _.body branches) (Just fallback)
    M.ESwitchKey _ branches fallback -> branches' (map _.body branches) fallback
    M.EIf _ consequent alternative -> branches' [ consequent ] (Just alternative)

  branches' bodies fallback =
    Array.concat (map body (bodies <> Array.fromFoldable fallback))

number :: M.Local -> P.Int
number (M.Local n) = n

duplicate :: forall a. Ord a => P.Array a -> Maybe a
duplicate xs = (foldl step { seen: Set.empty, found: Nothing } xs).found
  where
  step acc x = case acc.found of
    Just _ -> acc
    Nothing
      | Set.member x acc.seen -> acc { found = Just x }
      | otherwise -> acc { seen = Set.insert x acc.seen }

-- | The locals of a function are `0 … n-1`, which is what lets a lowering take
-- | a number for a slot.
dense :: M.Function -> P.Array P.Int -> Either VerifyError Unit
dense f bound
  | Array.null bound = Right unit
  | otherwise = traverse_ present (Array.range 0 (Array.length bound - 1))
      where
      held = Set.fromFoldable bound
      present n
        | Set.member n held = Right unit
        | otherwise = Left (LocalsNotDense f.id n)

-- | The parameters come first and the captures after them.
placed :: M.Function -> Either VerifyError Unit
placed f = do
  traverse_ param (Array.mapWithIndex Tuple f.params)
  traverse_ capture (Array.mapWithIndex Tuple f.captures)
  where
  nparams = Array.length f.params

  param (Tuple i binder)
    | number binder.local == i = Right unit
    | otherwise = Left (ParameterOutOfPlace f.id binder.local)

  capture (Tuple i binder)
    | number binder.local == nparams + i = Right unit
    | otherwise = Left (CaptureOutOfPlace f.id binder.local)

-- Scope, references, and arities -------------------------------------------------

bindLocal :: Env -> M.Local -> Env
bindLocal env local = env { locals = Set.insert (number local) env.locals }

expr :: Ctx -> Env -> M.Expr -> Either VerifyError Unit
expr ctx env = case _ of
  M.ERet a -> atom ctx env a

  M.ELet local _ c rest -> do
    comp ctx env c
    expr ctx (bindLocal env local) rest

  -- every member of the group is allocated before any capture list is filled,
  -- so a capture may name any of them
  M.ELetRec bindings rest -> do
    let env' = foldl (\acc b -> bindLocal acc b.local) env bindings
    traverse_ (\b -> closure ctx env' b.func b.captures) bindings
    expr ctx env' rest

  -- a join point is in scope in its own definition, which is what lets one
  -- stand for a loop
  M.ELetJoin j params definition rest -> do
    let env' = env { joins = Map.insert j (Array.length params) env.joins }
    expr ctx (foldl (\acc p -> bindLocal acc p.local) env' params) definition
    expr ctx env' rest

  M.EJump j args -> case Map.lookup j env.joins of
    Nothing -> Left (JoinNotInScope env.func j)
    Just arity
      | arity == Array.length args -> traverse_ (atom ctx env) args
      | otherwise -> Left (JoinArity env.func j arity (Array.length args))

  M.ETail c -> comp ctx env c

  M.ESwitchCtor a branches fallback -> do
    atom ctx env a
    ctorBranches ctx env (map _.ctor branches) fallback
    traverse_ (\b -> expr ctx env b.body) branches
    traverse_ (expr ctx env) fallback

  M.ESwitchLit a branches fallback -> do
    atom ctx env a
    traverse_ (\b -> expr ctx env b.body) branches
    expr ctx env fallback

  M.ESwitchKey a branches fallback -> do
    atom ctx env a
    traverse_ (\b -> expr ctx env b.body) branches
    traverse_ (expr ctx env) fallback

  M.EIf a consequent alternative -> do
    atom ctx env a
    expr ctx env consequent
    expr ctx env alternative

atom :: Ctx -> Env -> M.Atom -> Either VerifyError Unit
atom ctx env = case _ of
  M.ALocal local
    | Set.member (number local) env.locals -> Right unit
    | otherwise -> Left (LocalNotInScope env.func local)
  M.ALit _ -> Right unit
  M.AGlobal _ -> Right unit
  M.ACtor name -> declaredArity ctx.ctors _.arity name \arity ->
    if arity == 0 then Right unit else Left (CtorArity env.func name arity 0)

comp :: Ctx -> Env -> M.Comp -> Either VerifyError Unit
comp ctx env = case _ of
  M.CPure a -> atom ctx env a

  M.CCallKnown name args -> do
    traverse_ (atom ctx env) args
    case Map.lookup name ctx.globals of
      -- a global of another module: its definitional arity is that module's
      Nothing -> Right unit
      Just (M.GRun _) -> Left (NoDefinitionalArity env.func name)
      Just (M.GFunc func) -> case Map.lookup func ctx.functions of
        Nothing -> Left (UnknownFunction env.func func)
        Just f -> exactly (Array.length f.params) (Array.length args)
          (CallArity env.func name)

  M.CCallUnknown callee args -> do
    atom ctx env callee
    traverse_ (atom ctx env) args

  M.CPrim op args -> do
    traverse_ (atom ctx env) args
    exactly (arityOfOp op) (Array.length args) (PrimArity env.func op)

  M.CForeign name args -> do
    traverse_ (atom ctx env) args
    declaredArity ctx.foreigns identity name \arity ->
      exactly arity (Array.length args) (ForeignArity env.func name)

  M.CCtor name args -> do
    traverse_ (atom ctx env) args
    declaredArity ctx.ctors _.arity name \arity ->
      exactly arity (Array.length args) (CtorArity env.func name)

  M.CPap callee args -> do
    traverse_ (atom ctx env) args
    arity <- calleeArity ctx env callee
    case arity of
      Nothing -> Right unit
      Just n
        | Array.length args < n -> Right unit
        | otherwise -> Left (PapSaturated env.func n (Array.length args))

  M.CClosure func captures -> closure ctx env func captures

  M.CField a ctorName index -> do
    atom ctx env a
    declaredArity ctx.ctors _.arity ctorName \arity ->
      if index >= 0 && index < arity then Right unit
      else Left (FieldOutOfRange env.func ctorName index)

  M.CPayload _ a -> atom ctx env a
  M.CRecordEmpty -> Right unit
  M.CRecordExtend _ a1 a2 -> atom ctx env a1 *> atom ctx env a2
  M.CRecordSelect _ a -> atom ctx env a
  M.CRecordRestrict _ a -> atom ctx env a
  M.CRecordUpdate _ a1 a2 -> atom ctx env a1 *> atom ctx env a2
  M.CRecordMerge a1 a2 -> atom ctx env a1 *> atom ctx env a2
  M.CInject _ a -> atom ctx env a
  M.CAbsurd a -> atom ctx env a
  M.CPerform _ _ a -> atom ctx env a

  -- how many cells the region has is not a property of this function: the
  -- identity may have been captured, and the Core type checker established that
  -- the cell is one the region declares
  M.CReadCell region index -> do
    atom ctx env region
    cellPosition env index
  M.CWriteCell region index a -> do
    atom ctx env region
    cellPosition env index
    atom ctx env a

  M.CRegion keys func captures initial -> do
    clause ctx env 1 func captures
    traverse_ (atom ctx env) initial
    case duplicate keys of
      Just key -> Left (DuplicateCell env.func key)
      Nothing -> Right unit
    exactly (Array.length keys) (Array.length initial) (CellCount env.func)

  M.CHandle handler func captures -> do
    clause ctx env 0 func captures
    clause ctx env 1 handler.returnClause.func handler.returnClause.captures
    case duplicate (map _.op handler.opClauses) of
      Just op -> Left (DuplicateOperation env.func op)
      Nothing -> Right unit
    traverse_
      (\oc -> clause ctx env (formArity oc.form) oc.clause.func oc.clause.captures)
      handler.opClauses

cellPosition :: Env -> P.Int -> Either VerifyError Unit
cellPosition env index
  | index >= 0 = Right unit
  | otherwise = Left (NegativeCell env.func index)

-- | The captures a closure supplies are in scope, and the function it names
-- | takes exactly them.
closure :: Ctx -> Env -> M.FuncId -> P.Array M.Atom -> Either VerifyError Unit
closure ctx env func captures = do
  traverse_ (atom ctx env) captures
  case Map.lookup func ctx.functions of
    Nothing -> Left (UnknownFunction env.func func)
    Just f -> exactly (Array.length f.captures) (Array.length captures)
      (CaptureCount env.func func)

-- | A function a handler reaches, which has the arity its form gives it.
clause :: Ctx -> Env -> P.Int -> M.FuncId -> P.Array M.Atom -> Either VerifyError Unit
clause ctx env arity func captures = do
  closure ctx env func captures
  case Map.lookup func ctx.functions of
    Nothing -> Left (UnknownFunction env.func func)
    Just f -> exactly arity (Array.length f.params) (ClauseArity env.func func)

formArity :: M.ClauseForm -> P.Int
formArity = case _ of
  M.ClauseFull -> 2
  M.ClauseFast -> 1

-- | The arity of a partial application's callee, where this module states it.
-- | A name it does not declare belongs to a module that does.
calleeArity :: Ctx -> Env -> M.Callee -> Either VerifyError (Maybe P.Int)
calleeArity ctx env = case _ of
  M.CalleePrim op -> Right (Just (arityOfOp op))
  M.CalleeCtor name -> Right (map _.arity (Map.lookup name ctx.ctors))
  M.CalleeForeign name -> Right (Map.lookup name ctx.foreigns)
  M.CalleeValue name -> case Map.lookup name ctx.globals of
    Nothing -> Right Nothing
    Just (M.GRun _) -> Left (NoDefinitionalArity env.func name)
    Just (M.GFunc func) ->
      Right (map (Array.length <<< _.params) (Map.lookup func ctx.functions))

-- | Check against an arity this module declares. A name it does not declare
-- | belongs to a module that does, and is checked where they are together.
declaredArity
  :: forall v
   . Map (Qualified Ident) v
  -> (v -> P.Int)
  -> Qualified Ident
  -> (P.Int -> Either VerifyError Unit)
  -> Either VerifyError Unit
declaredArity declarations arityOf name k = case Map.lookup name declarations of
  Nothing -> Right unit
  Just v -> k (arityOf v)

exactly :: P.Int -> P.Int -> (P.Int -> P.Int -> VerifyError) -> Either VerifyError Unit
exactly expected supplied err
  | expected == supplied = Right unit
  | otherwise = Left (err expected supplied)

-- | A dispatch names constructors of one type, each once, and either has a
-- | default or leaves none of that type without a destination.
ctorBranches
  :: Ctx
  -> Env
  -> P.Array (Qualified Ident)
  -> Maybe M.Expr
  -> Either VerifyError Unit
ctorBranches ctx env names fallback = do
  case duplicate names of
    Just name -> Left (DuplicateBranch env.func name)
    Nothing -> Right unit
  -- a constructor of another module carries its type's own constructors there
  case traverse (\n -> Map.lookup n ctx.ctors) names of
    Nothing -> Right unit
    Just entries -> case Array.head entries of
      Nothing -> Right unit
      Just first -> do
        traverse_ (sameOwner first.owner) entries
        covers first.owner
  where
  sameOwner owner entry
    | entry.owner == owner = Right unit
    | otherwise = Left (BranchOwnerMismatch env.func owner)

  covers owner = case fallback, Map.lookup owner ctx.owners of
    Just _, _ -> Right unit
    Nothing, Nothing -> Right unit
    Nothing, Just all
      | Set.subset all (Set.fromFoldable names) -> Right unit
      | otherwise -> Left (BranchesNotExhaustive env.func owner)
