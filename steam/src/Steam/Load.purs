-- | Loading a module into the registry
-- | ([Abstract Machine](../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- |
-- | **Steam resolves no module.** What it is given is what it loads, and in the
-- | order it is given: a module's `imports` is read as a condition — every one of
-- | them is already loaded, or this fails — and never as a way to find anything.
-- | Ordering is the front end's.
-- |
-- | The order below is what the procedure needs. **The slots come before the
-- | references because a resolved reference is a slot**: a `GLOBALREFS` entry of
-- | this module's own name resolves to the slot this load has just opened.
-- | **Initialization then runs against a working registry** — the persistent one
-- | with the candidate beside it — because a `run` global's code reads that
-- | module's tables and calls the closures its earlier `func` globals installed.
-- | **The module is committed only once it has initialized.**
-- |
-- | **An interned identity is not taken back.** An identity belongs to a name
-- | rather than to a module, so the tables that hold them are the one part of a
-- | store a failed load leaves changed: what is left is an identity nothing refers
-- | to, and a later module declaring that name is given the same one.
module Steam.Load
  ( Store
  , Identities
  , emptyStore
  , noIdentities
  , unitValue
  , internKeyIn
  , claimedByInterpreter
  , registryOf
  , namesOf
  , moduleNamed
  , globalNamed
  , LoadError(..)
  , load
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, for_, traverse_)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (EFFECT, Run, liftEffect)
import Run.Except (EXCEPT)
import Run.Except as Except
import Steam.Eval (Failure, enter)
import Steam.Foreign (ForeignTable)
import Steam.Foreign as Foreign
import Steam.Module (CalleeTarget(..), CtorRef, ForeignRef, GlobalSlot, HandlerRef, Loaded, Prepared, Registry, prepare)
import Steam.Op as Op
import Steam.Structural (RuntimeNames)
import Steam.Value (Closure, CtorId(..), Foreign(..), KeyId(..), ModuleId(..), OpId(..), Value(..), arityOfIO, entryOfIO, ioEntries)
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), CtorIx(..), ForeignIx(..), FuncIx(..), Function, GlobalIx(..), HandlerIx(..), Instr(..), Join, JoinName, KeyIx(..), Node, OpIx(..), PrimIx(..), Tail(..))
import Stella.Compiler.Bytecode.Module (CalleeEntry(..), Dmo, GlobalInit(..), HandlerEntry, Key)
import Stella.Compiler.Primitive (PrimOp, arityOfOp, entryOfOp)
import Stella.Compiler.TypedCore.Name (EffName, Ident, ModuleName, OpName, Qualified(..))
import Stella.Compiler.TypedCore.Prim (primModule, unitCtor)
import Type.Row (type (+))

-- The store ------------------------------------------------------------------------

-- | What the modules loaded so far amount to.
-- |
-- | The declarations are the committed part and a failed load leaves them as they
-- | were. The identities are in a reference of their own, since interning one is not
-- | taken back.
type Store =
  { identities :: Ref Identities
  , modules :: Map ModuleId Loaded
  , byName :: Map ModuleName ModuleId
  , nextModule :: P.Int
  -- | The slot of every global of every module loaded, which is what a reference to
  -- | one resolves to.
  , globals :: Map (Qualified Ident) GlobalSlot
  -- | The definitional arity of a global installed as a function, and nothing for
  -- | one evaluated at initialization.
  , arities :: Map (Qualified Ident) (Maybe P.Int)
  -- | What the host supplies, which a declaration the interpreter does not claim is
  -- | resolved against. It is read and never written: assembling it belongs to
  -- | whoever calls `load` ([Foreign](Foreign.purs)).
  , hostForeigns :: ForeignTable
  , foreigns :: Map (Qualified Ident) ForeignRef
  , ctors :: Map (Qualified Ident) CtorRef
  , exports :: Map ModuleName (Set Ident)
  }

-- | One identity per key, per operation name, and per constructor across everything
-- | loaded, and the way back from each: a value carries an identity and an identity
-- | is compared rather than read, so rendering one needs the name it was assigned
-- | for.
type Identities =
  { keys :: Map Key KeyId
  , keyNames :: Map KeyId Key
  , ops :: Map OpName OpId
  , opNames :: Map OpId OpName
  , ctors :: Map (Qualified Ident) CtorId
  , ctorNames :: Map CtorId (Qualified Ident)
  , next :: P.Int
  }

-- | The identities nothing has been loaded against yet.
noIdentities :: Identities
noIdentities =
  { keys: Map.empty
  , keyNames: Map.empty
  , ops: Map.empty
  , opNames: Map.empty
  , ctors: Map.empty
  , ctorNames: Map.empty
  , next: 0
  }

-- | A store holding no module, against the host's table and the identity tables
-- | given: a session keeps one set of those across every module it loads, and the
-- | table is complete for a module before that module is handed over.
emptyStore :: ForeignTable -> Ref Identities -> Store
emptyStore hostForeigns identities =
  { identities
  , modules: Map.empty
  , byName: Map.empty
  , nextModule: 0
  , globals: Map.empty
  , arities: Map.empty
  , hostForeigns
  , foreigns: Map.empty
  , ctors: Map.empty
  , exports: Map.empty
  }

-- | What a run reads: the modules, under the identities assigned to them.
registryOf :: Store -> Registry
registryOf store = store.modules

-- | The way back from an identity to the name it was assigned for, which is what a
-- | snapshot of a value reads ([Structural](Structural.purs)). A value carries an
-- | identity and an identity is compared rather than read, so a report needs this.
namesOf :: Store -> Effect RuntimeNames
namesOf store = do
  identities <- Ref.read store.identities
  pure
    { ctors: identities.ctorNames
    , keys: identities.keyNames
    , ops: identities.opNames
    }

moduleNamed :: Store -> ModuleName -> Maybe ModuleId
moduleNamed store name = Map.lookup name store.byName

-- | The slot a top-level value stands in, which is what a session's request and an
-- | entry point are read from. **Not through the exports**: an entry point need not
-- | be exported.
globalNamed :: Store -> Qualified Ident -> Maybe GlobalSlot
globalNamed store name = Map.lookup name store.globals

-- What loading refuses ------------------------------------------------------------

data LoadError
  = ModuleTwice ModuleName
  -- | A module under a name the implicit environment holds. `Prim` is Core's own
  -- | vocabulary and no file declares it, so a file claiming the name would be
  -- | declaring what every module already names.
  | ReservedModuleName ModuleName
  -- | A declaration whose qualified name belongs to another module, or a
  -- | constructor whose owner type does.
  | NotThisModule ModuleName (Qualified Ident)
  | OwnerNotThisModule ModuleName (Qualified Ident)
  | EffectNotThisModule ModuleName (Qualified EffName)
  | EffectDeclaredTwice (Qualified EffName)
  -- | Two declarations of one name in one namespace. The values of a module are one
  -- | namespace, so a global and a foreign of one name collide.
  | DeclaredTwice (Qualified Ident)
  -- | An exported name that is not a value this module declares.
  | ExportNotDeclared (Qualified Ident)
  | ImportNotLoaded ModuleName
  -- | A reference to a name no loaded module declares, or to one of the wrong kind.
  | NoSuchCtor (Qualified Ident)
  | NoSuchForeign (Qualified Ident)
  | NoSuchGlobal (Qualified Ident)
  -- | A reference to a name of a module this one does not import. A header is what
  -- | says which modules a term may name, and the order modules are loaded in adds
  -- | nothing to it.
  | NotImported ModuleName (Qualified Ident)
  -- | A reference to a name the module declaring it does not export.
  | NotExported (Qualified Ident)
  -- | A known call, or a partial application over a global, whose arity the
  -- | declaring module's function table does not admit: the arity it states, where
  -- | it states one, and the count the call supplies.
  | WrongCallArity (Qualified Ident) (Maybe P.Int) P.Int
  -- | A partial application that is not below the callee's arity, as the arity the
  -- | declaring module states and the count supplied.
  | PapNotBelowArity (Qualified Ident) P.Int P.Int
  -- | A constructor, a foreign, or an operation applied to a count its declaration
  -- | does not take.
  | WrongCtorArity (Qualified Ident) P.Int P.Int
  | WrongForeignArity (Qualified Ident) P.Int P.Int
  | WrongOperationArity PrimOp P.Int P.Int
  -- | A global installed as a function whose function expects captures. One is
  -- | installed as a closure over an empty capture list.
  | GlobalExpectsCaptures (Qualified Ident) P.Int
  -- | A global installed as a function of no parameters. A definitional arity counts
  -- | leading lambdas and is at least one, so a value with none is installed as one
  -- | evaluated at initialization instead.
  | FunctionGlobalWithoutParameters (Qualified Ident)
  -- | A global evaluated at initialization whose function takes parameters. It is
  -- | entered with none.
  | RunGlobalWithParameters (Qualified Ident) P.Int
  -- | An index naming nothing in a table of this module.
  | IndexOutOfRange P.String P.Int
  -- | A handler naming a key or an operation its module's tables do not hold.
  | NoSuchKeyIndex P.Int
  | NoSuchOpIndex P.Int
  -- | A handler declaring one cell twice, or holding two clauses for one operation,
  -- | as the key or the operation's name. Two indices may intern to one identity, so
  -- | what is compared is the identity.
  | CellKeyTwice Key
  | ClauseTwice OpName
  -- | A `HNDL` or `TAILHNDL` supplying another count of clauses, or of initial cell
  -- | values, than its handler entry holds: the key of the handler's effect, the
  -- | entry's count, and the instruction's.
  | HandlerClausesDisagree Key P.Int P.Int
  | HandlerCellsDisagree Key P.Int P.Int
  -- | Two join points of one function under one name.
  | JoinNameTwice JoinName
  -- | A foreign nothing carries out: neither an entry this interpreter claims nor
  -- | one the host's table holds. Resolution happens at load, so a program whose
  -- | foreigns are incomplete does not start, however little of it reaches the
  -- | declaration.
  | ForeignWithoutImplementation (Qualified Ident)
  -- | A foreign the interpreter claims — an operation, or one of the two `Base.IO`
  -- | entries — declared at an arity other than the one the ABI gives it, as the
  -- | ABI's and the declaration's. **The source is selected by the name**, so
  -- | nothing else may answer for it and the declaration is not of the entry it
  -- | names. The two kinds share a refusal because they share that rule; what
  -- | separates them is only that an operation carries a code and an IO entry does
  -- | not.
  | InterpreterEntryDeclaredAtWrongArity (Qualified Ident) P.Int P.Int
  -- | A foreign the host's table holds at an arity other than the one declared, as
  -- | the declaration's and the table's. **Reported as the disagreement it is
  -- | rather than as an absence**: an implementation is there, and a call site is
  -- | checked against the declaration, which is what the table was to match.
  | ForeignArityDisagrees (Qualified Ident) P.Int P.Int
  -- | An operation this interpreter does not carry out.
  | OperationNotImplemented PrimOp
  -- | A global whose initialization did not produce a value. The module is not
  -- | committed, so nothing of it is visible to what comes next.
  | InitializationFailed (Qualified Ident) Failure

type LOAD r = (EXCEPT LoadError + EFFECT + r)

refuse :: forall r a. LoadError -> Run (LOAD r) a
refuse = Except.throw

-- Loading ---------------------------------------------------------------------------

-- | Load one module against the store, or refuse it.
load :: forall r. Store -> Dmo -> Run (LOAD r) Store
load store dmo = do
  when (dmo.name == primModule) (refuse (ReservedModuleName dmo.name))
  when (isJust (Map.lookup dmo.name store.byName)) (refuse (ModuleTwice dmo.name))
  checkDeclarations dmo
  traverse_ (\name -> when (not (isJust (Map.lookup name store.byName))) (refuse (ImportNotLoaded name)))
    dmo.imports
  for_ dmo.prims \op ->
    when (not (Array.elem op Op.implemented)) (refuse (OperationNotImplemented op))
  functions <- traverse prepareOrRefuse dmo.functions
  declaredForeigns <- map Map.fromFoldable (traverse (implementationOf store) dmo.foreigns)

  -- identities, which outlive a refusal
  keys <- traverse (internKey store) dmo.keys
  ops <- traverse (internOp store) dmo.ops
  ctorIds <- traverse (\entry -> map { id: _, arity: entry.arity } (internCtor store entry.name))
    dmo.ctors

  -- `Prim.Unit` is the one value the implicit environment holds, and every module
  -- may name it: it stands among the declarations before a reference is resolved,
  -- under the identity every module shares
  unitCtorId <- internCtor store unitCtor

  -- the slots, and the tables of what this module declares
  slots <- traverse (\entry -> map (Tuple entry.name) (liftEffect (Ref.new Nothing)))
    dmo.globals
  let
    moduleId = ModuleId store.nextModule

    declaredCtors = Map.fromFoldable
      (Array.zipWith (\entry ref -> Tuple entry.name ref) dmo.ctors ctorIds)

    declaredGlobals = Map.fromFoldable slots

    declaredArities = Map.fromFoldable (map (\entry -> Tuple entry.name (arityOf functions entry.init)) dmo.globals)

    withDeclarations = store
      { foreigns = Map.union declaredForeigns store.foreigns
      , globals = Map.union declaredGlobals store.globals
      , arities = Map.union declaredArities store.arities
      , ctors = Map.union declaredCtors
          (Map.union (Map.singleton unitCtor { id: unitCtorId, arity: 0 }) store.ctors)
      , exports = Map.insert dmo.name (Set.fromFoldable (map unqualify dmo.exports)) store.exports
      }

  -- the references, against those tables and the registry. **A term names this
  -- module or one it imports**, which the header says and the order of loading adds
  -- nothing to
  let scope = { here: dmo.name, allowed: Set.insert dmo.name (Set.fromFoldable dmo.imports) }
  ctorRefs <- traverse (resolveCtor withDeclarations scope) dmo.ctorRefs
  foreigns <- traverse (resolveForeign withDeclarations scope) dmo.foreignRefs
  globalRefs <- traverse (resolveGlobal withDeclarations scope) dmo.globalRefs
  callees <- traverse (resolveCallee withDeclarations scope) dmo.callees
  handlers <- traverse (resolveHandler dmo keys ops) dmo.handlers
  checkHandlers dmo
  checkGlobals functions dmo
  checkArities withDeclarations dmo

  let
    candidate =
      { id: moduleId
      , constants: dmo.constants
      , keys
      , ops
      , ctors: ctorRefs
      , foreigns
      , globals: globalRefs
      , callees
      , prims: dmo.prims
      , handlers
      , unit: VData unitCtorId []
      , functions
      }

    -- the working registry: the persistent one with the candidate beside it, which
    -- is what a `run` global's own code runs against
    working = Map.insert moduleId candidate withDeclarations.modules

  initialize working dmo candidate declaredGlobals

  pure withDeclarations
    { modules = working
    , byName = Map.insert dmo.name moduleId withDeclarations.byName
    , nextModule = store.nextModule + 1
    }
  where
  unqualify (Qualified _ name) = name

  prepareOrRefuse function = case prepare function of
    Right prepared -> pure prepared
    Left name -> refuse (JoinNameTwice name)

-- | The definitional arity of a global, which is the number of parameters of the
-- | function it installs. One evaluated at initialization has none.
arityOf :: P.Array Prepared -> GlobalInit -> Maybe P.Int
arityOf functions = case _ of
  GFunc (FuncIx i) -> map _.nparams (Array.index functions i)
  GRun _ -> Nothing

-- Declarations ----------------------------------------------------------------------

-- | That every declaration belongs to this module, that no name stands over two of
-- | them in one namespace, and that every export is a value it declares.
checkDeclarations :: forall r. Dmo -> Run (LOAD r) Unit
checkDeclarations dmo = do
  for_ dmo.ctors \entry -> do
    own entry.name
    case entry.owner of
      Qualified moduleName _ ->
        when (moduleName /= dmo.name) (refuse (OwnerNotThisModule dmo.name entry.name))
  for_ dmo.effects \entry -> case entry.name of
    Qualified moduleName _ ->
      when (moduleName /= dmo.name) (refuse (EffectNotThisModule dmo.name entry.name))
  for_ dmo.foreigns (own <<< _.name)
  for_ dmo.globals (own <<< _.name)
  unique DeclaredTwice (map _.name dmo.ctors)
  unique EffectDeclaredTwice (map _.name dmo.effects)
  -- a global and a foreign of one name are two declarations of one value
  unique DeclaredTwice (map _.name dmo.foreigns <> map _.name dmo.globals)
  for_ dmo.exports \name ->
    when (not (Array.elem name (map _.name dmo.globals <> map _.name dmo.foreigns)))
      (refuse (ExportNotDeclared name))
  where
  own name@(Qualified moduleName _) =
    when (moduleName /= dmo.name) (refuse (NotThisModule dmo.name name))

  unique :: forall r' a. Ord a => (a -> LoadError) -> P.Array a -> Run (LOAD r') Unit
  unique twice names = void (foldM one Set.empty names)
    where
    one seen name
      | Set.member name seen = refuse (twice name)
      | otherwise = pure (Set.insert name seen)

-- Identities --------------------------------------------------------------------------

internKey :: forall r. Store -> Key -> Run (LOAD r) KeyId
internKey store key = liftEffect (internKeyIn store.identities key)

-- | The identity of a key, assigned where it has none yet. A key a value carries
-- | in from outside a load — a record field of a session answer — is interned
-- | the same way a module's `KEYS` are.
internKeyIn :: Ref Identities -> Key -> Effect KeyId
internKeyIn ref key = do
  identities <- Ref.read ref
  case Map.lookup key identities.keys of
    Just id -> pure id
    Nothing -> do
      let id = KeyId identities.next
      Ref.write
        identities
          { keys = Map.insert key id identities.keys
          , keyNames = Map.insert id key identities.keyNames
          , next = identities.next + 1
          }
        ref
      pure id

internOp :: forall r. Store -> OpName -> Run (LOAD r) OpId
internOp store name = do
  identities <- liftEffect (Ref.read store.identities)
  case Map.lookup name identities.ops of
    Just id -> pure id
    Nothing -> do
      let id = OpId identities.next
      liftEffect
        ( Ref.write
            identities
              { ops = Map.insert name id identities.ops
              , opNames = Map.insert id name identities.opNames
              , next = identities.next + 1
              }
            store.identities
        )
      pure id

internCtor :: forall r. Store -> Qualified Ident -> Run (LOAD r) CtorId
internCtor store name = liftEffect (internCtorIn store.identities name)

internCtorIn :: Ref Identities -> Qualified Ident -> Effect CtorId
internCtorIn ref name = do
  identities <- Ref.read ref
  case Map.lookup name identities.ctors of
    Just id -> pure id
    Nothing -> do
      let id = CtorId identities.next
      Ref.write
        identities
          { ctors = Map.insert name id identities.ctors
          , ctorNames = Map.insert id name identities.ctorNames
          , next = identities.next + 1
          }
        ref
      pure id

-- | `Prim.Unit`, under the identity every module loaded against these identities
-- | gives it.
-- |
-- | **An identity belongs to a name**, so asking for this one before any module is
-- | loaded gives the identity each load then finds. That is what lets a value
-- | built outside a load — the `Prim.Unit` a hosted foreign's `unit` result
-- | stands for — be the one every module compares against.
unitValue :: Ref Identities -> Effect Value
unitValue identities = map (\id -> VData id []) (internCtorIn identities unitCtor)

-- References -----------------------------------------------------------------------

-- | That a reference reaches a declaration of the kind its table calls for, and
-- | that the module declaring it published the name where that module is not this
-- | one.
-- | What a module's terms may name: itself, and the modules its header imports.
type Scope =
  { here :: ModuleName
  , allowed :: Set ModuleName
  }

-- | That a reference names a module this one imports, or this one itself.
-- |
-- | **`Prim` is the exception**, being the implicit environment: it is the vocabulary
-- | the rules of Core name, it stands in no header, and the one value it holds is
-- | `Prim.Unit` ([Prim and Base](../../../docs/technical-references/06-Modules/02-Prim-and-Base.md)).
imported :: forall r. Scope -> Qualified Ident -> Run (LOAD r) Unit
imported scope name@(Qualified moduleName _) =
  when (moduleName /= primModule && not (Set.member moduleName scope.allowed))
    (refuse (NotImported scope.here name))

-- | That the module declaring a name published it, where that module is not this
-- | one. A constructor is not checked this way: `EXPORTS` holds value names, and
-- | data abstraction is settled where types are (D22).
exported :: forall r. Store -> Scope -> Qualified Ident -> Run (LOAD r) Unit
exported store scope name@(Qualified moduleName ident)
  | moduleName == scope.here = pure unit
  | otherwise = case Map.lookup moduleName store.exports of
      Just names | Set.member ident names -> pure unit
      _ -> refuse (NotExported name)

resolveCtor :: forall r. Store -> Scope -> Qualified Ident -> Run (LOAD r) CtorRef
resolveCtor store scope name = do
  imported scope name
  case Map.lookup name store.ctors of
    Just ref -> pure ref
    Nothing -> refuse (NoSuchCtor name)

resolveForeign :: forall r. Store -> Scope -> Qualified Ident -> Run (LOAD r) ForeignRef
resolveForeign store scope name = do
  imported scope name
  case Map.lookup name store.foreigns of
    Just entry -> do
      exported store scope name
      pure entry
    Nothing -> refuse (NoSuchForeign name)

-- | Whether the interpreter carries out a foreign of this name itself: an operation, or
-- | `Base.IO.pure` or `Base.IO.bind`. **The name alone decides it**, as it does in
-- | `implementationOf`, so the host is never asked for such a name.
claimedByInterpreter :: Qualified Ident -> P.Boolean
claimedByInterpreter name =
  Array.any (\op -> entryOfOp op == name) Op.implemented
    || Array.any (\io -> entryOfIO io == name) ioEntries

-- | What carries out a foreign this module declares.
-- |
-- | **Which of the two sources answers is decided by the name alone.** A `Base`
-- | entry the interpreter claims is carried out by the interpreter itself and the
-- | host's table is not consulted for that name at all; anything else the table
-- | holds is carried out by that entry's body; anything else is carried out by
-- | nothing, and the module does not load.
-- |
-- | Selecting on the name **together with** an arity would leave a way around the
-- | first rule: a declaration of `Base.Int.add` at the wrong arity would fail to be
-- | the interpreter's, fall through to a host entry holding that same wrong arity,
-- | and run an implementation where the ABI fixes an operation's meaning for every
-- | backend. So the arity is checked afterwards, against whichever source the name
-- | selected.
implementationOf
  :: forall r
   . Store
  -> { name :: Qualified Ident, arity :: P.Int }
  -> Run (LOAD r) (Tuple (Qualified Ident) ForeignRef)
implementationOf store entry =
  case Array.find (\op -> entryOfOp op == entry.name) Op.implemented of
    Just op
      | arityOfOp op == entry.arity ->
          pure (Tuple entry.name { carriedOutBy: ForeignOperation op, arity: entry.arity })
      | otherwise ->
          refuse (InterpreterEntryDeclaredAtWrongArity entry.name (arityOfOp op) entry.arity)
    Nothing -> case Array.find (\io -> entryOfIO io == entry.name) ioEntries of
      -- `Base.IO.pure` and `Base.IO.bind` are the interpreter's like an operation,
      -- and are not operations: each returns `IO`, so no code stands for it
      Just io
        | arityOfIO io == entry.arity ->
            pure (Tuple entry.name { carriedOutBy: ForeignIO io, arity: entry.arity })
        | otherwise ->
            refuse (InterpreterEntryDeclaredAtWrongArity entry.name (arityOfIO io) entry.arity)
      Nothing -> hosted
  where
  hosted = case Foreign.lookup entry.name store.hostForeigns of
    Just held
      | held.arity == entry.arity ->
          pure
            ( Tuple entry.name
                { carriedOutBy: ForeignHosted entry.name held.body
                , arity: entry.arity
                }
            )
      | otherwise -> refuse (ForeignArityDisagrees entry.name entry.arity held.arity)
    Nothing -> refuse (ForeignWithoutImplementation entry.name)

resolveGlobal :: forall r. Store -> Scope -> Qualified Ident -> Run (LOAD r) GlobalSlot
resolveGlobal store scope name = do
  imported scope name
  case Map.lookup name store.globals of
    Just slot -> do
      exported store scope name
      pure slot
    Nothing -> refuse (NoSuchGlobal name)

resolveCallee :: forall r. Store -> Scope -> CalleeEntry -> Run (LOAD r) CalleeTarget
resolveCallee store scope = case _ of
  CalleeValue name -> map TargetGlobal (resolveGlobal store scope name)
  CalleeCtor name -> do
    ref <- resolveCtor store scope name
    pure (TargetCtor ref.id ref.arity)
  CalleeForeign name -> do
    entry <- resolveForeign store scope name
    pure (TargetForeign entry.carriedOutBy entry.arity)
  CalleePrim op -> pure (TargetPrim op)

-- | That how a global is installed agrees with the function it names: one installed
-- | as a **function** has a definitional arity, which counts leading lambdas and is
-- | at least one, and one **evaluated at initialization** is entered with no
-- | arguments. Neither closes over anything.
checkGlobals :: forall r. P.Array Prepared -> Dmo -> Run (LOAD r) Unit
checkGlobals functions dmo = traverse_ one dmo.globals
  where
  one entry = do
    function <- functionAt (funcOf entry.init)
    when (function.ncaptures /= 0)
      (refuse (GlobalExpectsCaptures entry.name function.ncaptures))
    case entry.init of
      GFunc _ ->
        when (function.nparams < 1) (refuse (FunctionGlobalWithoutParameters entry.name))
      GRun _ ->
        when (function.nparams /= 0)
          (refuse (RunGlobalWithParameters entry.name function.nparams))

  funcOf = case _ of
    GFunc ix -> ix
    GRun ix -> ix

  functionAt (FuncIx i) = case Array.index functions i of
    Just function -> pure function
    Nothing -> refuse (IndexOutOfRange "FUNCTIONS" i)

-- | A handler with the key it answers, its cells' keys, and its clauses resolved. A
-- | `HANDLERS` entry indexes this module's own `KEYS` and `OPS`, so nothing is
-- | looked up where the handler is installed.
resolveHandler
  :: forall r
   . Dmo
  -> P.Array KeyId
  -> P.Array OpId
  -> HandlerEntry
  -> Run (LOAD r) HandlerRef
resolveHandler dmo keys ops entry = do
  key <- map _.id (keyAt entry.key)
  cells <- traverse keyAt entry.cells
  opClauses <- traverse clause entry.opClauses
  unique CellKeyTwice cells
  unique ClauseTwice opClauses
  pure { key, cells: map _.id cells, opClauses: map (\c -> { op: c.id, form: c.form }) opClauses }
  where
  keyAt (KeyIx i) = case Array.index keys i, Array.index dmo.keys i of
    Just id, Just name -> pure { id, name }
    _, _ -> refuse (NoSuchKeyIndex i)

  clause c = case c.op of
    OpIx i -> case Array.index ops i, Array.index dmo.ops i of
      Just id, Just name -> pure { id, name, form: c.form }
      _, _ -> refuse (NoSuchOpIndex i)

  -- a cell is found by its key and a clause by its operation, so either standing
  -- twice would leave which one a `CGET` or a `PERF` means to the order of a table
  unique
    :: forall r2 id name more
     . Ord id
    => (name -> LoadError)
    -> P.Array { id :: id, name :: name | more }
    -> Run (LOAD r2) Unit
  unique twice named = void (foldM one Set.empty named)
    where
    one seen resolved
      | Set.member resolved.id seen = refuse (twice resolved.name)
      | otherwise = pure (Set.insert resolved.id seen)

-- | That every `HNDL` and `TAILHNDL` supplies one clause per clause of its handler
-- | entry and one initial value per cell, wherever in a function it stands.
checkHandlers :: forall r. Dmo -> Run (LOAD r) Unit
checkHandlers dmo = traverse_ perFunction dmo.functions
  where
  perFunction function = do
    traverse_ perInstr (instructionsOf function)
    traverse_ perTail (tailsOf function)

  perInstr = case _ of
    HNDL _ ix _ _ clauses cells -> operands ix clauses cells
    _ -> pure unit

  perTail = case _ of
    TAILHNDL ix _ _ clauses cells -> operands ix clauses cells
    _ -> pure unit

  operands :: forall r2 a b. HandlerIx -> P.Array a -> P.Array b -> Run (LOAD r2) Unit
  operands (HandlerIx i) clauses cells = case Array.index dmo.handlers i of
    Nothing -> refuse (IndexOutOfRange "HANDLERS" i)
    Just entry -> do
      key <- case entry.key of
        KeyIx k -> case Array.index dmo.keys k of
          Just key -> pure key
          Nothing -> refuse (NoSuchKeyIndex k)
      when (Array.length clauses /= Array.length entry.opClauses)
        (refuse (HandlerClausesDisagree key (Array.length entry.opClauses) (Array.length clauses)))
      when (Array.length cells /= Array.length entry.cells)
        (refuse (HandlerCellsDisagree key (Array.length entry.cells) (Array.length cells)))

-- | That every call in the code supplies a count the declaration it reaches admits.
-- |
-- | This is the check the modules being together is what makes possible: an arity is
-- | the declaring module's, and a `.dmi` that published a wrong one is caught here
-- | rather than where the call runs
-- | ([Interface](../../../docs/technical-references/05-Backend/03-Interface.md)).
checkArities :: forall r. Store -> Dmo -> Run (LOAD r) Unit
checkArities store dmo = traverse_ perFunction dmo.functions
  where
  perFunction function = do
    traverse_ perInstr (instructionsOf function)
    traverse_ perTail (tailsOf function)

  perInstr = case _ of
    CALLK _ ix args -> known ix (Array.length args)
    PAP _ ix args -> partial ix (Array.length args)
    CTOR _ ix args -> constructor ix (Array.length args)
    LOADC _ ix -> constructor ix 0
    FFI _ ix args -> foreignCall ix (Array.length args)
    PRIM _ ix args -> operation ix (Array.length args)
    _ -> pure unit

  perTail = case _ of
    TAILK ix args -> known ix (Array.length args)
    TAILFFI ix args -> foreignCall ix (Array.length args)
    _ -> pure unit

  -- a known call supplies exactly the arity the entry takes
  known (GlobalIx i) count = do
    name <- at "GLOBALREFS" dmo.globalRefs i
    case Map.lookup name store.arities of
      Just (Just arity)
        | arity == count -> pure unit
      stated -> refuse (WrongCallArity name (join stated) count)

  -- a partial application supplies fewer, whatever kind of callee it stands over
  partial (CalleeIx i) count = do
    entry <- at "CALLEES" dmo.callees i
    case entry of
      CalleeValue name -> case Map.lookup name store.arities of
        Just (Just arity)
          | count < arity -> pure unit
          | otherwise -> refuse (PapNotBelowArity name arity count)
        stated -> refuse (WrongCallArity name (join stated) count)
      CalleeCtor name -> do
        ref <- ctorNamed name
        when (count >= ref.arity) (refuse (PapNotBelowArity name ref.arity count))
      CalleeForeign name -> do
        entry' <- foreignNamed name
        when (count >= entry'.arity) (refuse (PapNotBelowArity name entry'.arity count))
      CalleePrim op ->
        when (count >= arityOfOp op)
          (refuse (PapNotBelowArity (entryOfOp op) (arityOfOp op) count))

  constructor (CtorIx i) count = do
    name <- at "CTORREFS" dmo.ctorRefs i
    ref <- ctorNamed name
    when (count /= ref.arity) (refuse (WrongCtorArity name ref.arity count))

  foreignCall (ForeignIx i) count = do
    name <- at "FOREIGNREFS" dmo.foreignRefs i
    entry <- foreignNamed name
    when (count /= entry.arity) (refuse (WrongForeignArity name entry.arity count))

  operation (PrimIx i) count = do
    op <- at "PRIMS" dmo.prims i
    when (count /= arityOfOp op) (refuse (WrongOperationArity op (arityOfOp op) count))

  ctorNamed name = case Map.lookup name store.ctors of
    Just ref -> pure ref
    Nothing -> refuse (NoSuchCtor name)

  foreignNamed name = case Map.lookup name store.foreigns of
    Just entry -> pure entry
    Nothing -> refuse (NoSuchForeign name)

  at :: forall r2 a. P.String -> P.Array a -> P.Int -> Run (LOAD r2) a
  at table xs i = case Array.index xs i of
    Just x -> pure x
    Nothing -> refuse (IndexOutOfRange table i)

-- | Every instruction of a function, the branches of its decision trees included.
instructionsOf :: Function -> P.Array Instr
instructionsOf function = Array.concatMap nodeInstrs (nodesOf function)

tailsOf :: Function -> P.Array Tail
tailsOf function = map _.tail (nodesOf function)

nodeInstrs :: Node -> P.Array Instr
nodeInstrs node = node.code

-- | Every node of a function: its body, the body of each join point, and the nodes
-- | a branch holds inline.
nodesOf :: Function -> P.Array Node
nodesOf function =
  Array.concatMap expand ([ function.body ] <> map joinBody function.joins)
  where
  joinBody :: Join -> Node
  joinBody join = join.body

  expand node = [ node ] <> Array.concatMap expand (inline node.tail)

  inline = case _ of
    BRIF _ a b -> [ a, b ]
    BRC _ cases fallback -> map _.body cases <> maybe' fallback
    BRL _ cases fallback -> map _.body cases <> [ fallback ]
    BRK _ cases fallback -> map _.body cases <> maybe' fallback
    _ -> []

  maybe' = case _ of
    Just node -> [ node ]
    Nothing -> []

-- Initialization ---------------------------------------------------------------------

-- | Run the globals in declaration order against the working registry: a `run`
-- | entry is evaluated once and its value stored, a `func` entry installs a closure
-- | over an empty capture list.
initialize
  :: forall r
   . Registry
  -> Dmo
  -> Loaded
  -> Map (Qualified Ident) GlobalSlot
  -> Run (LOAD r) Unit
initialize working dmo candidate slots = traverse_ one dmo.globals
  where
  one entry = case Map.lookup entry.name slots of
    Nothing -> refuse (NoSuchGlobal entry.name)
    Just slot -> case entry.init of
      GFunc ix -> do
        closure <- closureOver ix
        liftEffect (Ref.write (Just (VClos closure)) slot)
      GRun ix -> do
        closure <- closureOver ix
        outcome <- Except.runExcept (enter working closure [])
        case outcome of
          Right value -> liftEffect (Ref.write (Just value) slot)
          Left failure -> refuse (InitializationFailed entry.name failure)

  -- how a global is installed was checked against the function it names, so what is
  -- left here is to install it
  closureOver ix = do
    captures <- liftEffect (Ref.new Map.empty)
    pure { func: { module: candidate.id, func: ix }, captures } :: Run (LOAD r) Closure

derive instance Eq LoadError
derive instance Generic LoadError _

instance Show LoadError where
  show = genericShow
