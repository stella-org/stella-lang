-- | `translate`, from Typed Core to Mid IR.
-- |
-- | It performs the erasures of the Semantics document, names every
-- | intermediate result, folds application spines, materializes occurrences,
-- | and lifts every function body out of its nesting.
-- |
-- | **Translation checks nothing.** Every property it relies on the Core type
-- | checker has established, and a term that has not been checked never reaches
-- | it. What it owes in return is the invariants of Mid IR.
-- |
-- | Types reach it through the annotation checking left on the term, so no type
-- | is re-derived here. Where one is not to hand the binding takes `RepVal`,
-- | which costs precision and never correctness.
module Stella.Compiler.MiddleEnd.Translate
  ( TranslateError(..)
  , translate
  , Free
  , freeVars
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Interface (Imports, importedArities)
import Stella.Compiler.Primitive (PrimOp, lookupPrim)
import Stella.Compiler.MiddleEnd.Rep (Rep(..), repOf)
import Stella.Compiler.MiddleEnd.IR as M
import Stella.Compiler.TypedCore.Check (Typed)
import Stella.Compiler.TypedCore.Decl as D
import Stella.Compiler.TypedCore.Declare (CheckedGroup, Declared)
import Stella.Compiler.TypedCore.Name (Ident, JoinName, ModuleName, Qualified(..), RegionName)
import Stella.Compiler.TypedCore.Prim (asFunction)
import Stella.Compiler.TypedCore.Signature (Signature, lookupCtor, lookupValue)
import Stella.Compiler.TypedCore.Term as C
import Stella.Compiler.TypedCore.Type (RowKey, Type(..), TypeScheme, rowEntryKey)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldMap, foldl, traverse_)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))

data TranslateError
  = UnboundLocal Ident
  -- | A `Base` entry the manifest holds at one arity and the declaration at
  -- | another, as the manifest's and the declaration's. The two describe one
  -- | entry, so a disagreement is an inconsistent ABI package rather than
  -- | something to fall back from.
  | AbiArityMismatch (Qualified Ident) P.Int P.Int
  | UnboundJoin JoinName
  | UnknownGlobal (Qualified Ident)
  -- | A path the tree mentions that neither a scrutinee nor a dispatch
  -- | established. A checked tree has none.
  | UnresolvedOccurrence C.Occurrence
  -- | A control construct reached the forms that are one computation. Both
  -- | callers take those constructs first — one to a destination, the other
  -- | through a join point — so this reports a translator that grew a third.
  | ControlInValuePosition
  | UnboundRegion RegionName
  -- | A cell the region's layout does not declare, as the region and the key.
  | UnknownCell RegionName RowKey

derive instance Eq TranslateError
derive instance Generic TranslateError _

instance Show TranslateError where
  show x = genericShow x

-- The state ------------------------------------------------------------------

-- | `nextLocal` and `nextJoin` count within one function and are saved and
-- | restored around each, which is what makes a `Local` dense from zero there —
-- | a backend maps one onto a frame slot without renaming. `nextFunc` counts
-- | across the module, a `FuncId` being an index into its table.
type TState ann =
  { nextLocal :: P.Int
  , nextJoin :: P.Int
  , nextFunc :: P.Int
  , currentFunc :: Maybe M.FuncId
  , functions :: Map M.FuncId M.Function
  , debug :: M.Debug ann
  }

newtype T ann r = T (TState ann -> Either TranslateError (Tuple r (TState ann)))

runT :: forall ann r. TState ann -> T ann r -> Either TranslateError (Tuple r (TState ann))
runT s (T f) = f s

instance Functor (T ann) where
  map f (T g) = T \s -> case g s of
    Left err -> Left err
    Right (Tuple a s') -> Right (Tuple (f a) s')

instance Apply (T ann) where
  apply = ap

instance Applicative (T ann) where
  pure a = T \s -> Right (Tuple a s)

instance Bind (T ann) where
  bind (T g) f = T \s -> case g s of
    Left err -> Left err
    Right (Tuple a s') -> runT s' (f a)

instance Monad (T ann)

throw :: forall ann r. TranslateError -> T ann r
throw err = T \_ -> Left err

freshLocal :: forall ann. T ann M.Local
freshLocal = T \s -> Right (Tuple (M.Local s.nextLocal) (s { nextLocal = s.nextLocal + 1 }))

freshJoin :: forall ann. T ann M.JoinId
freshJoin = T \s -> Right (Tuple (M.JoinId s.nextJoin) (s { nextJoin = s.nextJoin + 1 }))

freshFunc :: forall ann. T ann M.FuncId
freshFunc = T \s -> Right (Tuple (M.FuncId s.nextFunc) (s { nextFunc = s.nextFunc + 1 }))

emitFunction :: forall ann. M.Function -> T ann Unit
emitFunction f = T \s -> Right (Tuple unit (s { functions = Map.insert f.id f s.functions }))

-- | What a `.dmo` names in its `DEBUG` section. Nothing about the module the
-- | translation produces depends on any of it.
recordFunction :: forall ann. M.FuncId -> Maybe ann -> T ann Unit
recordFunction func source = T \s ->
  Right
    ( Tuple unit
        ( s
            { debug = s.debug
                { functions = Map.insert func { name: Nothing, source } s.debug.functions }
            }
        )
    )

nameFunction :: forall ann. M.FuncId -> Qualified Ident -> T ann Unit
nameFunction func name = T \s ->
  Right
    ( Tuple unit
        ( s
            { debug = s.debug
                { functions =
                    Map.alter
                      (map (_ { name = Just name }))
                      func
                      s.debug.functions
                }
            }
        )
    )

-- | A local is named within the function it belongs to, there being no identity
-- | in the number alone.
recordLocal :: forall ann. M.Local -> Ident -> T ann Unit
recordLocal local name = T \s -> case s.currentFunc of
  Nothing -> Right (Tuple unit s)
  Just func ->
    Right
      ( Tuple unit
          ( s
              { debug = s.debug
                  { locals =
                      Map.alter
                        (Just <<< Map.insert local name <<< fromMaybe Map.empty)
                        func
                        s.debug.locals
                  }
              }
          )
      )

-- | Translate a function body under its own numbering: a `Local` and a `JoinId`
-- | are unique within a function and not beyond one.
inFunction :: forall ann r. M.FuncId -> T ann r -> T ann r
inFunction func (T body) = T \s ->
  case body (s { nextLocal = 0, nextJoin = 0, currentFunc = Just func }) of
    Left err -> Left err
    Right (Tuple r s') ->
      Right
        ( Tuple r
            ( s'
                { nextLocal = s.nextLocal
                , nextJoin = s.nextJoin
                , currentFunc = s.currentFunc
                }
            )
        )

-- The context ----------------------------------------------------------------

-- | What a Core variable stands for. A `let` whose right-hand side is already an
-- | atom binds an alias, so not every variable is a local.
type Bound =
  { atom :: M.Atom
  , rep :: Rep
  }

type Ctx =
  { signature :: Signature
  , locals :: Map Ident Bound
  , regions :: Map RegionName RegionBound
  , joins :: Map JoinName M.JoinId
  -- | The definitional arity of a top-level value of this module or of one it
  -- | imports: the number of leading lambdas the erased right-hand side has. A
  -- | value whose right-hand side is not a lambda has none, and a call to it is
  -- | `callu`.
  , arities :: Map (Qualified Ident) P.Int
  }

-- | What a region name stands for: the atom holding the identity of the region,
-- | and its keys in the order the layout writes them, which is what a cell's
-- | position is read from.
type RegionBound =
  { identity :: M.Atom
  , keys :: P.Array RowKey
  }

-- | What the head of an application spine is, and how many arguments saturate
-- | it.
data Head
  = HValue (Maybe P.Int)
  | HForeign P.Int
  | HCtor P.Int

-- | Whether a foreign is a `Base` operation.
-- |
-- | Both the bare reference and the saturated call read it here, so an entry
-- | cannot be an operation on one path and an implementation on the other.
foreignKind :: forall a. Qualified Ident -> P.Int -> T a (Maybe PrimOp)
foreignKind name arity = case lookupPrim name of
  Nothing -> pure Nothing
  Just prim
    | prim.arity == arity -> pure (Just prim.op)
    | otherwise -> throw (AbiArityMismatch name prim.arity arity)

classify :: Ctx -> Qualified Ident -> Maybe Head
classify ctx name = case lookupValue ctx.signature name of
  Just info
    | info.isForeign -> Just (HForeign (foreignArity info.scheme))
    | otherwise -> Just (HValue (Map.lookup name ctx.arities))
  Nothing -> case lookupCtor ctx.signature name of
    Just info -> Just (HCtor (Array.length info.fields))
    Nothing -> Nothing

-- | The number of arrows on a declared type's spine, which is what a `foreign`
-- | takes. Arity is a static property of the declaration: substitution can
-- | introduce arrows the declaration never called for, and those are not
-- | argument positions.
foreignArity :: TypeScheme -> P.Int
foreignArity scheme = walk scheme.body
  where
  walk ty = case ty of
    TForall _ _ body -> walk body
    TConstrained _ body -> walk body
    _ -> case asFunction ty of
      Just parts -> 1 + walk parts.result
      Nothing -> 0

bindLocal :: Ctx -> Ident -> Bound -> Ctx
bindLocal ctx name bound = ctx { locals = Map.insert name bound ctx.locals }

lookupBound :: forall ann. Ctx -> Ident -> T ann Bound
lookupBound ctx name = case Map.lookup name ctx.locals of
  Just bound -> pure bound
  Nothing -> throw (UnboundLocal name)

lookupRegion :: forall ann. Ctx -> RegionName -> T ann RegionBound
lookupRegion ctx name = case Map.lookup name ctx.regions of
  Just region -> pure region
  Nothing -> throw (UnboundRegion name)

-- | The identity of the region a cell belongs to, and the cell's position in it.
cellOf :: forall ann. Ctx -> RegionName -> RowKey -> T ann { region :: M.Atom, index :: P.Int }
cellOf ctx name key = do
  region <- lookupRegion ctx name
  case Array.elemIndex key region.keys of
    Just index -> pure { region: region.identity, index }
    Nothing -> throw (UnknownCell name key)

-- Destinations ---------------------------------------------------------------

-- | Where a term's value goes.
data Dest
  = DRet
  | DJump M.JoinId

-- | What translating one term produced: a value, or a computation to bind.
data Result
  = RAtom M.Atom
  | RComp M.Comp Rep

deliver :: forall ann. Dest -> Result -> T ann M.Expr
deliver dest result = case dest, result of
  DRet, RAtom atom -> pure (M.ERet atom)
  DRet, RComp comp _ -> pure (M.ETail comp)
  DJump j, RAtom atom -> pure (M.EJump j [ atom ])
  DJump j, RComp comp rep -> do
    local <- freshLocal
    pure (M.ELet local rep comp (M.EJump j [ M.ALocal local ]))

-- Terms ----------------------------------------------------------------------

typeAt :: forall a. C.Expr (Typed a) -> Type
typeAt = _.ty <<< C.exprAnnotation

-- | The annotation the term arrived with, which is what a source span reaches
-- | the debug table through.
sourceAt :: forall a. C.Expr (Typed a) -> a
sourceAt = _.source <<< C.exprAnnotation

repAt :: forall a. Ctx -> C.Expr (Typed a) -> Rep
repAt ctx = repOf ctx.signature <<< typeAt

-- | A term at a destination.
-- | The wrappers erasure removes are looked through to find the construct, and
-- | `expr` itself — the outermost node, wrappers included — is what goes on to
-- | `value`. Recursing into the inner term instead would lose the annotation
-- | that spans the whole of it.
go :: forall a. Ctx -> Dest -> C.Expr (Typed a) -> T a M.Expr
go ctx dest expr = case stripErased expr of
  C.Let _ name _ rhs body ->
    atomizeNamed ctx (Just name) rhs \bound ->
      go (bindLocal ctx name bound) dest body

  C.LetRec _ bindings body -> do
    group <- recursiveGroup ctx bindings
    M.ELetRec group.bindings <$> go group.ctx dest body

  C.Case ann scrutinees dt ->
    withAtoms ctx scrutinees \atoms ->
      decisionTree ctx dest ann.occurrences (seedOccurrences atoms) dt

  C.LetJoin _ name params _ definitionBody body -> do
    j <- freshJoin
    binders <- traverse (\param -> paramBinder ctx param.name param.ty) params
    let outer = ctx { joins = Map.insert name j ctx.joins }
    let inner = foldl (\acc b -> bindLocal acc b.name b.bound) outer binders
    definition <- go inner dest definitionBody
    rest <- go outer dest body
    pure (M.ELetJoin j (map _.binder binders) definition rest)

  C.Jump _ name args -> case Map.lookup name ctx.joins of
    Nothing -> throw (UnboundJoin name)
    Just j -> withAtoms ctx args \atoms -> pure (M.EJump j atoms)

  _ -> value ctx expr (deliver dest)

-- | A term whose value is wanted as an atom.
atomize :: forall a. Ctx -> C.Expr (Typed a) -> (M.Atom -> T a M.Expr) -> T a M.Expr
atomize ctx expr k = atomizeBound ctx expr (k <<< _.atom)

-- | The same, keeping the representation so that an alias carries it too.
atomizeBound :: forall a. Ctx -> C.Expr (Typed a) -> (Bound -> T a M.Expr) -> T a M.Expr
atomizeBound ctx = atomizeNamed ctx Nothing

-- | The same again, with the Core name the value is about to be bound to.
-- |
-- | The name reaches the debug table only where a local is **created** for it.
-- | A right-hand side that is already an atom binds an alias — `let y = x` makes
-- | no local, and recording `y` against `x`'s would rename `x`.
atomizeNamed
  :: forall a
   . Ctx
  -> Maybe Ident
  -> C.Expr (Typed a)
  -> (Bound -> T a M.Expr)
  -> T a M.Expr
atomizeNamed ctx named expr k = case stripErased expr of
  C.Let _ name _ rhs body ->
    atomizeNamed ctx (Just name) rhs \bound ->
      atomizeNamed (bindLocal ctx name bound) named body k

  C.LetRec _ bindings body -> do
    group <- recursiveGroup ctx bindings
    M.ELetRec group.bindings <$> atomizeNamed group.ctx named body k

  -- A control construct cannot deliver a value to a surrounding expression, so
  -- the surrounding expression becomes a join point and the construct jumps to
  -- it. Duplicating the continuation into each branch is what this avoids.
  C.Case _ _ _ -> viaJoin ctx named expr k
  C.LetJoin _ _ _ _ _ _ -> viaJoin ctx named expr k
  C.Jump _ _ _ -> viaJoin ctx named expr k

  _ -> value ctx expr \result -> case result of
    RAtom atom -> k { atom, rep: repAt ctx expr }
    RComp comp rep -> do
      local <- freshLocal
      traverse_ (recordLocal local) named
      M.ELet local rep comp <$> k { atom: M.ALocal local, rep }

viaJoin :: forall a. Ctx -> Maybe Ident -> C.Expr (Typed a) -> (Bound -> T a M.Expr) -> T a M.Expr
viaJoin ctx named expr k = do
  j <- freshJoin
  local <- freshLocal
  traverse_ (recordLocal local) named
  let rep = repAt ctx expr
  rest <- k { atom: M.ALocal local, rep }
  body <- go ctx (DJump j) expr
  pure (M.ELetJoin j [ { local, rep } ] rest body)

-- | The forms that are an atom or one computation.
-- | `expr` is the node as it stands, wrappers included. Dispatch is on what
-- | erasure leaves of it, while `expr` itself supplies the type and the
-- | annotation: a wrapper changes the type and spans the whole of what it wraps,
-- | so both belong to the outer node.
value :: forall a. Ctx -> C.Expr (Typed a) -> (Result -> T a M.Expr) -> T a M.Expr
value ctx expr k = case stripErased expr of
  C.Var _ name -> do
    bound <- lookupBound ctx name
    k (RAtom bound.atom)

  C.Lit _ literal -> k (RAtom (M.ALit literal))

  C.Global _ name _ -> case classify ctx name of
    Nothing -> throw (UnknownGlobal name)
    Just (HValue _) -> k (RAtom (M.AGlobal name))
    Just (HCtor 0) -> k (RAtom (M.ACtor name))
    Just (HCtor _) -> k (RComp (M.CPap (M.CalleeCtor name) []) RepClos)
    -- an arity-zero foreign saturates as soon as its spine is formed, so
    -- referring to it runs it; one of greater arity is a partial application.
    -- Both read the same classification, so an entry is an operation on either
    -- path or on neither
    Just (HForeign arity) -> do
      kind <- foreignKind name arity
      case kind, arity of
        Just op, 0 -> k (RComp (M.CPrim op []) (repAt ctx expr))
        Just op, _ -> k (RComp (M.CPap (M.CalleePrim op) []) RepClos)
        Nothing, 0 -> k (RComp (M.CForeign name []) (repAt ctx expr))
        Nothing, _ -> k (RComp (M.CPap (M.CalleeForeign name) []) RepClos)

  C.Lam _ _ _ _ -> do
    let run = lambdaRun expr
    lifted <- liftFunction ctx (sourceAt expr) run.params run.body
    k (RComp (M.CClosure lifted.func lifted.captures) RepClos)

  C.App _ _ _ -> application ctx expr k

  C.RecordEmpty _ -> k (RComp M.CRecordEmpty RepRec)

  C.RecordExtend _ key v rest ->
    atomize ctx v \a1 -> atomize ctx rest \a2 -> k (RComp (M.CRecordExtend key a1 a2) RepRec)

  C.RecordSelect _ key e ->
    atomize ctx e \a -> k (RComp (M.CRecordSelect key a) (repAt ctx expr))

  C.RecordRestrict _ key e ->
    atomize ctx e \a -> k (RComp (M.CRecordRestrict key a) RepRec)

  C.RecordUpdate _ key rec newValue ->
    atomize ctx rec \a1 -> atomize ctx newValue \a2 -> k (RComp (M.CRecordUpdate key a1 a2) RepRec)

  C.RecordMerge _ left right ->
    atomize ctx left \a1 -> atomize ctx right \a2 -> k (RComp (M.CRecordMerge a1 a2) RepRec)

  C.VariantInject _ key v ->
    atomize ctx v \a -> k (RComp (M.CInject key a) RepVariant)

  C.VariantAbsurd _ _ e ->
    atomize ctx e \a -> k (RComp (M.CAbsurd a) (repAt ctx expr))

  -- the type binders are erased with every other type application, and nothing
  -- consults the ambient row: the key is what a handler is found by
  C.Perform _ key op _ arg ->
    atomize ctx arg \a -> k (RComp (M.CPerform key op a) (repAt ctx expr))

  C.Handle _ body handler ->
    handled ctx (repAt ctx expr) body handler k

  -- the initial values are evaluated before the region opens, so the bindings
  -- naming them stand outside it and the body captures none of them
  C.Region _ name cells initial body ->
    withAtoms ctx initial \values -> do
      let keys = map _.key cells
      lifted <- liftRegionBody ctx (sourceAt body) name keys body
      k (RComp (M.CRegion keys lifted.func lifted.captures values) (repAt ctx expr))

  C.ReadCell _ name key -> do
    cell <- cellOf ctx name key
    k (RComp (M.CReadCell cell.region cell.index) (repAt ctx expr))

  C.WriteCell _ name key written -> do
    cell <- cellOf ctx name key
    atomize ctx written \a -> k (RComp (M.CWriteCell cell.region cell.index a) (repAt ctx expr))

  -- reached only through `go`, which handles these before delegating here
  _ -> throw ControlInValuePosition

-- Application ----------------------------------------------------------------

type Arg a =
  { value :: C.Expr (Typed a)
  -- | The type of applying the head to this argument and every one before it.
  , result :: Type
  }

type Spine a =
  { head :: C.Expr (Typed a)
  , args :: P.Array (Arg a)
  }

-- | The whole chain at once, looking through the forms erasure removes.
-- |
-- | **Looking through `openEff` is what makes a known call possible.** Widening
-- | is inserted once per argument consumed, so a saturated call to a pure global
-- | under a non-empty ambient row arrives wrapped several times over.
-- | **Peeling looks through the same wrappers dispatch does**, and through all
-- | of them: `weaken k [τ] (f x)` is an application under a wrapper that no
-- | other rule here would strip, and a peel that stopped at it would hand back
-- | the term it was given with no arguments taken off.
-- |
-- | The head comes back as it stands. A wrapper over it changes its type, and
-- | what it stands for is read by stripping it where that is wanted.
peel :: forall a. C.Expr (Typed a) -> Spine a
peel expr = case stripErased expr of
  C.App ann f x ->
    let
      s = peel f
    in
      s { args = Array.snoc s.args { value: x, result: ann.ty } }
  _ -> { head: expr, args: [] }

application :: forall a. Ctx -> C.Expr (Typed a) -> (Result -> T a M.Expr) -> T a M.Expr
application ctx expr k = do
  let spine = peel expr
  let whole = repAt ctx expr
  -- every argument reaches a value before any application happens (D35), and
  -- the vector keeps the source order
  withArgs ctx spine.args \atoms -> case stripErased spine.head of
    C.Global _ name _ -> case classify ctx name of
      Nothing -> throw (UnknownGlobal name)
      Just head -> saturate ctx spine head name atoms whole k
    -- the head as it stands, so that a wrapper over it keeps its type
    _ -> atomize ctx spine.head \callee ->
      k (RComp (M.CCallUnknown callee atoms) whole)

saturate
  :: forall a
   . Ctx
  -> Spine a
  -> Head
  -> Qualified Ident
  -> P.Array M.Atom
  -> Rep
  -> (Result -> T a M.Expr)
  -> T a M.Expr
saturate ctx spine head name atoms whole k = case head of
  HValue Nothing -> k (RComp (M.CCallUnknown (M.AGlobal name) atoms) whole)
  HValue (Just arity) -> split arity (M.CCallKnown name) (M.CalleeValue name)
  HForeign arity -> do
    kind <- foreignKind name arity
    case kind of
      -- the callee is the operation too: saturating a partial application of one
      -- runs the operation, not an implementation of that name
      Just op -> split arity (M.CPrim op) (M.CalleePrim op)
      Nothing -> split arity (M.CForeign name) (M.CalleeForeign name)
  HCtor arity -> split arity (M.CCtor name) (M.CalleeCtor name)
  where
  supplied = Array.length atoms

  split arity call callee
    | supplied == arity = k (RComp (call atoms) whole)
    | supplied < arity = k (RComp (M.CPap callee atoms) RepClos)
    | otherwise = do
        -- the saturated call runs, and the rest is applied to what it returns.
        -- Nothing moves: every argument is a value already
        local <- freshLocal
        let intermediate = resultAfter ctx spine arity
        M.ELet local intermediate (call (Array.take arity atoms))
          <$> k (RComp (M.CCallUnknown (M.ALocal local) (Array.drop arity atoms)) whole)

-- | The representation of what a spine has produced once `n` arguments are
-- | consumed, read off the application node that consumed the last of them.
resultAfter :: forall a. Ctx -> Spine a -> P.Int -> Rep
resultAfter ctx spine n = case Array.index spine.args (n - 1) of
  Just arg -> repOf ctx.signature arg.result
  Nothing -> RepVal

withArgs :: forall a. Ctx -> P.Array (Arg a) -> (P.Array M.Atom -> T a M.Expr) -> T a M.Expr
withArgs ctx args k = fromEnd (Array.length args - 1) []
  where
  fromEnd i acc
    | i < 0 = k acc
    | otherwise = case Array.index args i of
        Nothing -> k acc
        Just arg -> atomize ctx arg.value \atom -> fromEnd (i - 1) (Array.cons atom acc)

-- | Terms whose values are wanted in the order they are written.
withAtoms :: forall a. Ctx -> P.Array (C.Expr (Typed a)) -> (P.Array M.Atom -> T a M.Expr) -> T a M.Expr
withAtoms ctx exprs k = fromStart 0 []
  where
  fromStart i acc
    | i >= Array.length exprs = k acc
    | otherwise = case Array.index exprs i of
        Nothing -> k acc
        Just e -> atomize ctx e \atom -> fromStart (i + 1) (Array.snoc acc atom)

-- Handlers -------------------------------------------------------------------

-- | `handle e with h`, with the handled computation and every clause lifted into
-- | the function table.
handled
  :: forall a
   . Ctx
  -> Rep
  -> C.Expr (Typed a)
  -> C.Handler (Typed a)
  -> (Result -> T a M.Expr)
  -> T a M.Expr
handled ctx rep body handler k = do
  lifted <- liftFunction ctx (sourceAt body) [] body
  returnClause <- clauseRef ctx
    [ Tuple handler.returnClause.binder handler.returnClause.ty ]
    handler.returnClause.body
  opClauses <- traverse (opClauseRef ctx) handler.opClauses
  let
    h =
      { key: rowEntryKey handler.element
      , returnClause
      , opClauses
      }
  k (RComp (M.CHandle h lifted.func lifted.captures) rep)

-- | A function a handler reaches, over its own binders as parameters.
-- |
-- | The parameters are the clause's binders and nothing more: a body that is
-- | itself a lambda becomes a closure within the clause rather than a parameter
-- | of it, the arity being what the clause's form gives it.
clauseRef
  :: forall a
   . Ctx
  -> P.Array (Tuple Ident Type)
  -> C.Expr (Typed a)
  -> T a M.ClauseRef
clauseRef ctx params body = do
  lifted <- liftFunction ctx (sourceAt body) params body
  pure { func: lifted.func, captures: lifted.captures }

-- | **A clause's form is copied, never inferred** (D28). Whether a `full` clause
-- | resumes once cannot be read off its syntax, so Core writes the marker on
-- | every clause and this carries it through.
opClauseRef :: forall a. Ctx -> C.OpClause (Typed a) -> T a M.OpClauseRef
opClauseRef ctx = case _ of
  C.FullClause c -> do
    clause <- clauseRef ctx
      [ Tuple c.argBinder.name c.argBinder.ty
      , Tuple c.contBinder.name c.contBinder.ty
      ]
      c.body
    pure { op: c.op, form: M.ClauseFull, clause }
  C.FastClause c -> do
    clause <- clauseRef ctx [ Tuple c.argBinder.name c.argBinder.ty ] c.body
    pure { op: c.op, form: M.ClauseFast, clause }

-- Functions ------------------------------------------------------------------

-- | A run of adjacent lambdas, taken **after erasure**, so a type or constraint
-- | abstraction standing between two of them does not break it.
-- |
-- | Collapsing the run is what makes arity mean one thing: a saturated call site
-- | supplies the parameters of one entry rather than one at a time.
lambdaRun :: forall a. C.Expr (Typed a) -> { params :: P.Array (Tuple Ident Type), body :: C.Expr (Typed a) }
lambdaRun expr = case stripErased expr of
  C.Lam _ name ty body ->
    let
      r = lambdaRun body
    in
      r { params = Array.cons (Tuple name ty) r.params }
  e -> { params: [], body: e }

-- | Every wrapper erasure removes.
-- |
-- | All six have to go, and not the abstractions alone: `openEff` and the
-- | eliminations wrap a function as readily as the abstractions do, so a run
-- | stopping at one would read `openEff [ρ] (λx. e)` as taking no argument and
-- | leave every call to it a `callu`.
stripErased :: forall a. C.Expr (Typed a) -> C.Expr (Typed a)
stripErased = case _ of
  C.TyLam _ _ _ body -> stripErased body
  C.ConstraintLam _ _ body -> stripErased body
  C.TyApp _ e _ -> stripErased e
  C.ConstraintApp _ e -> stripErased e
  C.OpenEff _ _ e -> stripErased e
  C.VariantWeaken _ _ _ e -> stripErased e
  e -> e

paramBinder :: forall ann. Ctx -> Ident -> Type -> T ann { name :: Ident, binder :: M.Binder, bound :: Bound }
paramBinder ctx name ty = do
  local <- freshLocal
  recordLocal local name
  let rep = repOf ctx.signature ty
  pure { name, binder: { local, rep }, bound: { atom: M.ALocal local, rep } }

-- | Lift a body into the function table, over the free locals it needs.
-- |
-- | Join points are not among the captures: one does not cross a function
-- | boundary, so none of the enclosing scope's reaches the body.
-- | `source` is the annotation of the term the function was made from — the
-- | outermost node of the run, wrappers included, and not the body left after
-- | the lambdas are taken off. That term is what spans the definition.
liftFunction
  :: forall a
   . Ctx
  -> a
  -> P.Array (Tuple Ident Type)
  -> C.Expr (Typed a)
  -> T a { func :: M.FuncId, captures :: P.Array M.Atom }
liftFunction ctx source params = lift ctx source { region: Nothing, values: params }

-- | The body of a `region`, lifted into a function of one parameter: the
-- | region's identity.
liftRegionBody
  :: forall a
   . Ctx
  -> a
  -> RegionName
  -> P.Array RowKey
  -> C.Expr (Typed a)
  -> T a { func :: M.FuncId, captures :: P.Array M.Atom }
liftRegionBody ctx source name keys =
  lift ctx source { region: Just { name, keys }, values: [] }

-- | A function's parameters: the identity of a region where it is the body of
-- | one, then the Core variables it binds.
type Params =
  { region :: Maybe { name :: RegionName, keys :: P.Array RowKey }
  , values :: P.Array (Tuple Ident Type)
  }

-- | **A region's identity is captured like a local.** A function using the
-- | cells of a region it does not open reaches them through the identity it
-- | captured, which is the one of the opening its closure was made under, and
-- | the captures list the region identities after the locals.
lift
  :: forall a
   . Ctx
  -> a
  -> Params
  -> C.Expr (Typed a)
  -> T a { func :: M.FuncId, captures :: P.Array M.Atom }
lift ctx source params body = do
  let free = freeVars body
  let bracketed = Set.fromFoldable (map (\(Tuple name _) -> name) params.values)
  let captured = Array.filter (isCaptured ctx) (Set.toUnfoldable (Set.difference free.values bracketed))
  let opened = Set.fromFoldable (map _.name params.region)
  let capturedRegions = Set.toUnfoldable (Set.difference free.regions opened) :: P.Array RegionName
  -- what the enclosing function supplies, read before the numbering changes
  outers <- traverse (\name -> _.atom <$> lookupBound ctx name) captured
  outerRegions <- traverse (\name -> _.identity <$> lookupRegion ctx name) capturedRegions
  func <- freshFunc
  recordFunction func (Just source)
  inFunction func do
    regionInfos <- traverse (\r -> regionBinder r.name r.keys) (Array.fromFoldable params.region)
    paramInfos <- traverse (\(Tuple name ty) -> paramBinder ctx name ty) params.values
    captureInfos <- traverse (captureBinder ctx) captured
    regionCaptureInfos <- traverse (regionCaptureBinder ctx) capturedRegions
    let
      inner = ctx
        { locals =
            foldl (\acc info -> Map.insert info.name info.bound acc)
              (foldl (\acc info -> Map.insert info.name info.bound acc) ctx.locals captureInfos)
              paramInfos
        , regions =
            foldl (\acc info -> Map.insert info.name info.bound acc) ctx.regions
              (regionInfos <> regionCaptureInfos)
        , joins = Map.empty
        }
    translated <- go inner DRet body
    emitFunction
      { id: func
      , params: map _.binder regionInfos <> map _.binder paramInfos
      , captures: map _.binder captureInfos <> map _.binder regionCaptureInfos
      , body: translated
      }
    pure { func, captures: outers <> outerRegions }

-- | A variable standing for a global, a literal, or a nullary constructor needs
-- | no capture: the lifted body names it directly.
isCaptured :: Ctx -> Ident -> P.Boolean
isCaptured ctx name = case Map.lookup name ctx.locals of
  Just { atom: M.ALocal _ } -> true
  _ -> false

captureBinder :: forall ann. Ctx -> Ident -> T ann { name :: Ident, binder :: M.Binder, bound :: Bound, outer :: M.Atom }
captureBinder ctx name = do
  bound <- lookupBound ctx name
  local <- freshLocal
  recordLocal local name
  pure
    { name
    , binder: { local, rep: bound.rep }
    , bound: { atom: M.ALocal local, rep: bound.rep }
    , outer: bound.atom
    }

-- | The parameter holding a region's identity. Nothing is known of an identity
-- | but that it is a value.
regionBinder :: forall ann. RegionName -> P.Array RowKey -> T ann { name :: RegionName, binder :: M.Binder, bound :: RegionBound }
regionBinder name keys = do
  local <- freshLocal
  pure { name, binder: { local, rep: RepVal }, bound: { identity: M.ALocal local, keys } }

regionCaptureBinder :: forall ann. Ctx -> RegionName -> T ann { name :: RegionName, binder :: M.Binder, bound :: RegionBound }
regionCaptureBinder ctx name = do
  region <- lookupRegion ctx name
  regionBinder name region.keys

-- | A local recursive group. Every closure is allocated before any capture list
-- | is filled, so a member may capture its neighbours.
recursiveGroup
  :: forall a
   . Ctx
  -> P.Array { name :: Ident, ty :: Type, value :: C.Expr (Typed a) }
  -> T a { ctx :: Ctx, bindings :: P.Array M.RecBinding }
recursiveGroup ctx bindings = do
  infos <- traverse (\b -> paramBinder ctx b.name b.ty) bindings
  let inner = foldl (\acc info -> Map.insert info.name info.bound acc) ctx.locals infos
  let ctx' = ctx { locals = inner }
  lifted <- traverse (liftOne ctx') bindings
  pure
    { ctx: ctx'
    , bindings:
        Array.zipWith
          (\info l -> { local: info.binder.local, rep: info.binder.rep, func: l.func, captures: l.captures })
          infos
          lifted
    }
  where
  liftOne ctx' b = do
    let run = lambdaRun b.value
    liftFunction ctx' (sourceAt b.value) run.params run.body

-- Decision trees -------------------------------------------------------------

seedOccurrences :: P.Array M.Atom -> Map C.Occurrence M.Atom
seedOccurrences atoms =
  Map.fromFoldable (Array.mapWithIndex (\i atom -> Tuple (C.OccScrutinee i) atom) atoms)

decisionTree
  :: forall a
   . Ctx
  -> Dest
  -> Map C.Occurrence Type
  -> Map C.Occurrence M.Atom
  -> C.DecisionTree (Typed a)
  -> T a M.Expr
decisionTree ctx dest types atoms dt = case dt of
  C.Leaf e -> go ctx dest e

  -- a bind whose occurrence is already materialized aliases that local rather
  -- than creating one, so only the first name reaches the debug table
  C.Bind name occurrence inner -> do
    let created = Map.lookup occurrence atoms == Nothing
    materialize ctx types atoms occurrence \atoms' atom -> do
      case atom of
        M.ALocal local | created -> recordLocal local name
        _ -> pure unit
      decisionTree (bindLocal ctx name { atom, rep: occurrenceRep ctx types occurrence }) dest types atoms' inner

  C.SwitchCtor occurrence branches fallback ->
    materialize ctx types atoms occurrence \atoms' atom -> do
      branches' <- traverse
        ( \branch -> do
            body <- decisionTree ctx dest types atoms' branch.tree
            pure { ctor: branch.ctor, body }
        )
        branches
      fallback' <- traverse (decisionTree ctx dest types atoms') fallback
      pure (M.ESwitchCtor atom branches' fallback')

  C.SwitchLit occurrence branches fallback ->
    materialize ctx types atoms occurrence \atoms' atom -> do
      branches' <- traverse
        ( \branch -> do
            body <- decisionTree ctx dest types atoms' branch.tree
            pure { lit: branch.lit, body }
        )
        branches
      fallback' <- decisionTree ctx dest types atoms' fallback
      pure (M.ESwitchLit atom branches' fallback')

  C.SwitchKey occurrence branches fallback ->
    materialize ctx types atoms occurrence \atoms' atom -> do
      branches' <- traverse
        ( \branch -> do
            body <- decisionTree ctx dest types atoms' branch.tree
            pure { key: branch.key, body }
        )
        branches
      fallback' <- traverse (decisionTree ctx dest types atoms') fallback
      pure (M.ESwitchKey atom branches' fallback')

  C.Guard condition consequent alternative ->
    atomize ctx condition \atom -> do
      c <- decisionTree ctx dest types atoms consequent
      a <- decisionTree ctx dest types atoms alternative
      pure (M.EIf atom c a)

occurrenceRep :: Ctx -> Map C.Occurrence Type -> C.Occurrence -> Rep
occurrenceRep ctx types occurrence =
  fromMaybe RepVal (map (repOf ctx.signature) (Map.lookup occurrence types))

-- | A path, projected where it is first used and nowhere earlier.
-- |
-- | A field of a constructor exists only under the dispatch that selected that
-- | constructor, so projecting one before it would read a value that is not
-- | there. The map is what keeps a repeated path from being projected twice.
materialize
  :: forall a
   . Ctx
  -> Map C.Occurrence Type
  -> Map C.Occurrence M.Atom
  -> C.Occurrence
  -> (Map C.Occurrence M.Atom -> M.Atom -> T a M.Expr)
  -> T a M.Expr
materialize ctx types atoms occurrence k = case Map.lookup occurrence atoms of
  Just atom -> k atoms atom
  Nothing -> case occurrence of
    C.OccScrutinee _ -> throw (UnresolvedOccurrence occurrence)
    C.OccField base ctor index ->
      project base (\atom -> M.CField atom ctor index)
    C.OccRecordField base key ->
      project base (M.CRecordSelect key)
    C.OccVariantPayload base key ->
      project base (M.CPayload key)
  where
  project base build =
    materialize ctx types atoms base \atoms' baseAtom -> do
      local <- freshLocal
      let rep = occurrenceRep ctx types occurrence
      M.ELet local rep (build baseAtom)
        <$> k (Map.insert occurrence (M.ALocal local) atoms') (M.ALocal local)

-- Free variables -------------------------------------------------------------

-- | What a term names from outside it: value variables, and the regions whose
-- | cells it reaches.
-- |
-- | Global names are not among them, being named directly, and neither are join
-- | points, which are not values.
type Free =
  { values :: Set Ident
  , regions :: Set RegionName
  }

value' :: Ident -> Free
value' name = { values: Set.singleton name, regions: Set.empty }

region' :: RegionName -> Free
region' name = { values: Set.empty, regions: Set.singleton name }

withoutValues :: P.Array Ident -> Free -> Free
withoutValues names free = free { values = Set.difference free.values (Set.fromFoldable names) }

withoutRegion :: RegionName -> Free -> Free
withoutRegion name free = free { regions = Set.delete name free.regions }

-- | The free value variables and region names of a term. A `region` binds its
-- | name in its body and not in its initial values, which are evaluated before
-- | it opens.
freeVars :: forall a. C.Expr a -> Free
freeVars = case _ of
  C.Var _ name -> value' name
  C.Global _ _ _ -> mempty
  C.Lit _ _ -> mempty
  C.Lam _ name _ body -> withoutValues [ name ] (freeVars body)
  C.App _ f x -> freeVars f <> freeVars x
  C.TyLam _ _ _ body -> freeVars body
  C.TyApp _ e _ -> freeVars e
  C.ConstraintLam _ _ body -> freeVars body
  C.ConstraintApp _ e -> freeVars e
  C.Let _ name _ rhs body -> freeVars rhs <> withoutValues [ name ] (freeVars body)
  C.LetRec _ bindings body ->
    withoutValues (map _.name bindings)
      (foldMap (freeVars <<< _.value) bindings <> freeVars body)
  C.Case _ scrutinees dt -> foldMap freeVars scrutinees <> freeVarsTree dt
  C.LetJoin _ _ params _ definitionBody body ->
    withoutValues (map _.name params) (freeVars definitionBody) <> freeVars body
  C.Jump _ _ args -> foldMap freeVars args
  C.RecordEmpty _ -> mempty
  C.RecordExtend _ _ v rest -> freeVars v <> freeVars rest
  C.RecordSelect _ _ e -> freeVars e
  C.RecordRestrict _ _ e -> freeVars e
  C.RecordUpdate _ _ rec newValue -> freeVars rec <> freeVars newValue
  C.RecordMerge _ left right -> freeVars left <> freeVars right
  C.VariantInject _ _ e -> freeVars e
  C.VariantWeaken _ _ _ e -> freeVars e
  C.VariantAbsurd _ _ e -> freeVars e
  C.Perform _ _ _ _ arg -> freeVars arg
  C.Handle _ body handler ->
    freeVars body
      <> withoutValues [ handler.returnClause.binder ] (freeVars handler.returnClause.body)
      <> foldMap freeVarsClause handler.opClauses
  C.Region _ name _ initial body -> foldMap freeVars initial <> withoutRegion name (freeVars body)
  C.ReadCell _ name _ -> region' name
  C.WriteCell _ name _ written -> region' name <> freeVars written
  C.OpenEff _ _ e -> freeVars e

freeVarsClause :: forall a. C.OpClause a -> Free
freeVarsClause = case _ of
  C.FullClause c ->
    withoutValues [ c.argBinder.name, c.contBinder.name ] (freeVars c.body)
  C.FastClause c ->
    withoutValues [ c.argBinder.name ] (freeVars c.body)

freeVarsTree :: forall a. C.DecisionTree a -> Free
freeVarsTree = case _ of
  C.Leaf e -> freeVars e
  C.Bind name _ inner -> withoutValues [ name ] (freeVarsTree inner)
  C.SwitchCtor _ branches fallback ->
    foldMap (freeVarsTree <<< _.tree) branches <> foldMap freeVarsTree fallback
  C.SwitchLit _ branches fallback ->
    foldMap (freeVarsTree <<< _.tree) branches <> freeVarsTree fallback
  C.SwitchKey _ branches fallback ->
    foldMap (freeVarsTree <<< _.tree) branches <> foldMap freeVarsTree fallback
  C.Guard condition consequent alternative ->
    freeVars condition <> freeVarsTree consequent <> freeVarsTree alternative

-- Modules --------------------------------------------------------------------

-- | A checked module, lowered.
-- |
-- | The header and the type-level declarations come from the module as it was
-- | written; the value declarations come from checking, which annotated them.
-- | The module and the debug table beside it, which `lower` fills a `.dmo`'s
-- | `DEBUG` section from and may discard.
-- |
-- | **The imports are what make a call to an imported value a known one.** A
-- | definitional arity is a property of a right-hand side, so for a value of this
-- | module it is read off the term and for an imported one it comes from that
-- | module's interface, checked where the environment was assembled and read through
-- | this module's import list ([Interface](../Interface.purs)). An arity neither
-- | source holds costs a `callk` and nothing else: the call is a `callu`, which is
-- | correct for every callee.
translate
  :: forall a
   . Imports
  -> D.Module a
  -> Declared a
  -> Either TranslateError { module :: M.Module, debug :: M.Debug a }
translate imports m declared =
  case runT initialState (traverse (globalOf ctx m.name) declared.values) of
    Left err -> Left err
    Right (Tuple globals final) -> Right
      { module:
          { name: m.name
          , imports: m.imports
          , ctors: Array.concatMap (ctorEntries m.name) m.decls
          , effects: Array.mapMaybe (effectEntry m.name) m.decls
          , foreigns: Array.mapMaybe (foreignEntry m.name) m.decls
          , functions: Array.fromFoldable (Map.values final.functions)
          , globals: Array.concat globals
          , exports: Array.mapMaybe (exportEntry m.name) m.exports
          }
      , debug: final.debug
      }
  where
  initialState =
    { nextLocal: 0
    , nextJoin: 0
    , nextFunc: 0
    , currentFunc: Nothing
    , functions: Map.empty
    , debug: M.emptyDebug
    }

  ctx =
    { signature: declared.signature
    , locals: Map.empty
    , regions: Map.empty
    , joins: Map.empty
    -- an arity is taken from the environment for the modules this one depends
    -- on, and this one speaks for its own
    , arities:
        Map.union (definitionalArities m.name declared)
          (importedArities m.name m.imports imports)
    }

-- | The number of leading lambdas a top-level right-hand side has, where it has
-- | any.
-- |
-- | **Absent is not zero.** A right-hand side that is not a lambda stores
-- | whatever it evaluates to, which is a function of that value's own arity;
-- | reading zero there would make every call to it an over-application.
definitionalArities :: forall a. ModuleName -> Declared a -> Map (Qualified Ident) P.Int
definitionalArities moduleName declared =
  foldl add Map.empty (Array.concatMap _.bindings declared.values)
  where
  add acc binding = case lambdaRun binding.value of
    run | Array.length run.params > 0 ->
      Map.insert (Qualified moduleName binding.name) (Array.length run.params) acc
    _ -> acc

-- | How a top-level value is installed, which **the shape of its right-hand side
-- | decides and not the form of its declaration**.
-- |
-- | A right-hand side that is a lambda once erasure has looked through the
-- | wrappers becomes the function itself, installed as a closure over an empty
-- | capture list: at the top level every free name is a global, so there is
-- | nothing to capture and nothing to evaluate. Anything else becomes a
-- | function of no parameters, evaluated once when the module is initialized.
-- |
-- | This is the same test the definitional arity is read by, which is what makes
-- | the two agree: a global reached by `callk` holds a function of that arity,
-- | and one that is evaluated has no definitional arity at all.
globalOf :: forall a. Ctx -> ModuleName -> CheckedGroup a -> T a (P.Array M.GlobalEntry)
globalOf ctx moduleName group = traverse one group.bindings
  where
  one binding = do
    let run = lambdaRun binding.value
    lifted <-
      if Array.null run.params then liftFunction ctx (sourceAt binding.value) [] binding.value
      else liftFunction ctx (sourceAt binding.value) run.params run.body
    nameFunction lifted.func (Qualified moduleName binding.name)
    pure
      { ref: Qualified moduleName binding.name
      , init:
          if Array.null run.params then M.GRun lifted.func
          else M.GFunc lifted.func
      }

ctorEntries :: forall a. ModuleName -> D.Decl a -> P.Array M.CtorEntry
ctorEntries moduleName = case _ of
  D.DeclData _ decl ->
    map
      ( \ctor ->
          { ref: Qualified moduleName ctor.name
          , owner: Qualified moduleName decl.name
          , tag: ctor.tag
          , arity: Array.length ctor.fields
          , isNewtype: decl.isNewtype
          }
      )
      decl.constructors
  _ -> []

effectEntry :: forall a. ModuleName -> D.Decl a -> Maybe M.EffectEntry
effectEntry moduleName = case _ of
  D.DeclEffect _ decl ->
    Just { ref: Qualified moduleName decl.name, ops: map _.name decl.operations }
  _ -> Nothing

foreignEntry :: forall a. ModuleName -> D.Decl a -> Maybe M.ForeignEntry
foreignEntry moduleName = case _ of
  D.DeclForeign _ decl ->
    Just { ref: Qualified moduleName decl.name, arity: foreignArity decl.scheme }
  _ -> Nothing

exportEntry :: ModuleName -> D.Export -> Maybe (Qualified Ident)
exportEntry moduleName = case _ of
  D.ExportValue name -> Just (Qualified moduleName name)
  _ -> Nothing

