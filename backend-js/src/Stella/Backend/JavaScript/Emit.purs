-- | Frame IR written out as an ES module.
-- |
-- | One `.dmo` becomes one module. What it binds, and what those bindings are
-- | named:
-- |
-- | | Binding | What it holds |
-- | | --- | --- |
-- | | `rt` | the runtime, imported whole |
-- | | `iK_g_x`, `iK_c_X` | the global `x` and the constructor `X` of the `K`-th module of `IMPORTS` |
-- | | `iK_arities` | that module's table of definitional arities |
-- | | `cI` | the descriptor of the `I`-th constructor this module declares |
-- | | `pI` | the `I`-th operation of `PRIMS`, standing as a callee |
-- | | `fnI` | the descriptor of the `I`-th function |
-- | | `fI_sJ` | segment `J` of that function |
-- | | `gI` | the `I`-th global |
-- |
-- | **What another module reads is exported under a name no binding can clash
-- | with**: a global under its own name, a constructor as `"ctor Name"`, and the
-- | table of definitional arities as `"arity table"`. The last two hold spaces, so
-- | no Stella identifier is either of them.
-- |
-- | **Every name another module is referred to by is imported by that name**: each
-- | imported name that `GLOBALREFS`, `CTORREFS`, or `CALLEES` holds is imported
-- | once, however many entries hold it, and whether or not anything then reads
-- | the binding. Linking the modules therefore
-- | refuses a reference to what the module declaring it does not export, before
-- | anything runs, which is where Steam refuses one
-- | ([Abstract Machine](../../../../../docs/technical-references/07-Runtime/01-Abstract-Machine.md)).
-- | Every module of `IMPORTS` is imported, the arity table at least, so an imported
-- | module is initialized before this one whether or not anything of it is named,
-- | which is the order module initialization owes
-- | ([Bytecode](../../../../../docs/technical-references/05-Backend/01-Bytecode.md)).
module Stella.Backend.JavaScript.Emit
  ( Options
  , emit
  , fileName
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Enum (fromEnum)
import Data.Int (hexadecimal, toStringAs)
import Data.String as String
import Data.String.CodePoints as CodePoints
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Stella.Compiler.Bytecode.Instr (FuncIx(..))
import Stella.Compiler.Bytecode.Module (GlobalInit(..))
import Stella.Backend.JavaScript.Error (JsError(..))
import Stella.Backend.JavaScript.Frame (Block, Callee(..), CtorRef(..), Exit(..), Expr(..), FrameFunction, GlobalRef(..), Literal(..), SegmentId(..), Stmt(..), Target(..))
import Stella.Backend.JavaScript.Operation (inline)
import Stella.Backend.JavaScript.Syntax as S
import Stella.Backend.JavaScript.ToFrame (FrameModule)
import Stella.Compiler.Primitive (PrimOp, arityOfOp, entryOfOp, lookupPrim)
import Stella.Compiler.TypedCore.Domain (textOf)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))

-- | `runtime` is the specifier generated code imports the runtime by.
type Options = { runtime :: P.String }

-- | The file a module is written to, which is also how another generated module
-- | imports it: `./` followed by this.
fileName :: ModuleName -> P.String
fileName (ModuleName m) = m <> ".js"

emit :: Options -> FrameModule -> Either JsError S.Module
emit options fm = do
  foreignsChecked
  functionsOut <- traverse (functionTops fm) fm.functions
  pure $
    [ S.ImportAll "rt" options.runtime ]
      <> Array.mapWithIndex (importTop fm) dmo.imports
      <> map S.Statement importChecks
      <> Array.mapWithIndex ctorTop dmo.ctors
      <> Array.mapWithIndex primTop dmo.prims
      <> Array.concat functionsOut
      <> Array.mapWithIndex (\i _ -> S.Statement (S.Let (globalName i) Nothing)) dmo.globals
      <> Array.mapWithIndex initTop dmo.globals
      <> [ S.Statement (S.Const "arities" (S.Call (S.Member (S.Ident "Object") "freeze") [ arityTable ])) ]
      <> [ S.Export (exportedGlobals <> exportedCtors <> [ Tuple "arities" "arity table" ]) ]
  where
  dmo = fm.dmo

  -- A foreign this module declares is carried out by the backend where the ABI
  -- fixes it as an operation, and needs nothing emitted; any other is supplied by
  -- a host implementation, which this backend does not reach yet.
  foreignsChecked = case Array.find (\f -> lookupPrim f.name == Nothing) dmo.foreigns of
    Just f -> Left (Unsupported ("the foreign declaration " <> qualifiedText f.name))
    Nothing -> Right unit

  ctorTop i c =
    S.Statement (S.Const (ctorName i) (rtCall "ctor" [ S.String (qualifiedText c.name), S.Number (show c.arity) ]))

  primTop i op =
    let
      params = Array.mapWithIndex (\j _ -> "a" <> show j) (Array.replicate (arityOfOp op) unit)
    in
      S.Statement
        ( S.Const (primName i)
            ( rtCall "prim"
                [ S.String (qualifiedText (entryOfOp op))
                , S.Number (show (arityOfOp op))
                , S.Arrow params (operation op (map S.Ident params))
                ]
            )
        )

  initTop i g = S.Statement case g.init of
    GFunc (FuncIx f) -> S.Assign (S.Ident (globalName i)) (S.New (rtMember "Closure") [ S.Ident (fnName f), S.Array [] ])
    -- a fault ending initialization says which global it ended at
    GRun (FuncIx f) -> S.Assign (S.Ident (globalName i)) (rtCall "initialize" [ S.String (qualifiedText g.name), S.Ident (fnName f) ])

  ownGlobalIndex q = Array.findIndex (\g -> g.name == q) dmo.globals

  exportedGlobals = Array.mapMaybe
    ( \q@(Qualified _ (Ident x)) -> do
        i <- ownGlobalIndex q
        pure (Tuple (globalName i) x)
    )
    dmo.exports

  exportedCtors = Array.mapWithIndex (\i c -> let Qualified _ (Ident x) = c.name in Tuple (ctorName i) ("ctor " <> x)) dmo.ctors

  -- the definitional arity of each exported global installed as a function; a
  -- global evaluated at initialization has none and is absent
  arityTable = S.Call (S.Member (S.Ident "Object") "fromEntries")
    [ S.Array $ Array.mapMaybe
        ( \q@(Qualified _ (Ident x)) -> do
            i <- ownGlobalIndex q
            g <- Array.index dmo.globals i
            case g.init of
              GFunc (FuncIx f) -> do
                func <- Array.index dmo.functions f
                pure (S.Array [ S.String x, S.Number (show func.nparams) ])
              GRun _ -> Nothing
        )
        dmo.exports
    ]

  importChecks = map snd' (Array.nubBy (\a b -> compare (fst a) (fst b)) (Array.concatMap checksOf fm.functions))

  snd' (Tuple _ s) = s

  checksOf f = Array.concatMap (\s -> blockChecks s.body) f.segments

  blockChecks :: Block -> P.Array (Tuple P.String S.Stmt)
  blockChecks b = Array.concatMap stmtChecks b.stmts <> exitChecks b.exit

  stmtChecks = case _ of
    Set _ e -> exprChecks e
    _ -> []

  exprChecks = case _ of
    CtorValue ref -> ctorCheck ref 0 true
    Construct ref args -> ctorCheck ref (Array.length args) true
    Pap (CalleeCtor ref) args -> ctorCheck ref (Array.length args) false
    Pap (CalleeGlobal (ImportedGlobal m x)) args -> globalCheck "expectPartial" m x (Array.length args)
    _ -> []

  exitChecks = case _ of
    Call c -> targetChecks c.target (Array.length c.args)
    TailCall c -> targetChecks c.target (Array.length c.args)
    If _ a b -> blockChecks a <> blockChecks b
    SwitchCtor _ cases d -> Array.concatMap (blockChecks <<< _.body) cases <> maybe' d
    SwitchLit _ cases d -> Array.concatMap (blockChecks <<< _.body) cases <> blockChecks d
    SwitchKey _ cases d -> Array.concatMap (blockChecks <<< _.body) cases <> maybe' d
    _ -> []

  maybe' = case _ of
    Just b -> blockChecks b
    Nothing -> []

  targetChecks to count = case to of
    TargetGlobal (ImportedGlobal m x) -> globalCheck "expectCall" m x count
    _ -> []

  globalCheck how m (Ident name) count =
    let
      ModuleName mn = m
      key = how <> " " <> mn <> "." <> name <> " " <> show count
    in
      [ Tuple key
          ( S.ExprStmt
              ( rtCall how
                  [ arityTableOf fm m
                  , S.String mn
                  , S.String name
                  , S.Number (show count)
                  ]
              )
          )
      ]

  ctorCheck ref count saturated = case ref of
    ImportedCtor (ModuleName mn) (Ident x) ->
      [ Tuple ("ctor " <> mn <> "." <> x <> " " <> show count <> " " <> show saturated)
          (S.ExprStmt (rtCall "expectCtor" [ ctorExpr fm ref, S.Number (show count), S.Boolean saturated ]))
      ]
    _ -> []

-- Functions -----------------------------------------------------------------------------

functionTops :: FrameModule -> FrameFunction -> Either JsError (P.Array S.Top)
functionTops fm f = do
  segments <- traverse segmentTop f.segments
  pure $ segments <>
    [ S.Statement
        ( S.Const (fnName f.index)
            ( rtCall "fn"
                [ S.String (fromMaybe (moduleText fm.dmo.name <> ".#" <> show f.index) f.name)
                , S.Number (show f.arity)
                , S.Number (show f.registers)
                , S.Ident (segmentName f.entry)
                ]
            )
        )
    ]
  where
  segmentTop s = do
    body <- block fm s.body
    pure (S.Statement (S.Function (segmentName s.id) [ "m", "f" ] ([ S.Const "r" (S.Member (S.Ident "f") "r") ] <> body)))

block :: FrameModule -> Block -> Either JsError (P.Array S.Stmt)
block fm b = do
  let stmts = map (stmt fm) b.stmts
  exitOut <- exit fm b.exit
  pure (stmts <> exitOut)

stmt :: FrameModule -> Stmt -> S.Stmt
stmt fm = case _ of
  Set d e -> S.Assign (reg d) (expr fm e)
  SetCapture d i s -> S.Assign (S.Index (S.Member (reg d) "caps") (S.Number (show i))) (reg s)
  Unreachable what -> S.ExprStmt (rtCall "unreachable" [ S.String what ])

exit :: FrameModule -> Exit -> Either JsError (P.Array S.Stmt)
exit fm = case _ of
  Return s ->
    pure [ S.Assign (mField "value") (reg s), S.Return (rtMember "RET") ]
  Call c ->
    pure
      [ S.Assign (mField "callee") (target fm c.target)
      , S.Assign (mField "args") (S.Array (map reg c.args))
      , S.Assign (mField "dest") (S.Number (show c.dest))
      , S.Assign (mField "resume") (S.Ident (segmentName c.resume))
      , S.Return (rtMember "CALL")
      ]
  TailCall c ->
    pure
      [ S.Assign (mField "callee") (target fm c.target)
      , S.Assign (mField "args") (S.Array (map reg c.args))
      , S.Return (rtMember "TAIL")
      ]
  -- the arguments are read before any parameter is written, since an argument
  -- register may be a parameter of the join point too
  Jump j ->
    let
      moves = Array.filter (\(Tuple p a) -> p /= a) j.moves
      temps = Array.mapWithIndex (\k (Tuple _ a) -> S.Const ("t" <> show k) (reg a)) moves
      writes = Array.mapWithIndex (\k (Tuple p _) -> S.Assign (reg p) (S.Ident ("t" <> show k))) moves
    in
      pure [ S.Block (temps <> writes), S.Assign (mField "seg") (S.Ident (segmentName j.join)), S.Return (rtMember "RUN") ]
  If s yes no -> do
    a <- block fm yes
    b <- block fm no
    pure [ S.If (reg s) a b ]
  SwitchCtor s cases default -> do
    cs <- traverse (\c -> { label: ctorExpr fm c.ctor, body: _ } <$> block fm c.body) cases
    d <- defaultBlock default "no constructor matched"
    pure [ S.Switch (S.Member (reg s) "c") cs (Just d) ]
  SwitchKey s cases default -> do
    cs <- traverse (\c -> { label: S.String c.key, body: _ } <$> block fm c.body) cases
    d <- defaultBlock default "no key matched"
    pure [ S.Switch (S.Member (reg s) "k") cs (Just d) ]
  SwitchLit s cases default -> do
    cs <- traverse (\c -> Tuple c.lit <$> block fm c.body) cases
    d <- block fm default
    pure
      if Array.all (isNumber <<< fst) cs then [ numberDispatch s cs d ]
      else [ S.Switch (reg s) (map (\(Tuple l body) -> { label: literal l, body }) cs) (Just d) ]
  where
  defaultBlock default what = case default of
    Just b -> block fm b
    Nothing -> pure [ S.ExprStmt (rtCall "unreachable" [ S.String what ]) ]

  isNumber = case _ of
    LitNumber _ -> true
    _ -> false

-- | A `Number` dispatch compares by literal identity, which a `switch`'s strict
-- | equality does not implement: it identifies `0.0` with `-0.0` and separates a
-- | NaN from itself (D37).
numberDispatch :: P.Int -> P.Array (Tuple Literal (P.Array S.Stmt)) -> P.Array S.Stmt -> S.Stmt
numberDispatch s cases default = case Array.uncons cases of
  Nothing -> S.Block default
  Just { head: Tuple l body, tail } ->
    S.If (rtCall "sameNumber" [ reg s, literal l ]) body [ numberDispatch s tail default ]

expr :: FrameModule -> Expr -> S.Expr
expr fm = case _ of
  Reg s -> reg s
  Capture i -> S.Index (S.Member (S.Ident "f") "caps") (S.Number (show i))
  Lit l -> literal l
  Global ref -> globalExpr fm ref
  CtorValue ref -> S.Member (ctorExpr fm ref) "value"
  Closure f args -> S.New (rtMember "Closure") [ S.Ident (fnName f), S.Array (map reg args) ]
  OpenClosure f n -> S.New (rtMember "Closure") [ S.Ident (fnName f), S.New (S.Ident "Array") [ S.Number (show n) ] ]
  Pap c args -> S.New (rtMember "Pap") [ calleeExpr fm c, S.Array (map reg args) ]
  Construct ref args -> S.New (rtMember "Data") [ ctorExpr fm ref, S.Array (map reg args) ]
  Field s ref j -> rtCall "field" [ reg s, ctorExpr fm ref, S.Number (show j) ]
  RecordEmpty -> rtMember "emptyRecord"
  RecordExtend k v r -> rtCall "extend" [ reg r, S.String k, reg v ]
  RecordSelect k s -> rtCall "select" [ reg s, S.String k ]
  RecordRestrict k s -> rtCall "restrict" [ reg s, S.String k ]
  RecordUpdate k r v -> rtCall "update" [ reg r, S.String k, reg v ]
  RecordMerge a b -> rtCall "merge" [ reg a, reg b ]
  Inject k s -> S.New (rtMember "Variant") [ S.String k, reg s ]
  Payload k s -> rtCall "payload" [ reg s, S.String k ]
  Prim op args -> operation op (map reg args)

operation :: PrimOp -> P.Array S.Expr -> S.Expr
operation op args = inline op args

target :: FrameModule -> Target -> S.Expr
target fm = case _ of
  TargetGlobal ref -> globalExpr fm ref
  TargetReg s -> reg s

calleeExpr :: FrameModule -> Callee -> S.Expr
calleeExpr fm = case _ of
  CalleeGlobal ref -> globalExpr fm ref
  CalleeCtor ref -> ctorExpr fm ref
  CalleePrim i -> S.Ident (primName i)

globalExpr :: FrameModule -> GlobalRef -> S.Expr
globalExpr fm = case _ of
  OwnGlobal i -> S.Ident (globalName i)
  ImportedGlobal m x -> S.Ident (importedName fm m "g" x)

ctorExpr :: FrameModule -> CtorRef -> S.Expr
ctorExpr fm = case _ of
  OwnCtor i -> S.Ident (ctorName i)
  ImportedCtor m x -> S.Ident (importedName fm m "c" x)
  PrimUnit -> rtMember "PrimUnit"

-- | The import of the `K`-th module of `IMPORTS`: every global and constructor of
-- | it that a table of this module names, and its arity table.
importTop :: FrameModule -> P.Int -> ModuleName -> S.Top
importTop fm k m =
  S.ImportNamed
    ( map (\x@(Ident name) -> Tuple name (importedLocal k "g" x)) globals
        <> map (\x@(Ident name) -> Tuple ("ctor " <> name) (importedLocal k "c" x)) ctors
        <> [ Tuple "arity table" (arityLocal k) ]
    )
    ("./" <> fileName m)
  where
  globals = Array.nub
    ( Array.mapMaybe globalOf fm.resolved.globals
        <> Array.mapMaybe
          ( case _ of
              CalleeGlobal ref -> globalOf ref
              _ -> Nothing
          )
          fm.resolved.callees
    )
  ctors = Array.nub
    ( Array.mapMaybe ctorOf fm.resolved.ctors
        <> Array.mapMaybe
          ( case _ of
              CalleeCtor ref -> ctorOf ref
              _ -> Nothing
          )
          fm.resolved.callees
    )
  globalOf = case _ of
    ImportedGlobal m' x | m' == m -> Just x
    _ -> Nothing
  ctorOf = case _ of
    ImportedCtor m' x | m' == m -> Just x
    _ -> Nothing

-- | The binding an imported global (`kind` "g") or constructor ("c") is bound to.
-- | Resolution refused a reference to a module not imported, so the module is
-- | always found.
importedName :: FrameModule -> ModuleName -> P.String -> Ident -> P.String
importedName fm m kind x = importedLocal (moduleIndex fm m) kind x

arityTableOf :: FrameModule -> ModuleName -> S.Expr
arityTableOf fm m = S.Ident (arityLocal (moduleIndex fm m))

moduleIndex :: FrameModule -> ModuleName -> P.Int
moduleIndex fm m = fromMaybe (-1) (Array.elemIndex m fm.dmo.imports)

importedLocal :: P.Int -> P.String -> Ident -> P.String
importedLocal k kind (Ident x) = "i" <> show k <> "_" <> kind <> "_" <> mangle x

arityLocal :: P.Int -> P.String
arityLocal k = "i" <> show k <> "_arities"

-- | A name made an identifier: a letter, a digit, and `_` stand as they are, and
-- | every other character as `$` followed by its code point in hexadecimal and `$`,
-- | so two names never mangle to one.
mangle :: P.String -> P.String
mangle x = String.joinWith "" (map one (CodePoints.toCodePointArray x))
  where
  one cp =
    let
      n = fromEnum cp
    in
      if (n >= 0x30 && n <= 0x39) || (n >= 0x41 && n <= 0x5A) || (n >= 0x61 && n <= 0x7A) || n == 0x5F then CodePoints.singleton cp
      else "$" <> toStringAs hexadecimal n <> "$"

literal :: Literal -> S.Expr
literal = case _ of
  LitInt n -> S.Number (show n)
  LitNumber x -> S.Number (numberText x)
  LitString s -> S.String (textOf s)
  LitChar c -> S.Number (show c)
  LitBoolean b -> S.Boolean b

-- | A `Number` as JavaScript reads it back to the same value, the sign of a zero
-- | included.
numberText :: P.Number -> P.String
numberText x
  | x /= x = "NaN"
  | x == 1.0 / 0.0 = "Infinity"
  | x == -1.0 / 0.0 = "(-Infinity)"
  | x == 0.0 && 1.0 / x < 0.0 = "(-0)"
  | otherwise = show x

-- Names ----------------------------------------------------------------------------------

reg :: P.Int -> S.Expr
reg i = S.Index (S.Ident "r") (S.Number (show i))

mField :: P.String -> S.Expr
mField = S.Member (S.Ident "m")

rtMember :: P.String -> S.Expr
rtMember = S.Member (S.Ident "rt")

rtCall :: P.String -> P.Array S.Expr -> S.Expr
rtCall name = S.Call (rtMember name)

ctorName :: P.Int -> P.String
ctorName i = "c" <> show i

primName :: P.Int -> P.String
primName i = "p" <> show i

fnName :: P.Int -> P.String
fnName i = "fn" <> show i

globalName :: P.Int -> P.String
globalName i = "g" <> show i

segmentName :: SegmentId -> P.String
segmentName (SegmentId s) = "f" <> show s.func <> "_s" <> show s.index

qualifiedText :: Qualified Ident -> P.String
qualifiedText (Qualified (ModuleName m) (Ident x)) = m <> "." <> x

moduleText :: ModuleName -> P.String
moduleText (ModuleName m) = m
