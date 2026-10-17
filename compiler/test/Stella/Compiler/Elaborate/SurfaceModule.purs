-- | Data and value declarations written in source, resolved, elaborated
-- | against what their imports reach, and handed to the Core checker.
module Test.Stella.Compiler.Elaborate.SurfaceModule (spec) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), either)
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing, maybe)
import Data.Set as Set
import Data.String (joinWith)
import Data.String as String
import Data.Tuple (Tuple(..), snd)
import Effect.Aff (Aff)
import Fmt (fmt)
import Stella.Compiler.CST (parseModule, printSyntaxError)
import Stella.Compiler.CST.Types (inSource)
import Stella.Compiler.Surface.Decl (Observation(..))
import Stella.Compiler.Surface.Decl (Declaration(..)) as SurfaceDecl
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Row (rebuild, xnf)
import Stella.Compiler.Elaborate.CorePlus.Term (CoverageId(..), PendingCaseId(..), XDecisionTree(..), XExpr(..))
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar(..), XRowEntry(..), XType(..), fromCore)
import Stella.Compiler.Elaborate.Driver.Attempt (attemptPending, runAttempt)
import Stella.Compiler.Elaborate.Driver.Synthesis (attemptJob)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Environment.Imported (importedCatalog, importedSignature, sessionEnvOf)
import Stella.Compiler.Elaborate.Environment.Surface (importedSurface)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), closeBoundary, createSynthesis, equate, freshTypeMeta, initialState, openBoundary, placeFit)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindMetaBinding(..), MetaBinding(..), UnifyError(..), lookupMeta)
import Stella.Compiler.Elaborate.Surface.Types (readTypes)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitUse(..))
import Stella.Compiler.Elaborate.Surface.Module (ElaboratedValue, ElaborationError(..), cellRecords, elaborateModule, escapedCells, settleBodies)
import Stella.Compiler.Elaborate.Surface.Report (elaborationOrigins, printElaborationError, printType)
import Stella.Compiler.Elaborate.Surface.Type (Unsupported(..))
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Surface.Match (Tail(..), Witness(..))
import Stella.Compiler.Elaborate.Surface.Expr (tagsOf)
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeEntity(..), TypeSort(..), ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Scheme (plainScheme)
import Stella.Compiler.Resolve.Module (resolveModule)
import Stella.Compiler.Surface.Origin (rangeOf)
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore (Attribute, DataDecl, Decl(..), Declared, DecisionTree(..), Export(..), Expr(..), Module, OpClause(..), primSignature)
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), KindVar(..), ModuleName(..), OpName(..), Qualified(..), RegionName(..), Symbol(..), Tag(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (fn, intTy, pureFn, recordTy, stringTy, unitCtor, unitTy, variantTy)
import Stella.Compiler.TypedCore.Type (RowEntry(..), RowKey(..), Type(..))
import Stella.Compiler.TypedCore.Term (Literal(..), Occurrence(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

lib :: ModuleName
lib = ModuleName "Lib"

int :: Type
int = TCon intTy []

-- | `Lib`: `inc : Int -> Int`, `id : forall a. a -> a`, and
-- | `const : forall a b. a -> b -> a`; `data Tuple a b = Tuple a b` and
-- | `snd : forall a b. Tuple a b -> b`; and `foreign type Phantom` at
-- | `forall k. Type`; `attribute label (text :: String)`; and `effect Ping` with
-- | its operation `ping`, which the interface gives no argument.
libInterface :: ModuleInterface
libInterface =
  { name: lib
  , imports: []
  , exports: emptyExports
      { values = Map.fromFoldable (map (\n -> Tuple n { entity: Qualified lib (Ident n), via: Declared }) [ "inc", "id", "const", "snd", "Tuple", "ping" ])
      , types = Map.fromFoldable
          [ Tuple "Phantom" { entity: TypeEntity (Qualified lib (TyName "Phantom")), via: Declared, members: [] }
          , Tuple "Tuple" { entity: TypeEntity (Qualified lib (TyName "Tuple")), via: Declared, members: [ Ident "Tuple" ] }
          , Tuple "Ping" { entity: EffectEntity (Qualified lib (EffName "Ping")), via: Declared, members: [ Ident "ping" ] }
          ]
      , attributes = Map.singleton "label" { entity: Qualified lib (Ident "label"), via: Declared }
      }
  , declarations: emptyDeclarations
      { values = Map.fromFoldable
          [ value "inc" (pureFn int int)
          , value "id" (TForall a KType (pureFn (TVar a) (TVar a)))
          , value "const" (TForall a KType (TForall b KType (pureFn (TVar a) (pureFn (TVar b) (TVar a)))))
          , value "snd" (TForall a KType (TForall b KType (pureFn (tuple (TVar a) (TVar b)) (TVar b))))
          , Tuple (Ident "Tuple") { sort: SortConstructor (Qualified lib (TyName "Tuple")), scheme: plainScheme (monoScheme (TForall a KType (TForall b KType (pureFn (TVar a) (pureFn (TVar b) (tuple (TVar a) (TVar b))))))), attributes: [] }
          , Tuple (Ident "ping") { sort: SortOperation (Qualified lib (EffName "Ping")), scheme: plainScheme (monoScheme (pureFn (TCon unitTy []) int)), attributes: [] }
          ]
      , types = Map.fromFoldable
          [ Tuple (TyName "Phantom") { kind: { kindVars: [ KindVar "k" ], body: KType }, sort: ForeignType, attributes: [] }
          , Tuple (TyName "Tuple")
              { kind: monoScheme (KFun KType (KFun KType KType))
              , sort: DataType { params: [ { name: a, kind: KType }, { name: b, kind: KType } ], constructors: [ { name: Ident "Tuple", fields: [ TVar a, TVar b ] } ], isNewtype: false }
              , attributes: []
              }
          ]
      , attributes = Map.singleton (Ident "label") { positional: [ TCon stringTy [] ], keyword: [] }
      , effects = Map.singleton (EffName "Ping") { params: [], operations: [ { name: Ident "ping", binders: [], arguments: [], resumesWith: int } ], attributes: [] }
      }
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }
  where
  a = TyVar "a"
  b = TyVar "b"
  value n ty = Tuple (Ident n) { sort: SortForeign MayObserve, scheme: plainScheme (monoScheme ty), attributes: [] }
  tuple x y = TApp (TApp (TCon (Qualified lib (TyName "Tuple")) []) x) y

-- | `Base.Continuation`, as its source compiles: `Continuation` and `continue`
-- | exported, and the constructor elaboration-only, declared under its internal
-- | identity and exported by name nowhere.
continuationInterface :: ModuleInterface
continuationInterface = continuationInterfaceHolding (fn (TVar (TyVar "a")) (TVar (TyVar "r")) (TVar (TyVar "b")))

-- | `Base.Continuation`, its constructor holding the one field given, over
-- | `a`, `b`, and `r`.
continuationInterfaceHolding :: Type -> ModuleInterface
continuationInterfaceHolding field = libInterface
  { name = continuationModule
  , exports = emptyExports
      { values = Map.singleton "continue" { entity: Qualified continuationModule (Ident "continue"), via: Declared }
      , types = Map.singleton "Continuation" { entity: TypeEntity continuationType, via: Declared, members: [] }
      }
  , declarations = emptyDeclarations
      { values = Map.fromFoldable
          [ Tuple (Ident "continue") { sort: SortValue, scheme: plainScheme (monoScheme (quantified (pureFn continuation (fn (TVar a) (TVar r) (TVar b))))), attributes: [] }
          , Tuple (Ident "$Continuation") { sort: SortConstructor continuationType, scheme: plainScheme (monoScheme (quantified (pureFn field continuation))), attributes: [] }
          ]
      , types = Map.singleton (TyName "Continuation")
          { kind: monoScheme (KFun KType (KFun KType (KFun (KRow RowEffect) KType)))
          , sort: DataType
              { params: [ { name: a, kind: KType }, { name: b, kind: KType }, { name: r, kind: KRow RowEffect } ]
              , constructors: [ { name: Ident "$Continuation", fields: [ field ] } ]
              , isNewtype: true
              }
          , attributes: []
          }
      }
  }
  where
  continuationModule = ModuleName "Base.Continuation"
  continuationType = Qualified continuationModule (TyName "Continuation")
  continuation = TApp (TApp (TApp (TCon continuationType []) (TVar a)) (TVar b)) (TVar r)
  quantified body = TForall a KType (TForall b KType (TForall r (KRow RowEffect) body))
  a = TyVar "a"
  b = TyVar "b"
  r = TyVar "r"

environment :: Either String BuildEnvironment
environment = environmentWith continuationInterface

-- | `Lib` and the `Base.Continuation` given.
environmentWith :: ModuleInterface -> Either String BuildEnvironment
environmentWith continuations = case addInterface libInterface initialEnvironment >>= addInterface continuations of
  Right env -> Right env
  Left err -> Left (show err)

type Ran =
  { values :: Array ElaboratedValue
  , errors :: Array ElaborationError
  , module :: Maybe { core :: Module Surface.Origin, declared :: Declared Surface.Origin }
  }

-- | The module `M`, importing `Lib`, declaring the lines given; elaborated.
elaborating :: Array String -> (Ran -> Aff Unit) -> Aff Unit
elaborating = elaboratingUnder "module M where"

-- | `elaborating`, the module's header the one given.
elaboratingUnder :: String -> Array String -> (Ran -> Aff Unit) -> Aff Unit
elaboratingUnder = elaboratingIn environment

-- | `elaboratingUnder`, the modules imported from the environment given.
elaboratingIn :: Either String BuildEnvironment -> String -> Array String -> (Ran -> Aff Unit) -> Aff Unit
elaboratingIn built header body k = case built of
  Left err -> fail err
  Right env -> case parseModule (joinWith "\n" ([ header, "import Lib" ] <> body)) of
    Left err -> fail (printSyntaxError err)
    Right cst -> do
      let resolved = resolveModule env cst
      -- the modules the header imports, as a build views them
      case resolved.errors, viewFor (Array.nub (map _.module resolved.module.imports)) env of
        [], Right view -> case importedSignature env view of
          Left err -> fail (show err)
          Right signature -> do
            let elaborated = elaborateModule signature (importedSurface env view) (importedCatalog env view) resolved.module resolved.exports
            k case elaborated.result of
              Left errors -> { values: elaborated.values, errors: NonEmptyArray.toArray errors, module: Nothing }
              Right made -> { values: elaborated.values, errors: [], module: Just { core: made.core, declared: made.declared } }
        errors, _ -> fail ("not resolved: " <> show errors)

-- | The Core module made, which the Core checker accepted.
checked :: Ran -> (Module Surface.Origin -> Aff Unit) -> Aff Unit
checked r k = case r.module of
  Just made -> k made.core
  Nothing -> fail ("no Core module: " <> show (map at r.errors))

-- | Each declaration of a Core module, as `rec` or `nonrec` and the names it
-- | binds.
shapes :: Module Surface.Origin -> Array String
shapes m = Array.mapMaybe
  ( case _ of
      DeclNonRec _ b -> Just ("nonrec " <> nameOf b.name)
      DeclRec _ bs -> Just ("rec " <> joinWith " " (map (nameOf <<< _.name) bs))
      _ -> Nothing
  )
  m.decls
  where
  nameOf (Ident n) = n

-- | Each data declaration of a Core module.
dataOf :: Module Surface.Origin -> Array DataDecl
dataOf m = Array.mapMaybe
  ( case _ of
      DeclData _ d -> Just d
      _ -> Nothing
  )
  m.decls

-- | A data declaration as its name, its kind variables and parameters with
-- | their kinds, and its constructors with their tags and fields.
dataShape :: DataDecl -> { name :: TyName, kindVars :: Array KindVar, params :: Array { name :: TyVar, kind :: Kind }, constructors :: Array { name :: Ident, tag :: Int, fields :: Array Type } }
dataShape d = { name: d.name, kindVars: d.kindVars, params: d.params, constructors: d.constructors }

-- | The attributes the bindings of a declaration carry.
attributesOf :: Decl Surface.Origin -> Array Attribute
attributesOf = case _ of
  DeclNonRec _ b -> b.attributes
  DeclRec _ bs -> Array.concatMap _.attributes bs
  _ -> []

-- | Where an error stands, as line and column of the source.
at :: ElaborationError -> String
at = case _ of
  Unsupported (OutsideSubset o what) -> located o <> " outside: " <> what
  Unsupported (ReportedAlready o) -> located o <> " reported"
  Unsupported (EffectAsType o _) -> located o <> " effect as type"
  Unsupported (KeyTwice o _) -> located o <> " key twice"
  Unsupported (SpreadTwice o _) -> located o <> " spread twice"
  Unsupported (AnonymousSpread o) -> located o <> " anonymous spread"
  Unsupported (UnheldConstraint o _) -> located o <> " unheld"
  Unsupported (SynonymUnsaturated o _ _) -> located o <> " unsaturated"
  Unsupported (SynonymCycle o _) -> located o <> " cycle"
  Unsupported (SynonymUnexpandable o _) -> located o <> " unexpandable"
  Unsupported (ForeignKindInvalid o _) -> located o <> " foreign kind"
  Unsupported (EffectKindVariable o) -> located o <> " effect kind variable"
  Unsupported (EffectKindUndetermined o) -> located o <> " effect kind undetermined"
  Unsupported (KindNotDecided o) -> located o <> " kind not decided"
  Unsupported (SynonymKindNotDecided o _) -> located o <> " synonym kind not decided"
  SignatureNeeded o _ -> located o <> " signature needed"
  ConstraintEscapes o _ -> located o <> " constraint escapes"
  SynthesisUndecided o -> located o <> " synthesis undecided"
  ConstraintUnwritten o -> located o <> " constraint unwritten"
  KindUndetermined o -> located o <> " kind undetermined"
  Rejected (EquationFailed (AtSource s) _) -> located s.origin <> " rejected"
  Rejected (SynthesisFailed { goal: { origin: AtSource s } }) -> located s.origin <> " synthesis failed"
  Rejected (ObligationRejected { obligation: AtSource s }) -> located s.origin <> " obligation rejected"
  Rejected (CellEscapes { reference: AtSource r, boundary: AtSource b, cell: Ident c }) -> located r.origin <> " " <> c <> " escapes " <> located b.origin
  Rejected _ -> "rejected"
  EquationUndecided _ -> "undecided"
  TypeUndetermined o -> located o <> " type undetermined"
  LeftUnchecked o _ -> located o <> " left unchecked"
  AttributeRejected o _ -> located o <> " attribute rejected"
  ForeignRefused o _ r -> located o <> " foreign refused " <> show r.position <> " " <> show r.refusal
  TypeHoleStands o name t -> located o <> " hole " <> name <> " " <> printType t
  ExpressionHoleStands o name t context -> located o <> " expression hole " <> name <> " " <> printType t <> " [" <> joinWith ", " (map (\x -> let Ident n = x.name in n <> " : " <> printType x.type) context) <> "]"
  NonExhaustiveMatch o _ -> located o <> " non-exhaustive"
  ValueFormNeeded o -> located o <> " value form needed"
  ReadWhileInitializing o through _ (Qualified _ (Ident read)) -> located o <> " reads " <> read <> " early" <> maybe "" (\p -> " through " <> located p) through
  LocalReadWhileInitializing o through (Ident reader) (Ident read) -> located o <> " " <> reader <> " reads local " <> read <> " early" <> maybe "" (\p -> " through " <> located p) through
  EffectRowAmbiguous _ os -> joinWith " " (map located os) <> " effect row ambiguous"
  CoreRefused _ -> "the Core checker refused it"
  InternalEntryMismatch _ -> "an internal entry mismatched"
  Broken _ -> "broken"
  AttemptPostponed -> "postponed"

-- | Where a source origin starts, as line and column.
located :: Surface.Origin -> String
located o = let r = rangeOf o in show r.start.line <> ":" <> show r.start.column

-- | An error as `at` gives it, a rejection's site by the whole of its range.
spanned :: ElaborationError -> String
spanned = case _ of
  Rejected (EquationFailed (AtSource s) _) -> spanOf s.origin <> " rejected"
  Rejected (ObligationRejected { obligation: AtSource s }) -> spanOf s.origin <> " obligation rejected"
  Rejected (RowNotContained (AtSource s) _) -> spanOf s.origin <> " row not contained"
  Rejected (ObligationBroken { obligation: AtSource s }) -> spanOf s.origin <> " obligation broken"
  e -> at e
  where
  spanOf o = let r = rangeOf o in fmt @"{startLine}:{startColumn}-{endLine}:{endColumn}" { startLine: r.start.line, startColumn: r.start.column, endLine: r.end.line, endColumn: r.end.column }

-- | The scheme of the value of `M` named, each row in its normal form, so that a
-- | row closed to nothing reads as none, however it was assembled.
normalSchemeOf :: String -> Array ElaboratedValue -> Maybe String
normalSchemeOf name values =
  map (\v -> printType (normalRows (fromCore v.scheme.body))) (Array.find (\x -> x.name == Qualified (ModuleName "M") (Ident name)) values)
  where
  normalRows t = case t of
    XApp f x -> XApp (normalRows f) (normalRows x)
    XForall a k body -> XForall a k (normalRows body)
    XConstrained c body -> XConstrained c (normalRows body)
    XRowExtend _ _ -> either (const t) rebuild (xnf t)
    XRowUnion _ _ -> either (const t) rebuild (xnf t)
    _ -> t

spec :: Spec Unit
spec = describe "Stella.Compiler.Elaborate.Surface.Module" do
  describe "a value declaration" do
    it "is checked against its signature, and the Core checker accepts what it becomes" do
      elaborating
        [ "f :: Int -> Int"
        , "f x = inc x"
        , "twice :: forall a. (a -> a) -> a -> a"
        , "twice g x = g (g x)"
        , "n :: Int"
        , "n = id 3"
        , "m :: Int"
        , "m = twice f (f n)"
        , "k :: Int -> Int"
        , "k = \\y -> (id :: Int -> Int) y"
        ]
        \r -> do
          map (\e -> at e) r.errors `shouldEqual` []
          map _.name r.values `shouldEqual` map (Qualified (ModuleName "M") <<< Ident) [ "f", "twice", "n", "m", "k" ]
          checked r \core -> shapes core `shouldEqual` [ "nonrec f", "nonrec twice", "nonrec n", "nonrec m", "nonrec k" ]

    it "may refer to a value the module declares after it, itself among them" do
      elaborating [ "a :: Int -> Int", "a x = b (a x)", "b :: Int -> Int", "b y = a y" ] \r -> do
        map at r.errors `shouldEqual` []
        map _.name r.values `shouldEqual` map (Qualified (ModuleName "M") <<< Ident) [ "a", "b" ]
        checked r \core -> shapes core `shouldEqual` [ "rec a b" ]

    it "applies a λ performing less than the row ambient, widened and keeping the row it writes" do
      elaborating
        [ "effect Ask where"
        , "  ask :: Unit ->* Int"
        , "effect Log where"
        , "  log :: Int ->* Unit"
        , "asked :: Unit -> Int / {| Ask |}"
        , "asked u = asked u"
        , "c :: Unit -> Int / {| Ask, Log |}"
        , "c u = (\\_ -> asked ()) u"
        ]
        \r -> do
          map at r.errors `shouldEqual` []
          let ask = TRowExtend (RowEffectEntry (Qualified (ModuleName "M") (EffName "Ask")) []) TRowEmpty
          case map _.body (Array.find (\v -> v.name == Qualified (ModuleName "M") (Ident "c")) r.values) of
            Just (Lam _ _ _ _ (App _ (OpenEff _ _ (Lam _ _ _ row _)) _)) | row == ask -> pure unit
            other -> fail ("not widened at its own row: " <> show (map (map (const unit)) other))
          checked r \core -> shapes core `shouldEqual` [ "rec asked", "nonrec c" ]

  describe "what is not elaborated" do
    it "is reported where it stands, and leaves the rest elaborated" do
      elaborating
        [ "k = 1"
        , "bad :: Int"
        , "bad = inc"
        , "lam :: Int"
        , "lam = Unit?"
        , "open :: Int"
        , "open = const 1 id"
        , "ok :: Int"
        , "ok = 1"
        ]
        \r -> do
          map at r.errors `shouldEqual`
            [ "5:7 rejected"
            , "7:7 outside: this form"
            , "9:8 type undetermined"
            , "9:16 type undetermined"
            ]
          map _.name r.values `shouldEqual` map (Qualified (ModuleName "M") <<< Ident) [ "k", "ok" ]

    it "reports a constructor whose kind arguments nothing decides, and leaves its declaration out" do
      elaborating [ "p :: Phantom -> Int", "p x = 1", "ok :: Int", "ok = 1" ] \r -> do
        map at r.errors `shouldEqual` [ "3:6 kind undetermined" ]
        map _.name r.values `shouldEqual` [ Qualified (ModuleName "M") (Ident "ok") ]

    it "reports an attribute declaration whose parameter's type holds a kind nothing decides, at each such type" do
      elaborating [ "attribute q Int Phantom (k :: Phantom)", "ok :: Int", "ok = 1" ] \r -> do
        map at r.errors `shouldEqual` [ "3:17 kind undetermined", "3:31 kind undetermined" ]
        map _.name r.values `shouldEqual` [ Qualified (ModuleName "M") (Ident "ok") ]

  describe "a data declaration" do
    let
      m = ModuleName "M"
      own n = TCon (Qualified m (TyName n))
      a = TyVar "a"

    it "is a Core data declaration, its constructors tagged in the order written, before the values using it" do
      elaborating [ "data List a = Nil | Cons a (List a)", "xs :: List Int", "xs = Cons 1 Nil" ] \r -> checked r \core -> do
        map dataShape (dataOf core) `shouldEqual`
          [ { name: TyName "List"
            , kindVars: []
            , params: [ { name: a, kind: KType } ]
            , constructors:
                [ { name: Ident "Nil", tag: 0, fields: [] }
                , { name: Ident "Cons", tag: 1, fields: [ TVar a, TApp (own "List" []) (TVar a) ] }
                ]
            }
          ]
        shapes core `shouldEqual` [ "nonrec xs" ]
        core.exports `shouldEqual` [ ExportType (TyName "List"), ExportCtor (Ident "Nil"), ExportCtor (Ident "Cons"), ExportValue (Ident "xs") ]

    it "is read with every other of the module, declarations referring to one another among them" do
      elaborating [ "data A = MkA B | NoA", "data B = MkB A" ] \r -> checked r \core ->
        map _.name (dataOf core) `shouldEqual` [ TyName "A", TyName "B" ]

    it "has the kinds of its parameters decided by its fields, where they decide them" do
      elaborating [ "data App f (a :: Type) = App (f a)" ] \r -> checked r \core ->
        map (map _.kind <<< _.params) (dataOf core) `shouldEqual` [ [ KFun KType KType, KType ] ]

    it "is generalized over the kinds its head leaves undecided, a kind variable in place of each" do
      elaborating [ "data App f a = App (f a)", "data Proxy a = Proxy" ] \r -> checked r \core ->
        map dataShape (dataOf core) `shouldEqual`
          [ { name: TyName "App", kindVars: [ KindVar "k" ], params: [ { name: TyVar "f", kind: KFun (KVar (KindVar "k")) KType }, { name: TyVar "a", kind: KVar (KindVar "k") } ], constructors: [ { name: Ident "App", tag: 0, fields: [ TApp (TVar (TyVar "f")) (TVar (TyVar "a")) ] } ] }
          , { name: TyName "Proxy", kindVars: [ KindVar "k" ], params: [ { name: TyVar "a", kind: KVar (KindVar "k") } ], constructors: [ { name: Ident "Proxy", tag: 0, fields: [] } ] }
          ]

    it "is instantiated afresh by a later group, at as many kinds as it is used at" do
      elaborating [ "data App f a = App (f a)", "data Proxy a = Proxy", "data L (a :: Type) = L", "data Uses = Uses (App L Int) (App Proxy L)" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> map _.name (dataOf core) `shouldEqual` [ TyName "App", TyName "Proxy", TyName "L", TyName "Uses" ]

    it "gives a reference inside its group the kinds its member is generalized over" do
      elaborating [ "data T f = T (U f)", "data U f = U (T f)" ] \r -> checked r \core ->
        map dataShape (dataOf core) `shouldEqual`
          [ { name: TyName "T", kindVars: [ KindVar "k" ], params: [ { name: TyVar "f", kind: KVar (KindVar "k") } ], constructors: [ { name: Ident "T", tag: 0, fields: [ TApp (TCon (Qualified (ModuleName "M") (TyName "U")) [ KVar (KindVar "k") ]) (TVar (TyVar "f")) ] } ] }
          , { name: TyName "U", kindVars: [ KindVar "k" ], params: [ { name: TyVar "f", kind: KVar (KindVar "k") } ], constructors: [ { name: Ident "U", tag: 0, fields: [ TApp (TCon (Qualified (ModuleName "M") (TyName "T")) [ KVar (KindVar "k") ]) (TVar (TyVar "f")) ] } ] }
          ]

    it "is used inside its group at the kind it writes afresh at each use, and at the one kind it is being given otherwise" do
      elaborating [ "data L (a :: Type) = L", "data Poly (a :: k) = Poly (Poly Int) (Poly L)" ] \r ->
        map at r.errors `shouldEqual` []
      elaborating [ "data L (a :: Type) = L", "data Mono a = Mono (Mono Int) (Mono L)" ] \r ->
        map at r.errors `shouldEqual` [ "4:32 rejected" ]

    it "is read with a synonym it refers to through, one group, a cycle of synonyms alone refused" do
      elaborating [ "data L (a :: Type) = L", "type S = L D", "data D = D S" ] \r ->
        map at r.errors `shouldEqual` []
      elaborating [ "data D = D S", "type S = T", "type T = S" ] \r ->
        map at r.errors `shouldEqual` [ "3:12 unexpandable", "4:6 cycle", "5:6 cycle" ]

    it "is generalized with a synonym of its group, a reference to it in the synonym given its kind arguments, both instantiated afresh by a later group" do
      elaborating [ "type S a = D a", "data D a = D (S a)", "data L (a :: Type) = L", "data Use = Use (D Int) (S L)" ] \r -> checked r \core ->
        map dataShape (dataOf core) `shouldEqual`
          [ { name: TyName "D", kindVars: [ KindVar "k" ], params: [ { name: a, kind: KVar (KindVar "k") } ], constructors: [ { name: Ident "D", tag: 0, fields: [ TApp (own "D" [ KVar (KindVar "k") ]) (TVar a) ] } ] }
          , { name: TyName "L", kindVars: [], params: [ { name: a, kind: KType } ], constructors: [ { name: Ident "L", tag: 0, fields: [] } ] }
          , { name: TyName "Use", kindVars: [], params: [], constructors: [ { name: Ident "Use", tag: 0, fields: [ TApp (own "D" [ KType ]) int, TApp (own "D" [ KFun KType KType ]) (own "L" []) ] } ] }
          ]

    it "is used inside its group through a synonym at the kind the synonym writes afresh at each use, and at the one kind it is being given otherwise" do
      elaborating [ "data P a = P", "type S a = D", "data D = D (S P)" ] \r ->
        map at r.errors `shouldEqual` []
      elaborating [ "data L (a :: Type) = L", "data K (a :: k) b = K b", "type S (a :: k) = K a D", "data D = D (S Int) (S L)" ] \r ->
        map at r.errors `shouldEqual` []
      elaborating [ "data L (a :: Type) = L", "data K (a :: k) b = K b", "type S a = K a D", "data D = D (S Int) (S L)" ] \r ->
        map at r.errors `shouldEqual` [ "6:23 rejected" ]

    it "reports a kind a synonym of its group leaves in its fields, which no generalization of its head reaches, where the constructor stands" do
      elaborating [ "data P a = P", "type S a = (D, P a)", "data D = D (S P)" ] \r ->
        map at r.errors `shouldEqual` [ "5:10 kind not decided" ]

    it "reports a kind that must produce `Type`, which no kind variable is, where the constructor holding it stands" do

      elaborating [ "data P a = P", "data H f a = H (P (f a))" ] \r ->
        map at r.errors `shouldEqual` [ "4:14 kind not decided" ]

    it "retires from `Ψ` the kinds it generalizes and those it reports a synonym for, none left unsolved for a later part to decide" do
      case environment, parseModule (joinWith "\n" [ "module M where", "import Lib", "data App f a = App (f a)", "data T f = T (U f)", "data U f = U (T f)", "data P a = P", "type I a = a", "type S = P P", "type F f a = f a" ]) of
        Right env, Right cst -> case viewFor [ lib ] env of
          Right view -> case importedSignature env view of
            Right signature -> do
              let
                resolved = resolveModule env cst
                declarations =
                  { order: Array.mapMaybe
                      ( case _ of
                          SurfaceDecl.DeclData d -> Just d.name
                          SurfaceDecl.DeclSynonym d -> Just d.name
                          _ -> Nothing
                      )
                      resolved.module.declarations
                  , data: Array.mapMaybe
                      ( case _ of
                          SurfaceDecl.DeclData d -> Just { origin: d.origin, attributes: d.attributes, name: d.name, kind: d.kind, params: d.params, constructors: d.constructors, isNewtype: false }
                          _ -> Nothing
                      )
                      resolved.module.declarations
                  , synonyms: Array.mapMaybe
                      ( case _ of
                          SurfaceDecl.DeclSynonym d -> Just d
                          _ -> Nothing
                      )
                      resolved.module.declarations
                  , foreignTypes: []
                  , effects: []
                  }
              case readTypes (sessionEnvOf signature (importedCatalog env view)) (importedSurface env view).synonyms declarations (initialState (SessionId 0) 1000) of
                Tuple (Done _) s ->
                  Array.filter
                    ( case _ of
                        KindUnsolved info -> info.level >= 1
                        KindAssigned _ -> false
                    )
                    (Array.fromFoldable (Map.values s.tentative.metas.kindBindings))
                    `shouldEqual` []
                Tuple (Failed d) _ -> fail ("not read: " <> show d)
                Tuple (Broke d) _ -> fail ("broken: " <> show d)
                Tuple _ _ -> fail "postponed"
            Left err -> fail (show err)
          Left err -> fail (show err)
        _, _ -> fail "no module"

    it "reports a kind only its fields hold, which no generalization of its head reaches" do

      elaborating [ "data Q = Q Phantom" ] \r ->
        map at r.errors `shouldEqual` [ "3:10 kind not decided" ]

    it "has the kind variables it writes, each use of the type instantiating them afresh" do
      elaborating [ "data Proxy (a :: k) = Proxy", "data IntProxy = IntProxy (Proxy Int)", "data Both = Both (Proxy Int) (Proxy List)", "data List (a :: Type) = Nil" ] \r -> checked r \core ->
        map dataShape (dataOf core) `shouldEqual`
          [ { name: TyName "Proxy", kindVars: [ KindVar "k" ], params: [ { name: a, kind: KVar (KindVar "k") } ], constructors: [ { name: Ident "Proxy", tag: 0, fields: [] } ] }
          , { name: TyName "IntProxy", kindVars: [], params: [], constructors: [ { name: Ident "IntProxy", tag: 0, fields: [ TApp (own "Proxy" [ KType ]) int ] } ] }
          , { name: TyName "Both", kindVars: [], params: [], constructors: [ { name: Ident "Both", tag: 0, fields: [ TApp (own "Proxy" [ KType ]) int, TApp (own "Proxy" [ KFun KType KType ]) (own "List" []) ] } ] }
          , { name: TyName "List", kindVars: [], params: [ { name: a, kind: KType } ], constructors: [ { name: Ident "Nil", tag: 0, fields: [] } ] }
          ]

    it "binds a kind variable written only in a field, as one written on a parameter is" do
      elaborating [ "data Poly = Poly (forall (f :: k -> Type) (a :: k). f a -> f a)" ] \r -> checked r \core -> do
        let
          k = KindVar "k"
          f = TyVar "f"
        map dataShape (dataOf core) `shouldEqual`
          [ { name: TyName "Poly"
            , kindVars: [ k ]
            , params: []
            , constructors:
                [ { name: Ident "Poly", tag: 0, fields: [ TForall f (KFun (KVar k) KType) (TForall a (KVar k) (pureFn (TApp (TVar f) (TVar a)) (TApp (TVar f) (TVar a)))) ] } ]
            }
          ]

    it "rejects a field at a kind other than Type where it stands" do
      elaborating [ "data Bad = Bad (Int Int)" ] \r -> map at r.errors `shouldEqual` [ "3:17 rejected" ]

  describe "a type synonym's kind" do
    let
      m = ModuleName "M"
      own n = TCon (Qualified m (TyName n))

    it "is generalized, and instantiated afresh by a later group, a signature, and an operation, at as many kinds as it is used at" do
      elaborating [ "type I a = a", "data L (a :: Type) = L", "data P a = P", "data U = U (P (I L)) (I Int)", "effect E where", "  op :: I Int ->* I Int", "f :: P (I L) -> I Int", "f p = 1" ] \r -> checked r \core ->
        map (map _.fields <<< _.constructors) (Array.filter (\d -> d.name == TyName "U") (dataOf core)) `shouldEqual` [ [ [ TApp (own "P" [ KFun KType KType ]) (own "L" []), int ] ] ]

    it "is reported where the synonym is declared where it holds a kind only its body holds, or one that must produce `Type`, and a use of the synonym as one that cannot be expanded" do
      elaborating [ "data P a = P", "type S = P P", "data U = U S" ] \r ->
        map at r.errors `shouldEqual` [ "5:12 unexpandable", "4:6 synonym kind not decided" ]
      elaborating [ "data L (a :: Type) = L", "type App f a = f a", "data U = U (App L Int)" ] \r ->
        map at r.errors `shouldEqual` [ "5:13 unexpandable", "4:6 synonym kind not decided" ]
      elaborating [ "data L (a :: Type) = L", "type App (f :: k -> Type) a = f a", "data U = U (App L Int)" ] \r ->
        map at r.errors `shouldEqual` []

  describe "a wildcard and a typed hole in an annotation" do
    it "stand for what elaboration decides, a wildcard at the kind where it stands" do
      elaborating
        [ "effect Console where"
        , "  log :: Int ->* Unit"
        , "f :: Int -> Int"
        , "f x = (inc :: _ -> Int) x"
        , "g :: (Unit -> Int / {| Console |}) -> Unit -> Int / {| Console |}"
        , "g k u = (k :: Unit -> Int / _) u"
        , "p :: Tuple Int Int -> Tuple Int Int"
        , "p t = (t :: _ Int Int)"
        ]
        \r -> do
          map at r.errors `shouldEqual` []
          checked r \core -> shapes core `shouldEqual` [ "nonrec f", "nonrec g", "nonrec p" ]

    it "report a hole with what it stands for, one of a name once and `?_` each time, the body no value" do
      elaborating [ "h :: Int -> Int", "h x = (inc :: ?a -> ?a) x", "u :: Int -> Int", "u x = (inc :: ?_ -> ?_) x", "ok :: Int", "ok = 1" ] \r -> do
        map at r.errors `shouldEqual`
          [ "4:15 hole a Int", "6:15 hole _ Int", "6:21 hole _ Int" ]
        map _.name r.values `shouldEqual` [ Qualified (ModuleName "M") (Ident "ok") ]

    it "report a hole nothing decides, and a wildcard nothing decides where it is written, once" do
      -- nothing a hole or a wildcard stands for is reported again where the term
      -- holds it
      elaborating [ "h :: Int", "h = const 1 (id :: ?a -> ?a)" ] \r ->
        map at r.errors `shouldEqual` [ "4:20 hole a ?" ]
      elaborating [ "w :: Int", "w = const 1 (id :: _ -> _)" ] \r ->
        map at r.errors `shouldEqual` [ "4:20 type undetermined", "4:25 type undetermined" ]
      -- what is undecided inside a type decided in part is undecided as well
      elaborating [ "w :: Int", "w = const 1 (id :: _)" ] \r ->
        map at r.errors `shouldEqual` [ "4:20 type undetermined" ]
      elaborating [ "h :: Int", "h = const 1 (id :: ?f)" ] \r ->
        map at r.errors `shouldEqual` [ "4:20 hole f ? -> ?" ]

    it "share a hole's name within one annotation alone" do
      elaborating [ "h :: Int -> Int", "h x = (inc :: ?a -> ?a) ((inc :: ?a -> ?a) x)" ] \r ->
        map at r.errors `shouldEqual` [ "4:15 hole a Int", "4:34 hole a Int" ]

  describe "an expression hole" do
    it "is reported with the type it stands at and the locals in scope, the body no value" do
      elaborating [ "f :: Int -> Int", "f x = inc ?todo", "ok :: Int", "ok = 1" ] \r -> do
        map at r.errors `shouldEqual` [ "4:11 expression hole todo Int [x : Int]" ]
        map printElaborationError r.errors `shouldEqual` [ "The expression hole `?todo` stands for `Int`\nIn scope:\n  x : Int" ]
        map _.name r.values `shouldEqual` [ Qualified (ModuleName "M") (Ident "ok") ]

    it "stands at a type nothing decides, reported once" do
      elaborating [ "g :: Int", "g = const 1 ?any" ] \r -> do
        map at r.errors `shouldEqual` [ "4:13 expression hole any ? []" ]
        map printElaborationError r.errors `shouldEqual` [ "The expression hole `?any` stands for `?`" ]

    it "is a value form, so that a value without a signature holding one is reported by the hole alone" do
      elaborating [ "x = ?todo" ] \r ->
        map at r.errors `shouldEqual` [ "3:5 expression hole todo ? []" ]
      elaborating [ "q :: forall a. a", "q = ?h" ] \r ->
        map at r.errors `shouldEqual` [ "4:5 expression hole h a []" ]
      -- reported before anything is generalized, `x` at what nothing decided
      elaborating [ "g x = inc ?h" ] \r ->
        map at r.errors `shouldEqual` [ "3:11 expression hole h Int [x : ?]" ]

    it "stands at the type expected where it is checked, a quantifier there not opened" do
      elaborating [ "k :: (forall a. a -> a) -> Int", "k f = 1", "m :: Int", "m = k ?h" ] \r ->
        map at r.errors `shouldEqual` [ "6:7 expression hole h forall a. a -> a []" ]

    it "is one of its own each time, a name shared by two being a label of each" do
      elaborating [ "h :: Tuple Int String", "h = Tuple ?x ?x" ] \r ->
        map at r.errors `shouldEqual` [ "4:11 expression hole x Int []", "4:14 expression hole x String []" ]

    it "shows the locals source can name, by name, at their types where it stands" do
      elaborating [ "p :: forall a. a -> Int -> a", "p y n = let", "      _ = inc n", "      b = inc n", "      a = 1", "    in (\\z -> ?here) a" ] \r ->
        map at r.errors `shouldEqual` [ "8:15 expression hole here a [a : Int, b : Int, n : Int, y : a, z : Int]" ]

    it "keeps what only a local in scope leaves undecided reported where the local's term holds it" do
      elaborating [ "u :: Int", "u = let w = \\y -> y in ?h" ] \r ->
        map at r.errors `shouldEqual` [ "4:24 expression hole h Int [w : ? -> ?]", "4:9 type undetermined", "4:14 type undetermined" ]

  describe "a `case`" do
    let
      schemeOf name values = map (\v -> printType (fromCore v.scheme.body)) (Array.find (\x -> x.name == inM name) values)
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
      types = [ "data Color = Red | Green | Blue", "data Opt a = None | Some a" ]
    it "is checked against the type expected, and the Core checker accepts what it becomes" do
      elaborating (types <> [ "fromOpt :: forall a. a -> Opt a -> a", "fromOpt d o = case o of", "  None -> d", "  Some x -> x" ]) \r -> do
        map at r.errors `shouldEqual` []
        map _.name r.values `shouldEqual` [ inM "fromOpt" ]
        checked r \core -> shapes core `shouldEqual` [ "nonrec fromOpt" ]

    it "is inferred where nothing gives its type" do
      elaborating (types <> [ "isRed c = case c of", "  Red -> true", "  _ -> false", "swap p = case p of", "  Tuple a b -> Tuple b a" ]) \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> schemeOf name r.values) [ "isRed", "swap" ] `shouldEqual` map Just [ "Color -> Boolean", "forall a. forall b. Tuple a b -> Tuple b a" ]
        checked r \core -> shapes core `shouldEqual` [ "nonrec isRed", "nonrec swap" ]

    it "matches several values, an or-pattern, a nested pattern, and a `Boolean` its alternatives exhaust" do
      elaborating
        ( types <>
            [ "level :: Color -> Opt Color -> Int"
            , "level c o = case c, o of"
            , "  (Red | Blue), _ -> 1"
            , "  Green, Some Red -> 2"
            , "  Green, _ -> 3"
            , "flip :: Boolean -> Boolean"
            , "flip b = case b of"
            , "  true -> false"
            , "  false -> true"
            ]
        )
        \r -> do
          map at r.errors `shouldEqual` []
          checked r \core -> shapes core `shouldEqual` [ "nonrec level", "nonrec flip" ]

    it "makes an alternative several leaves take a join point, its parameters the variables its patterns bind" do
      elaborating (types <> [ "f :: Color -> Opt Int -> Int", "f c o = case c, o of", "  Red, Some 0 -> 0", "  _, Some n -> n", "  _, None -> 9" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Lam _ _ _ _ (LetJoin _ _ [ { name: Ident "n" } ] _ (Var _ (Ident "n")) (Case _ _ _)))) -> pure unit
          other -> fail ("no join point: " <> show other)

    it "puts an alternative one leaf takes in that leaf, and keeps one no leaf takes once, as a join point nothing jumps to" do
      elaborating (types <> [ "fromInt :: Int -> Opt Int -> Int", "fromInt d o = case o of", "  None -> d", "  Some x -> x", "k :: Opt Int -> Int", "k o = case o of", "  _ -> 0", "  Some x -> x" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "fromInt" r.values of
          Just (Lam _ _ _ _ (Lam _ _ _ _ (Case _ _ (SwitchCtor _ [ { tree: Leaf (Var _ (Ident "d")) }, { tree: Bind (Ident "x") _ (Leaf (Var _ (Ident "x"))) } ] Nothing)))) -> pure unit
          other -> fail ("not in the leaves: " <> show other)
        case bodyOf "k" r.values of
          Just (Lam _ _ _ _ (LetJoin _ _ [ { name: Ident "x" } ] _ (Var _ (Ident "x")) (Case _ _ (Leaf (Lit _ (LitInt 0)))))) -> pure unit
          other -> fail ("not kept once: " <> show other)

    it "reports a pattern of another type than what it matches where the pattern stands" do
      elaborating (types <> [ "f :: Int -> Int", "f n = case n of", "  true -> 1", "  _ -> 0", "g :: Int -> Int", "g n = case n of", "  Some x -> x", "  _ -> 0" ]) \r ->
        map at r.errors `shouldEqual` [ "7:3 rejected", "11:3 rejected" ]

    it "that leaves a value unmatched is reported with one such value, the body no value" do
      elaborating (types <> [ "g :: Opt Int -> Int", "g o = case o of", "  Some x -> x", "ok :: Int", "ok = 1" ]) \r -> do
        map at r.errors `shouldEqual` [ "6:12 non-exhaustive" ]
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `None`" ]
        map _.name r.values `shouldEqual` [ inM "ok" ]
      elaborating (types <> [ "pick :: Color -> Boolean -> Int", "pick c b = case c, b of", "  Red, true -> 1", "  _, false -> 2" ]) \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `Green, true`" ]
      elaborating (types <> [ "deep :: Opt (Opt Int) -> Int", "deep o = case o of", "  None -> 0", "  Some None -> 1", "  Some (Some 0) -> 2" ]) \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `Some (Some _)`" ]

    it "that leaves a value unmatched is not reported where its body fails first" do
      elaborating (types <> [ "h :: Opt Int -> Int", "h o = case o of", "  Some x -> true" ]) \r ->
        map at r.errors `shouldEqual` [ "7:13 rejected" ]

    it "checks the body of an alternative no value reaches" do
      elaborating (types <> [ "k :: Opt Int -> Int", "k o = case o of", "  _ -> 0", "  Some x -> true" ]) \r ->
        map at r.errors `shouldEqual` [ "8:13 rejected" ]
      elaborating (types <> [ "k :: Opt Int -> Int", "k o = case o of", "  _ -> 0", "  Some x -> ?unreached" ]) \r ->
        map at r.errors `shouldEqual` [ "8:13 expression hole unreached Int [o : Opt Int, x : Int]" ]
      elaborating (types <> [ "k :: Opt Int -> Int", "k o = case o of", "  _ -> 0", "  Some x -> x" ]) \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec k" ]

    it "performs what its scrutinees and its bodies perform, in the row ambient where it stands" do
      elaborating
        ( types <>
            [ "effect Ask where"
            , "  ask :: Unit ->* Int"
            , "asked :: Unit -> Int / {| Ask |}"
            , "asked u = asked u"
            , "inBody :: Opt Int -> Int / {| Ask |}"
            , "inBody o = case o of"
            , "  None -> asked ()"
            , "  Some x -> x"
            , "inScrutinee :: Unit -> Int / {| Ask |}"
            , "inScrutinee u = case asked u of"
            , "  0 -> 1"
            , "  n -> n"
            ]
        )
        \r -> do
          map at r.errors `shouldEqual` []
          map _.name r.values `shouldEqual` map inM [ "asked", "inBody", "inScrutinee" ]
      -- a row its signature does not write reaches the boundary of its
      -- definition, as any application's does
      elaborating (types <> [ "effect Ask where", "  ask :: Unit ->* Int", "asked :: Unit -> Int / {| Ask |}", "asked u = asked u", "quiet :: Opt Int -> Int", "quiet o = case o of", "  None -> asked ()", "  Some x -> x" ]) \r ->
        map at r.errors `shouldEqual` [ "10:7 outside: implicit-handler resolution at this checking boundary", "8:1 left unchecked" ]

    it "under a λ reads nothing while a recursive group is initialized, and its scrutinee is read where it stands" do
      elaborating
        [ "data Stored = Stored (Int -> Int)"
        , "keep :: Stored -> Int -> Int"
        , "keep s n = n"
        , "stored :: Stored"
        , "stored = Stored (\\n -> case n of"
        , "  0 -> keep stored n"
        , "  _ -> n)"
        ]
        \r -> map at r.errors `shouldEqual` []
      elaborating (types <> [ "x :: Opt Int", "x = case x of", "  _ -> None" ]) \r ->
        map at r.errors `shouldEqual` [ "6:10 reads x early" ]

  describe "a guard block" do
    let
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
      -- `isZero` and `types` take lines 3 to 8, so a declaration after them
      -- starts at line 9
      prelude = [ "data Color = Red | Green | Blue", "data Opt a = None | Some a", "isZero :: Int -> Boolean", "isZero n = case n of", "  0 -> true", "  _ -> false" ]
    it "binds a name over the lines after it and tries its guards in order, and the Core checker accepts what it becomes" do
      elaborating (prelude <> [ "classify :: Int -> Int", "classify n = case n of", "  m where", "      z = isZero m", "      z -> 0", "      otherwise -> m" ]) \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec isZero", "nonrec classify" ]

    it "binds a name at the type of what it is bound to" do
      elaborating (prelude <> [ "f :: Int -> Int", "f n = case n of", "  m where", "      k = m", "      k -> 0", "      otherwise -> m" ]) \r ->
        map at r.errors `shouldEqual` [ "13:7 rejected" ]

    it "falls through to the alternatives after it where every guard fails" do
      elaborating (prelude <> [ "pick :: Opt Int -> Int", "pick o = case o of", "  Some x where", "      isZero x -> 0", "  Some x -> x", "  None -> 1" ]) \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec isZero", "nonrec pick" ]

    it "binds its scrutinees once where a block may fall through, the main match and the fall-through point reading the same variables" do
      elaborating (prelude <> [ "wrap :: Int -> Opt Int", "wrap n = Some n", "pick :: Int -> Int", "pick n = case wrap n of", "  Some x where", "      isZero x -> 0", "  Some x -> x", "  None -> 1" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "pick" r.values of
          Just (Lam _ _ _ _ (Let _ s _ (App _ (Global _ _ _) (Var _ _)) (LetJoin _ _ [] _ _ (LetJoin _ _ [] _ (Case _ [ Var _ s' ] _) (Case _ [ Var _ s'' ] _)))))
            | s == s' && s == s'' -> pure unit
          other -> fail ("not bound once: " <> show other)

    it "of several alternatives falls through each to the next, every join point in scope where it is jumped to" do
      elaborating (prelude <> [ "isOne :: Int -> Boolean", "isOne n = case n of", "  1 -> true", "  _ -> false", "layered :: Opt Int -> Int", "layered o = case o of", "  Some x where", "      isZero x -> 0", "  Some x where", "      isOne x -> 1", "  _ -> 2" ]) \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec isZero", "nonrec isOne", "nonrec layered" ]

    it "that may fail covers nothing, and one ending in `otherwise` covers what its patterns match" do
      elaborating (prelude <> [ "pick :: Opt Int -> Int", "pick o = case o of", "  Some x where", "      isZero x -> 0", "  None -> 1" ]) \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `Some _`" ]
      elaborating (prelude <> [ "pick :: Opt Int -> Int", "pick o = case o of", "  Some x where", "      isZero x -> 0", "      otherwise -> x", "  None -> 1" ]) \r ->
        map at r.errors `shouldEqual` []
      elaborating (prelude <> [ "pick :: Opt Int -> Int", "pick o = case o of", "  Some x where", "      true -> x", "  None -> 1" ]) \r ->
        map at r.errors `shouldEqual` []

    it "of an alternative no leaf takes is kept, its fall-through point jumping to itself" do
      elaborating (prelude <> [ "k :: Opt Int -> Int", "k o = case o of", "  _ -> 0", "  Some x where", "      isZero x -> 1" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "k" r.values of
          Just (Lam _ _ _ _ (Let _ _ _ (Var _ _) (LetJoin _ fall [] _ (Jump _ fall' []) (LetJoin _ _ [ { name: Ident "x" } ] _ _ (Case _ [ Var _ _ ] (Leaf (Lit _ (LitInt 0)))))))) | fall == fall' -> pure unit
          other -> fail ("not kept: " <> show other)

    it "keeps the lines after a guard that always succeeds, checked, their fall-through point jumping to itself" do
      elaborating (prelude <> [ "t :: Int -> Int", "t n = case n of", "  m where", "      otherwise -> 0", "      isZero m -> 1" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "t" r.values of
          Just (Lam _ _ _ _ (Let _ _ _ (Var _ _) (LetJoin _ fall [] _ (Jump _ fall' []) (Case _ _ _)))) | fall == fall' -> pure unit
          other -> fail ("not kept: " <> show other)
      elaborating (prelude <> [ "t :: Int -> Int", "t n = case n of", "  m where", "      otherwise -> 0", "      isZero m -> true" ]) \r ->
        map at r.errors `shouldEqual` [ "13:19 rejected" ]
      elaborating (prelude <> [ "t :: Int -> Int", "t n = case n of", "  m where", "      otherwise -> 0", "      isZero m -> ?after" ]) \r ->
        map at r.errors `shouldEqual` [ "13:19 expression hole after Int [m : Int, n : Int]" ]

    it "performs what its guards and its bindings' right-hand sides perform, in the row ambient where the `case` stands" do
      let
        effects = [ "effect Ask where", "  ask :: Unit ->* Int", "asked :: Unit -> Int / {| Ask |}", "asked u = asked u", "asks :: Unit -> Boolean / {| Ask |}", "asks u = asks u" ]
      elaborating (prelude <> effects <> [ "g :: Int -> Int / {| Ask |}", "g n = case n of", "  m where", "      a = asked ()", "      asks () -> a", "      otherwise -> m" ]) \r ->
        map at r.errors `shouldEqual` []
      elaborating (prelude <> effects <> [ "h :: Int -> Int", "h n = case n of", "  m where", "      a = asked ()", "      otherwise -> m" ]) \r ->
        map at r.errors `shouldEqual` [ "16:3 outside: implicit-handler resolution at this checking boundary", "12:1 left unchecked", "14:1 left unchecked" ]
      elaborating (prelude <> effects <> [ "h :: Int -> Int", "h n = case n of", "  m where", "      asks () -> 1", "      otherwise -> m" ]) \r ->
        map at r.errors `shouldEqual` [ "16:3 outside: implicit-handler resolution at this checking boundary", "12:1 left unchecked", "14:1 left unchecked" ]

    it "binds a pattern over the lines after it, matching the value it is bound to" do
      elaborating (prelude <> [ "f :: Int -> Int", "f n = case n of", "  m where", "      _ = isZero m", "      Tuple a b = Tuple m 1", "      otherwise -> b" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Case _ _ (Bind _ _ (Leaf (Let _ _ _ _ (Case _ [ _ ] (SwitchCtor _ [ { tree: Bind (Ident "a") _ (Bind (Ident "b") _ (Leaf (Var _ (Ident "b")))) } ] Nothing))))))) -> pure unit
          other -> fail ("not matched: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec isZero", "nonrec f" ]
      elaborating (prelude <> [ "f :: Int -> Int", "f n = case n of", "  m where", "      Tuple a b = Tuple m true", "      otherwise -> b" ]) \r ->
        map at r.errors `shouldEqual` [ "13:20 rejected" ]

  describe "a pattern a parameter is written as" do
    let
      schemeOf name values = map (\v -> printType (fromCore v.scheme.body)) (Array.find (\x -> x.name == inM name) values)
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
    it "is matched inside the last λ, the patterns of several parameters as one row from the left, and the Core checker accepts it" do
      elaborating [ "pick :: Tuple Int Int -> Int -> Tuple Int Int -> Int", "pick (Tuple a _) n (Tuple _ d) = d" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "pick" r.values of
          Just (Lam _ p _ _ (Lam _ (Ident "n") _ _ (Lam _ q _ _ (Case _ [ Var _ p', Var _ q' ] _)))) | p == p' && q == q' && p /= q -> pure unit
          other -> fail ("not one row: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec pick" ]
      elaborating [ "first :: Tuple Int Int -> Int", "first = \\(Tuple a _) -> a" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec first" ]

    it "is matched inside the abstractions a quantifier after it opens" do
      elaborating [ "f :: Tuple Int Int -> (forall a. a -> a)", "f (Tuple x _) y = y" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ p _ _ (TyLam _ _ _ (Lam _ (Ident "y") _ _ (Case _ [ Var _ p' ] (SwitchCtor _ [ { tree: Bind (Ident "x") _ (Leaf (Var _ (Ident "y"))) } ] Nothing))))) | p == p' -> pure unit
          other -> fail ("not inside: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "is inferred where nothing gives its type, a `_` parameter among them" do
      elaborating [ "first (Tuple a _) = a", "second = \\(Tuple _ b) -> b", "always _ = 0" ] \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> schemeOf name r.values) [ "first", "second", "always" ] `shouldEqual` map Just [ "forall a. forall b. Tuple a b -> a", "forall a. forall b. Tuple a b -> b", "forall a. a -> Int" ]
        checked r \core -> shapes core `shouldEqual` [ "nonrec first", "nonrec second", "nonrec always" ]

    it "binds the parameters of a local function, with a signature or without" do
      elaborating [ "f :: Int -> Int", "f n = inc (g (Tuple n (h (Tuple n n))))", "  where", "    g (Tuple a _) = a", "    h :: Tuple Int Int -> Int", "    h (Tuple _ b) = b" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "may be a constructor of a newtype, `()`, an as-pattern, or an annotation" do
      elaborating
        [ "newtype Wrap = Wrap Int"
        , "unwrap (Wrap n) = n"
        , "unit () = 1"
        , "whole t@(Tuple a _) = t"
        , "annotated (n :: Int) = n"
        ]
        \r -> do
          map at r.errors `shouldEqual` []
          map (\name -> schemeOf name r.values) [ "unwrap", "unit", "whole", "annotated" ] `shouldEqual` map Just [ "Wrap -> Int", "Unit -> Int", "forall a. forall b. Tuple a b -> Tuple a b", "Int -> Int" ]
          checked r \core -> shapes core `shouldEqual` [ "nonrec unwrap", "nonrec unit", "nonrec whole", "nonrec annotated" ]

    it "of another type than its argument's is reported where it stands" do
      elaborating [ "f :: Int -> Int", "f (Tuple a _) = a" ] \r ->
        map at r.errors `shouldEqual` [ "4:4 rejected" ]

  describe "a pattern a `let` or a `where` binds" do
    let
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
    it "matches its right-hand side's value where the block stands, its variables at the types it gives them" do
      elaborating [ "f :: Int -> Int", "f n = let Tuple a b = Tuple n true in a" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Case _ [ App _ _ _ ] (SwitchCtor _ [ { tree: Bind (Ident "a") _ (Bind (Ident "b") _ (Leaf (Var _ (Ident "a")))) } ] Nothing))) -> pure unit
          other -> fail ("not matched: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]
      elaborating [ "f :: Int -> Int", "f n = let Tuple a b = Tuple n true in b" ] \r ->
        map at r.errors `shouldEqual` [ "4:39 rejected" ]

    it "is kept where it binds no variable, its right-hand side evaluated once where the block stands" do
      let effects = [ "effect Ask where", "  ask :: Unit ->* Int", "told :: Unit -> Unit / {| Ask |}", "told u = told u" ]
      elaborating (effects <> [ "f :: Unit -> Int / {| Ask |}", "f u = let () = told u in 1" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Case _ [ App _ (Global _ _ _) (Var _ (Ident "u")) ] (SwitchCtor _ [ { tree: Leaf (Lit _ (LitInt 1)) } ] Nothing))) -> pure unit
          other -> fail ("not kept: " <> show other)
      elaborating (effects <> [ "f :: Unit -> Int", "f u = let () = told u in 1" ]) \r ->
        map at r.errors `shouldEqual` [ "8:3 outside: implicit-handler resolution at this checking boundary", "6:1 left unchecked" ]

    it "is one node, every variable it binds depended on there" do
      elaborating [ "f :: Int -> Tuple Int Boolean", "f n = Tuple x y", "  where", "    x = a", "    y = b", "    Tuple a b = Tuple n true" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Case _ _ (SwitchCtor _ [ { tree: Bind (Ident "a") _ (Bind (Ident "b") _ (Leaf (Let _ (Ident "x") _ (Var _ (Ident "a")) (Let _ (Ident "y") _ (Var _ (Ident "b")) _)))) } ] Nothing))) -> pure unit
          other -> fail ("not one node: " <> show other)

    it "is bound by no recursive group, which is reported where the pattern stands" do
      elaborating [ "f :: Int -> Int", "f n = let Tuple a b = Tuple n a in b" ] \r ->
        map at r.errors `shouldEqual` [ "4:11 outside: a pattern a recursive group binds" ]
      elaborating [ "f :: Int -> Int", "f n = b", "  where", "    c = b", "    Tuple a b = Tuple n c" ] \r ->
        map at r.errors `shouldEqual` [ "7:5 outside: a pattern a recursive group binds" ]

  describe "`case _ of`" do
    let
      schemeOf name values = map (\v -> printType (fromCore v.scheme.body)) (Array.find (\x -> x.name == inM name) values)
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
      types = [ "data Color = Red | Green | Blue", "data Opt a = None | Some a" ]
    it "is a function of its anonymous scrutinees, checked against the type expected" do
      elaborating (types <> [ "isRed :: Color -> Boolean", "isRed = case _ of", "  Red -> true", "  _ -> false" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "isRed" r.values of
          Just (Lam _ x _ _ (Case _ [ Var _ x' ] _)) | x == x' -> pure unit
          other -> fail ("no λ: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec isRed" ]

    it "is inferred where nothing gives its type, its anonymous scrutinees parameters from the left" do
      elaborating (types <> [ "orElse d = case d, _ of", "  _, Some x -> x", "  e, None -> e" ]) \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "orElse" r.values `shouldEqual` Just "forall a. a -> Opt a -> a"

    it "names no variable of its own where it is reported" do
      elaborating (types <> [ "h :: Opt Int -> Int", "h = case _ of", "  Some x -> ?here", "  None -> 0" ]) \r ->
        map at r.errors `shouldEqual` [ "7:13 expression hole here Int [x : Int]" ]
      elaborating (types <> [ "h :: Opt Int -> Int", "h = case _ of", "  Some x -> x" ]) \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `None`" ]

  describe "a record" do
    let
      schemeOf name values = map (\v -> printType (fromCore v.scheme.body)) (Array.find (\x -> x.name == inM name) values)
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
      key = SymbolKey <<< Symbol
    it "extends the empty record by each field, the first written outermost, and the Core checker accepts it" do
      elaborating [ "r = { a: 1, b: true }", "pun :: Int -> { a :: Int }", "pun a = { a }" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "r" r.values `shouldEqual` Just "{ a :: Int, b :: Boolean }"
        case bodyOf "r" r.values of
          Just (RecordExtend _ a (Lit _ (LitInt 1)) (RecordExtend _ b (Lit _ (LitBoolean true)) (RecordEmpty _))) | a == key "a" && b == key "b" -> pure unit
          other -> fail ("not extended: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec r", "nonrec pun" ]

    it "holds a λ no type around it writes, the row that λ writes closed" do
      elaborating [ "f u = { ignored: \\(x :: Int) -> x, kept: u }.kept" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "f" r.values `shouldEqual` Just "forall a. a -> a"
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "selects, replaces, and extends a record whose row is open, the field required absent from the rest" do
      elaborating [ "getA r = r.a", "setA r = { a = 1, ...r }", "addB r = { b: true, ...r }", "copy r = { ...r }", "setAB r = { a = 1, b = true, ...r }" ] \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> schemeOf name r.values) [ "getA", "setA", "addB", "copy", "setAB" ] `shouldEqual` map Just
          [ "forall a. forall b. … => { a :: a, ...b } -> a"
          , "forall a. forall b. … => { a :: b, ...a } -> { a :: Int, ...a }"
          , "forall a. … => { ...a } -> { b :: Boolean, ...a }"
          , "forall a. { ...a } -> { ...a }"
          , "forall a. forall b. forall c. … => … => { a :: b, b :: c, ...a } -> { a :: Int, b :: Boolean, ...a }"
          ]
        checked r \core -> shapes core `shouldEqual` [ "nonrec getA", "nonrec setA", "nonrec addB", "nonrec copy", "nonrec setAB" ]
      elaborating [ "getX :: { x :: Int, ... } -> Int", "getX r = r.x", "bump :: { x :: Int, ... } -> { x :: Boolean, ... }", "bump r = { x = true, ...r }" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec getX", "nonrec bump" ]

    it "is reported where the label stands that it selects or replaces and does not have, or extends it by and has" do
      elaborating [ "f :: { a :: Int } -> Int", "f r = r.b" ] \r ->
        map spanned r.errors `shouldEqual` [ "4:9-4:10 rejected" ]
      elaborating [ "g :: { a :: Int } -> { a :: Int, b :: Int }", "g r = { b = 1, ...r }" ] \r ->
        map spanned r.errors `shouldEqual` [ "4:9-4:10 rejected" ]
      elaborating [ "g :: { a :: Int } -> { a :: Int, b :: Int }", "g r = { a = 2, b = 1, ...r }" ] \r ->
        map spanned r.errors `shouldEqual` [ "4:16-4:17 rejected" ]
      elaborating [ "h :: { a :: Int } -> { a :: Int }", "h r = { a: 1, ...r }" ] \r ->
        map spanned r.errors `shouldEqual` [ "4:9-4:10 obligation rejected" ]

    it "evaluates its fields from the left and the record spread last, binding each field's value first where it replaces one" do
      elaborating [ "f :: { b :: Int, d :: Int } -> { a :: Int, b :: Boolean, c :: Int, d :: Int }", "f r = { a: 1, b = true, c: 3, d = 4, ...r }" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just
            ( Lam _ (Ident "r") _ _
                ( Let _ va _ (Lit _ (LitInt 1))
                    ( Let _ vb _ (Lit _ (LitBoolean true))
                        ( Let _ vc _ (Lit _ (LitInt 3))
                            ( Let _ vd _ (Lit _ (LitInt 4))
                                ( RecordExtend _ a (Var _ va')
                                    ( RecordExtend _ c (Var _ vc')
                                        (RecordUpdate _ b (RecordUpdate _ d (Var _ (Ident "r")) (Var _ vd')) (Var _ vb'))
                                    )
                                )
                            )
                        )
                    )
                )
            )
            | [ va, vb, vc, vd ] == [ va', vb', vc', vd' ] && [ a, b, c, d ] == map key [ "a", "b", "c", "d" ] -> pure unit
          other -> fail ("not in order: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]
      elaborating [ "f :: { a :: Int } -> { a :: Int, b :: Int }", "f r = { b: 2, ...r }" ] \r ->
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (RecordExtend _ _ (Lit _ (LitInt 2)) (Var _ (Ident "r")))) -> pure unit
          other -> fail ("bound: " <> show other)

    it "performs what its fields and the record it spreads perform, in the row ambient where it stands" do
      let effects = [ "effect Ask where", "  ask :: Unit ->* Int", "asked :: Unit -> Int / {| Ask |}", "asked u = asked u" ]
      elaborating (effects <> [ "f :: Unit -> { a :: Int } / {| Ask |}", "f u = { a: asked u }" ]) \r ->
        map at r.errors `shouldEqual` []
      elaborating (effects <> [ "f :: Unit -> { a :: Int }", "f u = { a: asked u }" ]) \r ->
        map at r.errors `shouldEqual` [ "8:3 outside: implicit-handler resolution at this checking boundary", "6:1 left unchecked" ]

  describe "a tuple" do
    let
      schemeOf name values = map (\v -> printType (fromCore v.scheme.body)) (Array.find (\x -> x.name == inM name) values)
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
    it "is the record of its components at their positions, built from the left" do
      elaborating [ "t = (1, true)", "pair :: Int -> (Int, Boolean)", "pair n = (n, false)" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "t" r.values `shouldEqual` Just "(Int, Boolean)"
        case bodyOf "t" r.values of
          Just (RecordExtend _ (PositionKey 0) (Lit _ (LitInt 1)) (RecordExtend _ (PositionKey 1) (Lit _ (LitBoolean true)) (RecordEmpty _))) -> pure unit
          other -> fail ("not by position: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec t", "nonrec pair" ]

  describe "a record or a tuple pattern" do
    let
      schemeOf name values = map (\v -> printType (fromCore v.scheme.body)) (Array.find (\x -> x.name == inM name) values)
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
      types = [ "data Opt a = None | Some a" ]
      key = SymbolKey <<< Symbol
    it "is checked against a record of the keys it writes, closed or open, its rest the record without them, and the Core checker accepts it" do
      elaborating [ "fst (a, _) = a", "both { x, y } = x", "getX { x, ... } = x", "dropX { x, ...rest } = rest", "whole { ...r } = r", "none {} = 0" ] \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> schemeOf name r.values) [ "fst", "both", "getX", "dropX", "whole", "none" ] `shouldEqual` map Just
          [ "forall a. forall b. (a, b) -> a"
          , "forall a. forall b. { y :: a, x :: b } -> b"
          , "forall a. forall b. … => { x :: b, ...a } -> b"
          , "forall a. forall b. … => { x :: b, ...a } -> { ...a }"
          , "forall a. { ...a } -> { ...a }"
          , "{} -> Int"
          ]
        checked r \core -> shapes core `shouldEqual` [ "nonrec fst", "nonrec both", "nonrec getX", "nonrec dropX", "nonrec whole", "nonrec none" ]
      elaborating [ "getX :: { x :: Int, ... } -> Int", "getX { x, ... } = x", "swap :: (Int, Boolean) -> (Boolean, Int)", "swap (a, b) = (b, a)" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec getX", "nonrec swap" ]

    it "binds its fields at their occurrences, and its rest by a `let` around the leaf, the keys it writes restricted in the order written" do
      elaborating [ "dropYX :: { x :: Int, y :: Int, z :: Int } -> { z :: Int }", "dropYX { y, x, ...rest } = rest" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "dropYX" r.values of
          Just
            ( Lam _ p _ _
                ( Case _ [ Var _ p' ]
                    ( Bind whole (OccScrutinee 0)
                        ( Bind (Ident "y") (OccRecordField (OccScrutinee 0) y)
                            ( Bind (Ident "x") (OccRecordField (OccScrutinee 0) x)
                                (Leaf (Let _ (Ident "rest") _ (RecordRestrict _ x' (RecordRestrict _ y' (Var _ whole'))) (Var _ (Ident "rest"))))
                            )
                        )
                    )
                )
            )
            | p == p' && whole == whole' && [ y, x, y', x' ] == map key [ "y", "x", "y", "x" ] -> pure unit
          other -> fail ("not restricted: " <> show other)

    it "passes its rest to the join point of an alternative several leaves take, whose body stands once" do
      elaborating (types <> [ "f :: Boolean -> { x :: Opt Int, y :: Int } -> { y :: Int }", "f b r = case b, r of", "  true, { x: Some 0, ...rest } -> rest", "  _, { x, ...rest } -> rest" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Lam _ _ _ _ (LetJoin _ _ [ { name: Ident "x" }, { name: Ident "rest" } ] _ (Var _ (Ident "rest")) (Case _ _ _)))) -> pure unit
          other -> fail ("not joined: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "dispatches within a field, and a value it does not match is shown as a record or a tuple" do
      elaborating (types <> [ "f :: { x :: Opt Int, y :: Int } -> Int", "f r = case r of", "  { x: Some a, y } -> a" ]) \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `{ x: None, y: _ }`" ]
      elaborating (types <> [ "g :: { x :: Opt Int, ... } -> Int", "g r = case r of", "  { x: Some a, ... } -> a" ]) \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `{ x: None, ... }`" ]
      elaborating [ "h :: (Boolean, Int) -> Int", "h p = case p of", "  (true, n) -> n" ] \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `(false, _)`" ]

    it "is reported where a label stands that the record does not have, and where a closed pattern or a tuple stands that does not write every key" do
      elaborating [ "f :: { a :: Int } -> Int", "f { b, ... } = b" ] \r ->
        map spanned r.errors `shouldEqual` [ "4:5-4:6 rejected" ]
      elaborating [ "g :: { a :: Int, b :: Int } -> Int", "g { a } = a" ] \r ->
        map spanned r.errors `shouldEqual` [ "4:3-4:8 rejected" ]
      elaborating [ "h :: (Int, Int, Int) -> Int", "h (a, b) = a" ] \r ->
        map spanned r.errors `shouldEqual` [ "4:4-4:8 rejected" ]

    it "is written where a `λ`, a `let`, and a guard block bind" do
      elaborating [ "pick = \\{ x, ... } -> x", "first p = let (a, _) = p in a", "g :: { x :: Int } -> Int", "g r = case r of", "  q where", "      { x } = q", "      otherwise -> x" ] \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> schemeOf name r.values) [ "pick", "first" ] `shouldEqual` map Just [ "forall a. forall b. … => { x :: b, ...a } -> b", "forall a. forall b. (a, b) -> a" ]
        checked r \core -> shapes core `shouldEqual` [ "nonrec pick", "nonrec first", "nonrec g" ]

  describe "a tag" do
    let
      schemeOf name values = map (\v -> printType (fromCore v.scheme.body)) (Array.find (\x -> x.name == inM name) values)
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
      tagKey = TagKey <<< Tag
      -- whether a Core term holds a `weaken`
      weakens = maybe false exprWeakens
      treeOf = case _ of
        TyLam _ _ _ e -> treeOf e
        ConstraintLam _ _ e -> treeOf e
        Lam _ _ _ _ e -> treeOf e
        Case _ _ tree -> treeWeakens tree
        _ -> false
      treeWeakens = case _ of
        Leaf e -> exprWeakens e
        Bind _ _ t -> treeWeakens t
        SwitchKey _ branches fallback -> Array.any (treeWeakens <<< _.tree) branches || maybe false treeWeakens fallback
        _ -> false
      exprWeakens = case _ of
        Let _ _ _ (VariantWeaken _ _ _ _) _ -> true
        Let _ _ _ _ e -> exprWeakens e
        e -> treeOf e
    it "injects its payload, `()` where none is written, at a row the rest lacks it from, and the Core checker accepts it" do
      elaborating [ "data List a = Nil | Cons a (List a)", "mk x = 'Ok x", "none = 'None", "pair x = ('A, x)", "field = { a: 'A }", "listed :: List [ 'A :: Int, 'B :: Unit ]", "listed = Cons ('A 1) (Cons 'B Nil)" ] \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> schemeOf name r.values) [ "mk", "none" ] `shouldEqual` map Just
          [ "forall a. forall b. … => a -> [ 'Ok :: a, ...b ]"
          , "forall a. … => [ 'None :: Unit, ...a ]"
          ]
        case bodyOf "none" r.values of
          Just (TyLam _ _ _ (ConstraintLam _ _ (VariantInject _ k (TVar _) (Global _ u [])))) | k == tagKey "None" && u == unitCtor -> pure unit
          other -> fail ("not injected: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec mk", "nonrec none", "nonrec pair", "nonrec field", "nonrec listed" ]

    it "checks its payload against the type the variant expected gives the tag" do
      elaborating [ "c :: [ 'F :: forall a. a -> a ]", "c = 'F (\\x -> x)" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec c" ]

    it "is matched against the tags of a closed variant, no default where every tag is taken" do
      elaborating [ "f :: [ 'A :: Int, 'B :: Boolean ] -> Int", "f v = case v of", "  'A n -> n", "  'B _ -> 0" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Case _ _ (SwitchKey (OccScrutinee 0) [ { key: a }, { key: b } ] Nothing))) | [ a, b ] == map tagKey [ "A", "B" ] -> pure unit
          other -> fail ("not dispatched: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "needs a default where the variant's row is open by a variable a quantifier binds" do
      elaborating [ "g :: [ 'A :: Int, ... ] -> Int", "g v = case v of", "  'A n -> n" ] \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `_`" ]
      elaborating [ "g :: [ 'A :: Int, ... ] -> Int", "g v = case v of", "  'A n -> n", "  _ -> 0" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec g" ]

    it "is shown in a value a match leaves uncovered by its tag, its payload where it is no `()`" do
      elaborating [ "f :: [ 'A :: Int, 'B :: Unit ] -> Int", "f v = case v of", "  'A n -> n" ] \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `'B`" ]
      elaborating [ "f :: [ 'A :: Int, 'B :: Int ] -> Int", "f v = case v of", "  'A n -> n" ] \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `'B _`" ]

    it "binds the variant whole in a default, widened by the tags its dispatch took" do
      elaborating [ "h :: [ 'A :: Int, 'B :: Int, ... ] -> [ 'A :: Int, 'B :: Int, ... ]", "h v = case v of", "  'A n -> 'A (inc n)", "  other -> other" ] \r -> do
        map at r.errors `shouldEqual` []
        weakens (bodyOf "h" r.values) `shouldEqual` true
        checked r \core -> shapes core `shouldEqual` [ "nonrec h" ]
      elaborating [ "w :: ([ 'A :: Int, ...r ], [ 'A :: Boolean, ...s ]) -> ([ 'A :: Int, ...r ], [ 'A :: Boolean, ...s ])", "w p = case p of", "  ('A n, 'A _) -> ('A n, 'A true)", "  (x, y) -> (x, y)" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec w" ]

    it "leaves the row open where a default takes what it may hold besides, and closes it where none does" do
      elaborating [ "k v = case v of", "  'A n -> n", "  _ -> 0" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "k" r.values `shouldEqual` Just "forall a. … => [ 'A :: Int, ...a ] -> Int"
        checked r \core -> shapes core `shouldEqual` [ "nonrec k" ]
      elaborating [ "k v = case v of", "  'A n -> n", "  'B -> 0" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "k" r.values `shouldEqual` Just "[ 'A :: Int, 'B :: Unit ] -> Int"
        case bodyOf "k" r.values of
          Just (Lam _ _ _ _ (Case _ _ (SwitchKey _ [ _, _ ] Nothing))) -> pure unit
          other -> fail ("not closed: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec k" ]

    it "closes the row where the default's guard block may fall through, its alternative kept as a join point nothing jumps to" do
      elaborating [ "k v = case v of", "  'A n -> n", "  _ where", "      false -> 0" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "k" r.values `shouldEqual` Just "[ 'A :: Int ] -> Int"
        map (String.contains (String.Pattern "(LitInt 0)") <<< show) (bodyOf "k" r.values) `shouldEqual` Just true
        checked r \core -> shapes core `shouldEqual` [ "nonrec k" ]
      elaborating [ "k v = case v of", "  'A n -> n", "  _ where", "      false -> 0", "      otherwise -> 1" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "k" r.values `shouldEqual` Just "forall a. … => [ 'A :: Int, ...a ] -> Int"
        checked r \core -> shapes core `shouldEqual` [ "nonrec k" ]

    it "closes a row nothing else decides to the tags its `case` takes, and quantifies no row for it" do
      elaborating [ "f v = case v of", "  'A -> 1", "  'B -> 2" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "f" r.values `shouldEqual` Just "[ 'A :: Unit, 'B :: Unit ] -> Int"
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Case _ _ (SwitchKey _ [ _, _ ] Nothing))) -> pure unit
          other -> fail ("not closed: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "decides the same whichever is elaborated first, the `case` or what else the variant is given to" do
      let
        before h = [ h, "h _ = 0", "g x = let", "    n = case x of", "      'A -> 1", "      'B -> 2", "  in h x" ]
        after h = [ h, "h _ = 0", "g x = let", "    n = h x", "  in case x of", "    'A -> 1", "    'B -> 2" ]
        wider = "h :: [ 'A :: Unit, 'B :: Unit, 'C :: Unit ] -> Int"
        exact = "h :: [ 'A :: Unit, 'B :: Unit ] -> Int"
      elaborating (before wider) \r -> map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `'C`" ]
      elaborating (after wider) \r -> map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `'C`" ]
      elaborating (before exact) \r -> map at r.errors `shouldEqual` []
      elaborating (after exact) \r -> map at r.errors `shouldEqual` []

    it "closes the instantiation of an open function the variant is given to" do
      elaborating [ "h :: [ 'A :: Unit, 'B :: Unit, ...r ] -> Int", "h _ = 0", "g x = let", "    n = h x", "  in case x of", "    'A -> 1", "    'B -> 2" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "g" r.values `shouldEqual` Just "[ 'A :: Unit, 'B :: Unit ] -> Int"
        checked r \core -> shapes core `shouldEqual` [ "nonrec h", "nonrec g" ]

    it "shows a tag the row has come to hold that no alternative takes" do
      elaborating [ "same :: a -> a -> a", "same a _ = a", "g x = let", "    n = case x of", "      'A -> 1", "      'B -> 2", "  in same x 'C" ] \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `'C`" ]

    it "leaves open, and shows as `_`, a row a quantifier comes to open" do
      elaborating [ "g :: [ 'A :: Unit, ...r ] -> Int", "g v = let", "    k = \\w -> case w of", "      'A -> 1", "  in k v" ] \r ->
        map printElaborationError r.errors `shouldEqual` [ "This `case` does not match every value: it does not match `_`" ]

    it "closes a row for a `case` in a local binding, in a body with a signature, and in another `case`'s alternative" do
      elaborating [ "f x = let", "    g v = case v of", "      'A -> 1", "      'B -> 2", "  in g x" ] \r -> do
        map at r.errors `shouldEqual` []
        normalSchemeOf "f" r.values `shouldEqual` Just "[ 'A :: Unit, 'B :: Unit ] -> Int"
      elaborating [ "f :: Int", "f = let", "    g = \\v -> case v of", "      'A -> 1", "      'B -> 2", "  in g 'A" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]
      elaborating [ "f v w = case v of", "  'A -> case w of", "      'X -> 1", "      'Y -> 2", "  'B -> 3" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "f" r.values `shouldEqual` Just "[ 'A :: Unit, 'B :: Unit ] -> [ 'X :: Unit, 'Y :: Unit ] -> Int"
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "closes a row two `case`s share, the one with a default keeping it" do
      elaborating [ "f v = let", "    a = case v of", "      'A -> 1", "      'B -> 2", "  in case v of", "    'A -> a", "    _ -> 0" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "f" r.values `shouldEqual` Just "[ 'A :: Unit, 'B :: Unit ] -> Int"
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "is reported where its tag stands, in an expression and in a pattern" do
      elaborating [ "f :: [ 'A :: Int ]", "f = 'B 1" ] \r ->
        map spanned r.errors `shouldEqual` [ "4:5-4:7 rejected" ]
      elaborating [ "f :: [ 'A :: Int ] -> Int", "f v = case v of", "  'B n -> n" ] \r ->
        map spanned r.errors `shouldEqual` [ "5:3-5:5 rejected" ]

  describe "an operation" do
    let
      schemeOf name values = map (\v -> printType (fromCore v.scheme.body)) (Array.find (\x -> x.name == inM name) values)
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
      state = [ "effect State s where", "  get :: Unit ->* s", "  put :: s ->* Unit" ]
      logs = [ "effect Log where", "  writeAt :: Int -> String ->* Unit" ]
      pick = [ "effect Pick where", "  pick :: forall a. a -> a ->* a" ]
      stateKey = EffectKey (Qualified (ModuleName "M") (EffName "State"))

    it "is performed where it is given its argument, the effect's parameter read off the row ambient" do
      elaborating (state <> [ "f :: Unit -> Int / {| State Int |}", "f _ = get ()" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Perform _ key (OpName "get") [] (Global _ _ _))) | key == stateKey -> pure unit
          other -> fail ("not performed: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "binds several arguments from the right and passes them as the record of their positions" do
      elaborating (logs <> [ "w :: Unit -> Unit / {| Log |}", "w _ = writeAt 1 \"a\"" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "w" r.values of
          Just (Lam _ _ _ _ (Let _ second _ (Lit _ (LitString _)) (Let _ first _ (Lit _ (LitInt 1)) (Perform _ _ (OpName "writeAt") [] (RecordExtend _ (PositionKey 0) (Var _ first') (RecordExtend _ (PositionKey 1) (Var _ second') (RecordEmpty _)))))))
            | first == first' && second == second' -> pure unit
          other -> fail ("not bound from the right: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec w" ]

    it "asks of the row only the element it is performed on" do
      elaborating (state <> [ "f = \\_ -> get ()" ]) \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "f" r.values `shouldEqual` Just "forall a. forall b. a -> b / {| State b |}"

    it "referred to short of its arguments is the `λ`s performing it, the rest of the row its type brings kept where nothing closes it" do
      elaborating (state <> [ "g = get", "p u = let h = get in Tuple h h", "q u = let h = \\_ -> get () in Tuple h h" ]) \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> schemeOf name r.values) [ "g", "p", "q" ] `shouldEqual` map Just
          [ "forall a. Unit -> a / {| State a |}"
          , "forall a. forall b. forall c. … => a -> Tuple (Unit -> b / {| State b, ...c |}) (Unit -> b / {| State b, ...c |})"
          , "forall a. forall b. forall c. a -> Tuple (b -> c / {| State c |}) (b -> c / {| State c |})"
          ]
        case bodyOf "g" r.values of
          Just (TyLam _ _ _ (Lam _ x _ _ (Perform _ key (OpName "get") [] (Var _ x')))) | key == stateKey && x == x' -> pure unit
          other -> fail ("not the λ performing it: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec g", "nonrec p", "nonrec q" ]

    it "applied short of its arguments performs nothing" do
      elaborating (logs <> [ "w :: String -> Unit / {| Log |}", "w = writeAt 0" ]) \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec w" ]

    it "applied short of its arguments is an application, which only a value form generalizes past" do
      elaborating (pick <> [ "q = pick", "r = pick id" ]) \r -> do
        map at r.errors `shouldEqual` [ "6:1 signature needed" ]
        schemeOf "q" r.values `shouldEqual` Just "forall a. a -> a -> a / {| Pick |}"

    it "applies what it resumes with to the arguments past its own" do
      elaborating ([ "effect Ask where", "  ask :: Unit ->* (Int -> Int)", "f :: Unit -> Int / {| Ask |}", "f _ = ask () 1" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (App _ (OpenEff _ _ (Perform _ _ (OpName "ask") [] _)) (Lit _ (LitInt 1)))) -> pure unit
          other -> fail ("not applied: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "instantiates its own variables afresh where it is called" do
      elaborating ([ "effect Abort where", "  abort :: forall a. Unit ->* a", "f :: Unit -> Tuple Int String / {| Abort |}", "f _ = Tuple (abort ()) (abort ())" ]) \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "is performed on the instance a label names, its fit at its name alone" do
      elaborating (state <> [ "f :: Unit -> Int / {| cache :: State Int |}", "f _ = get@cache ()" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Perform _ (SymbolKey (Symbol "cache")) (OpName "get") [] (Global _ _ _))) -> pure unit
          other -> fail ("not performed on the instance: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]
      elaborating (state <> [ "loud = get@cache ()" ]) \r ->
        map spanned r.errors `shouldEqual` [ "6:8-6:11 row not contained" ]

    it "reports an argument not of the type it takes where the argument is written" do
      elaborating (logs <> [ "w :: Unit -> Unit / {| Log |}", "w _ = writeAt \"a\" \"b\"" ]) \r ->
        map spanned r.errors `shouldEqual` [ "6:15-6:18 rejected" ]

    it "performed on an element at other parameters than the row's is a mismatch where the boundary decides it" do
      elaborating (state <> [ "f :: Unit -> Unit / {| State Int |}", "f _ = put \"x\"" ]) \r ->
        map spanned r.errors `shouldEqual` [ "7:3-7:4 rejected" ]

    it "performed where the row does not hold its element is a mismatch of rows, outside the boundary, and needs a handler under one" do
      elaborating (state <> logs <> [ "f :: Unit -> Int / {| Log |}", "f _ = get ()", "loud = get ()" ]) \r ->
        map spanned r.errors `shouldEqual` [ "10:8-10:11 row not contained", "9:3 outside: implicit-handler resolution at this checking boundary" ]

  describe "a handling expression" do
    let
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
      effects =
        [ "effect Ask where"
        , "  ask :: Unit ->* Int"
        , "effect Choose where"
        , "  choose :: Unit ->* Boolean"
        , "effect State s where"
        , "  get :: Unit ->* s"
        , "  put :: s ->* Unit"
        , "effect Log where"
        , "  writeAt :: Int -> String ->* Unit"
        ]
      inEffect n = Qualified (ModuleName "M") (EffName n)

    it "handles a group's element in the computation, under the row ambient, a `fast` clause at what the operation resumes with" do
      elaborating (effects <> [ "f :: Unit -> Int", "f _ = handle ask () with", "  Ask | fast ask _ -> 1" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Handle _ (Perform _ (EffectKey e) _ _ _) h)) | e == inEffect "Ask" -> do
            h.element `shouldEqual` RowEffectEntry (inEffect "Ask") []
            case h.opClauses of
              [ FastClause _ ] -> pure unit
              other -> fail ("not a fast clause: " <> show other)
          other -> fail ("not handled: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "applies a `full` clause's continuation where it resumes, and returns what the return clause gives, or the computation's value" do
      elaborating
        ( effects <>
            [ "f :: Unit -> Int"
            , "f _ = handle (case choose () of"
            , "    true -> 1"
            , "    false -> 2) with"
            , "  Choose | choose _ -> resume true"
            , "    | return x -> x"
            , "g :: Unit -> Int"
            , "g _ = handle ask () with"
            , "  Ask | ask _ -> resume 1"
            ]
        )
        \r -> do
          map at r.errors `shouldEqual` []
          case bodyOf "g" r.values of
            Just (Lam _ _ _ _ (Handle _ _ { returnClause: { binder: x, body: Var _ x' }, opClauses: [ FullClause { contBinder: k, body: App _ (Var _ k') (Lit _ (LitInt 1)) } ] })) | x == x' && k.name == k' -> pure unit
            other -> fail ("not resumed: " <> show other)
          checked r \core -> shapes core `shouldEqual` [ "nonrec f", "nonrec g" ]

    it "installs its items from the top, the first outermost, a group as a `handle` and a handler applied to the thunk of what is left" do
      elaborating
        ( effects <>
            [ "runAsk :: forall e. (Unit -> Boolean / {| Ask, ...e |}) -> Boolean / {| ...e |}"
            , "runAsk k = handle k () with"
            , "  Ask | fast ask _ -> 1"
            , "f :: Unit -> Boolean"
            , "f _ = handle choose () with"
            , "  runAsk"
            , "  Choose | fast choose _ -> true"
            , "g :: Unit -> Boolean"
            , "g _ = handle choose () with"
            , "  Choose | fast choose _ -> true"
            , "  runAsk"
            ]
        )
        \r -> do
          map at r.errors `shouldEqual` []
          case bodyOf "f" r.values of
            Just (Lam _ _ _ _ (App _ _ (Lam _ _ _ _ (Handle _ (Perform _ _ _ _ _) _)))) -> pure unit
            other -> fail ("not the handler applied outside the group: " <> show other)
          case bodyOf "g" r.values of
            Just (Lam _ _ _ _ (Handle _ (App _ _ (Lam _ _ _ _ (Perform _ _ _ _ _))) _)) -> pure unit
            other -> fail ("not the group outside the handler applied: " <> show other)
          checked r \core -> shapes core `shouldEqual` [ "nonrec runAsk", "nonrec f", "nonrec g" ]

    it "gives Core its clauses in the order the effect declares the operations, each binding the patterns written for its arguments" do
      elaborating
        ( effects <>
            [ "f :: Unit -> Int"
            , "f _ = handle 0 with"
            , "  State fast | put _ -> ()"
            , "    | get _ -> 1"
            , "w :: Unit -> Unit"
            , "w _ = handle writeAt 1 \"a\" with"
            , "  Log | fast writeAt line text -> const () (Tuple line text)"
            ]
        )
        \r -> do
          map at r.errors `shouldEqual` []
          case bodyOf "f" r.values of
            Just (Lam _ _ _ _ (Handle _ _ { opClauses: [ FastClause { op: OpName "get" }, FastClause { op: OpName "put" } ] })) -> pure unit
            other -> fail ("not in the order declared: " <> show other)
          checked r \core -> shapes core `shouldEqual` [ "nonrec f", "nonrec w" ]

    it "resumes, in a group written inside a `full` clause, that group's own continuation" do
      elaborating
        ( effects <>
            [ "f :: Unit -> Int"
            , "f _ = handle ask () with"
            , "  Ask | ask _ -> handle (case choose () of"
            , "          true -> 1"
            , "          false -> 2) with"
            , "        Choose | choose _ -> resume false"
            ]
        )
        \r -> do
          map at r.errors `shouldEqual` []
          case bodyOf "f" r.values of
            Just (Lam _ _ _ _ (Handle _ _ { opClauses: [ FullClause outer ] })) -> case outer.body of
              Handle _ _ { opClauses: [ FullClause inner ] } -> case inner.body of
                App _ (Var _ k) _ | k == inner.contBinder.name && k /= outer.contBinder.name -> pure unit
                other -> fail ("not the inner continuation: " <> show other)
              other -> fail ("not handled inside: " <> show other)
            other -> fail ("not handled: " <> show other)
          checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "binds one pattern, at `Unit`, for an imported operation its interface gives no argument" do
      elaborating [ "f :: Unit -> Int", "f _ = handle ping () with", "  Ping | fast ping _ -> 1" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "is inferred where a type is expected, and the type expected equated with what it gives" do
      elaborating (effects <> [ "n :: Int", "n = handle ask () with", "  Ask | fast ask _ -> 1" ]) \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec n" ]

    it "reports a group whose element the row ambient holds already, where the group's head stands" do
      elaborating (effects <> [ "f :: Unit -> Int / {| Ask |}", "f _ = handle ask () with", "  Ask | fast ask _ -> 1" ]) \r ->
        map spanned r.errors `shouldEqual` [ "14:3-14:6 obligation broken" ]

    it "reports a clause body not of the type its form gives it" do
      elaborating (effects <> [ "f :: Unit -> Int", "f _ = handle ask () with", "  Ask | fast ask _ -> \"x\"", "g :: Unit -> Int", "g _ = handle ask () with", "  Ask | ask _ -> \"x\"" ]) \r ->
        map spanned r.errors `shouldEqual` [ "14:23-14:26 rejected", "17:18-17:21 rejected" ]

    it "reports a clause performing what the row ambient does not hold as asking for a handler, under a boundary" do
      elaborating (effects <> [ "f :: Unit -> Int", "f _ = handle ask () with", "  Ask | fast ask _ -> get ()" ]) \r ->
        map spanned r.errors `shouldEqual` [ "13:3 outside: implicit-handler resolution at this checking boundary" ]

    -- the instance of `Continuation` written at the row a checking boundary
    -- owns, and `continue` applied to it, its own instantiation row the same
    it "wraps a `reifiable full` clause's continuation in `Continuation`, bound apart from the argument the operation takes" do
      elaboratingUnder "module M where\nimport Base.Continuation as Continuation" (effects <> [ "f :: Unit -> Unit", "f _ = handle writeAt 1 \"a\" with", "  Log reifiable full | writeAt line text k -> Continuation.continue k ()" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Handle _ _ { opClauses: [ FullClause clause ] })) -> do
            clause.argBinder.ty `shouldEqual` TApp (TCon recordTy []) (TRowExtend (RowTypeEntry (PositionKey 0) (TCon intTy [])) (TRowExtend (RowTypeEntry (PositionKey 1) (TCon stringTy [])) TRowEmpty))
            clause.contBinder.ty `shouldEqual` pureFn (TCon unitTy []) (TCon unitTy [])
            case clause.body of
              Case _ [ Var _ p ] (Bind _ _ (Bind _ _ (Leaf (Let _ k ty (App _ (TyApp _ (TyApp _ (TyApp _ (Global _ wrapper _) _) _) _) (Var _ k0)) (App _ (App _ _ (Var _ k')) _)))))
                | p == clause.argBinder.name && k0 == clause.contBinder.name && k' == k -> do
                    wrapper `shouldEqual` Qualified (ModuleName "Base.Continuation") (Ident "$Continuation")
                    ty `shouldEqual` TApp (TApp (TApp (TCon (Qualified (ModuleName "Base.Continuation") (TyName "Continuation")) []) (TCon unitTy [])) (TCon unitTy [])) TRowEmpty
              other -> fail ("not wrapped apart from the argument: " <> show other)
          other -> fail ("not a full clause: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "fits the constructor, applied to the continuation, into the row ambient the clause leaves" do
      elaboratingUnder "module M where\nimport Base.Continuation as Continuation" (effects <> [ "f :: Unit -> Unit / {| Ask |}", "f _ = handle writeAt 1 \"a\" with", "  Log reifiable full | writeAt line text k -> Continuation.continue k ()" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Handle _ _ { opClauses: [ FullClause clause ] })) -> case clause.body of
            Case _ _ (Bind _ _ (Bind _ _ (Leaf (Let _ _ _ (App _ (OpenEff _ _ (TyApp _ (TyApp _ (TyApp _ (Global _ _ _) _) _) _)) (Var _ k0)) _))))
              | k0 == clause.contBinder.name -> pure unit
            other -> fail ("not fitted into the row ambient: " <> show other)
          other -> fail ("not a full clause: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "is refused, its module importing a `Base.Continuation` whose constructor is at another scheme, as the compiler's fault" do
      elaboratingIn (environmentWith (continuationInterfaceHolding (pureFn (TVar (TyVar "a")) (TVar (TyVar "b"))))) "module M where\nimport Base.Continuation as Continuation" [ "f :: Unit -> Int", "f _ = 1" ] \r ->
        case r.errors of
          [ InternalEntryMismatch name ] -> name `shouldEqual` Qualified (ModuleName "Base.Continuation") (Ident "$Continuation")
          errors -> fail ("not a mismatch: " <> show (map at errors))

    it "is outside this version where it is a handler declaration" do
      elaborating (effects <> [ "handler h :: Ask ~> () where", "  fast | ask _ -> 1" ]) \r ->
        map at r.errors `shouldEqual` [ "12:9 outside: this declaration" ]
  describe "a handling expression declaring cells" do
    let
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
      effects =
        [ "effect Ask where"
        , "  ask :: Unit ->* Int"
        , "effect Tick where"
        , "  tick :: Unit ->* Int"
        , "effect Peek where"
        , "  peek :: Unit ->* Int"
        ]

    it "opens one region around its items, its initial values before it in the order declared, which its clauses read and write" do
      elaborating (effects <> [ "f :: Unit -> Int", "f _ = handle tick () with", "  var n := 0", "  var m := 1", "  Tick fast | tick _ -> let v = n! in let _ = n := m! in v" ]) \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (Region _ region [ n, m ] [ Lit _ (LitInt 0), Lit _ (LitInt 1) ] (Handle _ _ { opClauses: [ FastClause clause ] }))) -> do
            map _.key [ n, m ] `shouldEqual` [ SymbolKey (Symbol "n"), SymbolKey (Symbol "m") ]
            case clause.body of
              Let _ _ _ (ReadCell _ r1 (SymbolKey (Symbol "n"))) (Let _ _ _ (WriteCell _ r2 (SymbolKey (Symbol "n")) (ReadCell _ r3 (SymbolKey (Symbol "m")))) _)
                | r1 == region && r2 == region && r3 == region -> pure unit
              other -> fail ("not read and written: " <> show other)
          other -> fail ("not one region: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "shares its cells between its groups, and lets a function a clause makes read one" do
      elaborating
        ( effects <>
            [ "f :: Unit -> Int"
            , "f _ = handle (let _ = tick () in peek ()) with"
            , "  var n := 0"
            , "  Tick fast | tick _ -> let _ = n := 1 in 0"
            , "  Peek fast | peek _ -> let g = \\_ -> n! in g ()"
            ]
        )
        \r -> do
          map at r.errors `shouldEqual` []
          checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "evaluates its initial values outside the region, at the row it stands at" do
      elaborating (effects <> [ "f :: Unit -> Int / {| Ask |}", "f _ = handle tick () with", "  var n := ask ()", "  Tick fast | tick _ -> n!" ]) \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "keeps the cells of a function applied as an item apart, and reaches an outer cell from a clause of an inner expression" do
      elaborating
        ( effects <>
            [ "runTick :: forall a e. (Unit -> a / {| Tick, ...e |}) -> a / {| ...e |}"
            , "runTick k = handle k () with"
            , "  var n := 0"
            , "  Tick fast | tick _ -> n!"
            , "apart :: Unit -> Int"
            , "apart _ = handle (let _ = tick () in peek ()) with"
            , "  var n := 5"
            , "  runTick"
            , "  Peek fast | peek _ -> n!"
            , "reached :: Unit -> Int"
            , "reached _ = handle ask () with"
            , "  var c := 1"
            , "  Ask fast | ask _ -> let outer = \\_ -> c! in handle ask () with"
            , "      var c := 0"
            , "      Ask fast | ask _ -> outer ()"
            ]
        )
        \r -> do
          map at r.errors `shouldEqual` []
          checked r \core -> shapes core `shouldEqual` [ "nonrec runTick", "nonrec apart", "nonrec reached" ]

    it "reports a cell carried beyond the expression declaring it at the first reference to it, and at the expression" do
      elaborating
        ( effects <>
            [ "f :: Unit -> Unit -> Int"
            , "f _ = handle ask () with"
            , "  var n := 0"
            , "  Ask | ask _ -> \\_ -> n!"
            , "    | return x -> \\_ -> x"
            , "g u = handle ask () with"
            , "  var n := 0"
            , "  Ask | ask _ -> \\_ -> n!"
            , "    | return x -> \\_ -> x"
            ]
        )
        \r -> map at r.errors `shouldEqual` [ "16:24 n escapes 14:14", "12:24 n escapes 10:14" ]

    it "reports, of nested expressions, the one owning the region that escapes" do
      elaborating
        ( effects <>
            [ "inner :: Unit -> Unit -> Int"
            , "inner _ = handle ask () with"
            , "  var c := 0"
            , "  Ask | ask _ -> handle ask () with"
            , "      var d := 1"
            , "      Ask | ask _ -> \\_ -> d!"
            , "        | return x -> \\_ -> x"
            , "    | return x -> \\_ -> x"
            , "outer :: Unit -> Unit -> Int"
            , "outer _ = handle ask () with"
            , "  var c := 0"
            , "  Ask | ask _ -> handle ask () with"
            , "      var d := 1"
            , "      Ask | ask _ -> \\_ -> c!"
            , "        | return x -> \\_ -> x"
            , "    | return x -> \\_ -> x"
            ]
        )
        \r -> map at r.errors `shouldEqual` [ "14:28 d escapes 12:25", "22:28 c escapes 18:18" ]

    it "reports the first reference to a cell of the region, in the order elaborated, whichever reaches beyond it" do
      elaborating
        ( effects <>
            [ "f :: Unit -> Unit -> Int"
            , "f _ = handle ask () with"
            , "  var n := 0"
            , "  var m := 1"
            , "  Ask | ask _ -> let _ = n := 2 in \\_ -> m!"
            , "    | return x -> \\_ -> x"
            ]
        )
        \r -> map at r.errors `shouldEqual` [ "13:26 n escapes 10:14" ]

    it "reports a region escaping as a cell's only where the declaration it fails in noted the region" do
      let
        line l = Surface.FromSource (inSource { line: l, column: 1 } { line: l, column: 2 })
        region = RegionName "r#0"
        failed name = Rejected (EquationFailed (AtSource { declaration: inM name, origin: line 9 }) (EscapingRegion (MetaVar 0) region))
        records = cellRecords
          [ { name: inM "f"
            , regions: [ { region, boundary: line 3 } ]
            , references: [ { region, cell: Ident "n", origin: line 5 }, { region, cell: Ident "m", origin: line 7 } ]
            }
          ]
      map at [ escapedCells records (failed "f"), escapedCells records (failed "g"), escapedCells (cellRecords []) (failed "f") ]
        `shouldEqual` [ "5:1 n escapes 3:1", "9:1 rejected", "9:1 rejected" ]

    it "reports a value written to a cell not of the cell's type where the value stands" do
      elaborating (effects <> [ "f :: Unit -> Int", "f _ = handle tick () with", "  var n := 0", "  Tick fast | tick _ -> let _ = n := \"x\" in 1" ]) \r ->
        map spanned r.errors `shouldEqual` [ "12:38-12:41 rejected" ]

  describe "what a quantifier encloses" do
    let
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == Qualified (ModuleName "M") (Ident name)) values)
      idOf = Qualified lib (Ident "id")
      tupleOf = Qualified lib (Ident "Tuple")
      -- `Λ a. λ x. id [a] x`, whatever the names
      expanded = case _ of
        Just (TyLam _ a _ (Lam _ x _ _ (App _ (TyApp _ (Global _ g _) (TVar a')) (Var _ x')))) -> g == idOf && a == a' && x == x'
        _ -> false
    it "is built as it is where it is a value form, and η-expanded once where it is a function and may move" do
      elaborating
        [ "data Poly = Poly (forall a. a -> a)"
        , "f :: forall a. a -> a"
        , "f = id"
        , "g :: Int -> (forall b. b -> b)"
        , "g x = id"
        , "t :: forall a. a -> Tuple Int a"
        , "t = Tuple 1"
        , "annotated :: forall a. a -> a"
        , "annotated = (id :: a -> a)"
        , "p :: Poly"
        , "p = Poly id"
        ]
        \r -> do
          map at r.errors `shouldEqual` []
          expanded (bodyOf "f" r.values) `shouldEqual` true
          expanded (bodyOf "annotated" r.values) `shouldEqual` true
          case bodyOf "g" r.values of
            Just (Lam _ _ _ _ inner) -> expanded (Just inner) `shouldEqual` true
            other -> fail ("not a λ: " <> show other)
          -- a constructor spine is a value form, and is left as it is: the
          -- expansion's fit is decided equal only once its boundary is, after
          -- the loop, and the λ is contracted then
          case bodyOf "t" r.values of
            Just (TyLam _ a _ (App _ (TyApp _ (TyApp _ (Global _ c _) _) (TVar a')) (Lit _ (LitInt 1)))) | c == tupleOf && a == a' -> pure unit
            other -> fail ("not the spine: " <> show other)
          -- a field's quantifier is opened where the argument stands
          case bodyOf "p" r.values of
            Just (App _ (Global _ _ _) argument) -> expanded (Just argument) `shouldEqual` true
            other -> fail ("not the constructor applied: " <> show other)
          checked r \core -> shapes core `shouldEqual` [ "nonrec f", "nonrec g", "nonrec t", "nonrec annotated", "nonrec p" ]

    it "rebuilds a wrapping fit against the row of the λ the expansion makes" do
      elaborating
        [ "effect Console where"
        , "  log :: Int ->* Unit"
        , "loudId :: forall a. a -> a / {| Console |}"
        , "loudId = id"
        ]
        \r -> do
          map at r.errors `shouldEqual` []
          case bodyOf "loudId" r.values of
            Just (TyLam _ _ _ (Lam _ _ _ _ (App _ (OpenEff _ _ (TyApp _ (Global _ g _) _)) _))) | g == idOf -> pure unit
            other -> fail ("not widened under the λ: " <> show other)
          checked r \core -> shapes core `shouldEqual` [ "nonrec loudId" ]
      -- what a `Λ` encloses is at `()` whatever the λ around it performs, so the
      -- spine is a value form there
      elaborating
        [ "effect Console where"
        , "  log :: Int ->* Unit"
        , "h :: Int -> (forall a. a -> Tuple Int a) / {| Console |}"
        , "h x = Tuple 1"
        ]
        \r -> do
          map at r.errors `shouldEqual` []
          case bodyOf "h" r.values of
            Just (Lam _ _ _ _ (TyLam _ _ _ (App _ (TyApp _ (TyApp _ (Global _ c _) _) _) (Lit _ (LitInt 1))))) | c == tupleOf -> pure unit
            other -> fail ("not the spine under the Λ: " <> show other)
          checked r \core -> shapes core `shouldEqual` [ "nonrec h" ]
      -- and a spine that is no function is built there as it is, a value form
      elaborating
        [ "effect Console where"
        , "  log :: Int ->* Unit"
        , "k :: Int -> (forall a. Tuple Int (a -> a)) / {| Console |}"
        , "k x = Tuple 1 (\\y -> y)"
        ]
        \r -> do
          map at r.errors `shouldEqual` []
          checked r \core -> shapes core `shouldEqual` [ "nonrec k" ]

    it "reaches the boundary of the λ it makes where the fit the form would need fails, and hides no mismatch of types" do
      -- `fit(Console, ())` would refuse `quiet = loudId` as it stands; under
      -- the expansion's λ it is the boundary's to decide
      elaborating
        [ "effect Console where"
        , "  log :: Int ->* Unit"
        , "loudId :: forall a. a -> a / {| Console |}"
        , "loudId = id"
        , "quiet :: forall a. a -> a"
        , "quiet = loudId"
        ]
        \r -> map at r.errors `shouldEqual` [ "8:9 outside: implicit-handler resolution at this checking boundary" ]
      elaborating [ "wrong :: forall a. a -> a", "wrong = inc" ] \r ->
        map at r.errors `shouldEqual` [ "4:9 rejected" ]

    it "stays expanded where the row the λ's boundary decides widens what it applies" do
      elaborating [ "spread :: forall e a. a -> Tuple Int a / {| ...e |}", "spread = Tuple 1" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "spread" r.values of
          Just (TyLam _ _ _ (TyLam _ _ _ (Lam _ _ _ _ (App _ (OpenEff _ _ _) _)))) -> pure unit
          other -> fail ("not widened under the λ: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec spread" ]

    it "is reported where it is no value form and is not expanded, a function's parameter asked for" do
      elaborating [ "bad :: forall a. a -> a", "bad = const id 1" ] \r ->
        map at r.errors `shouldEqual` [ "4:1 value form needed" ]
      elaborating [ "pair :: forall a. Tuple Int (a -> a)", "pair = Tuple (inc 1) id" ] \r ->
        map at r.errors `shouldEqual` [ "4:1 value form needed" ]

    it "keeps a reference made before any λ immediate once expanded, judged as it stands before the expansion" do
      elaborating [ "loop :: forall a. a -> a", "loop = loop" ] \r ->
        map at r.errors `shouldEqual` [ "4:8 reads loop early" ]
      elaborating [ "p :: forall a. a -> a", "p = q", "q :: forall a. a -> a", "q = p" ] \r ->
        map at r.errors `shouldEqual` [ "4:5 reads q early" ]
      elaborating [ "typed :: Int -> Int", "typed = (typed :: Int -> Int)" ] \r ->
        map at r.errors `shouldEqual` [ "4:10 reads typed early" ]

  describe "a value declaration without a signature" do
    let
      schemeOf name values = map (\v -> printType (fromCore v.scheme.body)) (Array.find (\x -> x.name == inM name) values)
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM name) values)
      shouting =
        [ "effect Console where"
        , "  log :: Int ->* Unit"
        , "shout :: Int -> Unit / {| Console |}"
        , "shout x = shout x"
        ]
    it "is generalized, the rows nothing needs closed, and the Core checker accepts it" do
      elaborating
        ( shouting <>
            [ "ident = \\x -> x"
            , "ap f x = f x"
            , "first x y = x"
            , "n = inc 1"
            , "say x = shout x"
            , "nothing = ()"
            ]
        )
        \r -> do
          map at r.errors `shouldEqual` []
          map (\name -> schemeOf name r.values) [ "ident", "ap", "first", "n", "say", "nothing" ] `shouldEqual` map Just
            [ "forall a. a -> a"
            , "forall a. forall b. forall c. (a -> c / {| ...b |}) -> a -> c / {| ...b |}"
            , "forall a. forall b. a -> b -> a"
            , "Int"
            , "Int -> Unit / {| Console |}"
            , "Unit"
            ]
          checked r \core -> shapes core `shouldEqual` [ "rec shout", "nonrec ident", "nonrec ap", "nonrec first", "nonrec n", "nonrec say", "nonrec nothing" ]

    it "is η-expanded where it is a function that may move and no value form, and left as it is where it is one" do
      elaborating [ "g = id", "t = Tuple 1" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "g" r.values `shouldEqual` Just "forall a. a -> a"
        case bodyOf "g" r.values of
          Just (TyLam _ a _ (Lam _ x _ _ (App _ (TyApp _ (Global _ _ _) (TVar a')) (Var _ x')))) | a == a' && x == x' -> pure unit
          other -> fail ("not expanded: " <> show other)
        schemeOf "t" r.values `shouldEqual` Just "forall a. a -> Tuple Int a"
        case bodyOf "t" r.values of
          Just (TyLam _ a _ (App _ (TyApp _ (TyApp _ (Global _ _ _) _) (TVar a')) (Lit _ (LitInt 1)))) | a == a' -> pure unit
          other -> fail ("not the spine: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec g", "nonrec t" ]

    it "asks for a signature where it is no value form and leaves its type undecided" do
      elaborating [ "w = id id", "v = id 1" ] \r -> do
        map at r.errors `shouldEqual` [ "3:1 signature needed" ]
        map _.name r.values `shouldEqual` [ inM "v" ]
        schemeOf "v" r.values `shouldEqual` Just "Int"

    it "reports a type its body alone holds where it stands, an annotation asked for" do
      elaborating [ "f x = const x id" ] \r ->
        map at r.errors `shouldEqual` [ "3:7 type undetermined", "3:15 type undetermined" ]

    it "reports its annotations' holes and the wildcards nothing decides before anything is generalized" do
      elaborating [ "h x = (x :: ?a)", "k x = (x :: _)", "ok x = (inc :: _ -> Int) x" ] \r -> do
        map at r.errors `shouldEqual` [ "3:13 hole a ?", "4:13 type undetermined" ]
        schemeOf "ok" r.values `shouldEqual` Just "Int -> Int"

    it "is in dependency order, whatever order it is written in, and is referred to from a body with a signature" do
      elaborating [ "a = b 1", "m :: Tuple Int String", "m = Tuple (b 1) (b \"s\")", "b x = x" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "a" r.values `shouldEqual` Just "Int"
        schemeOf "b" r.values `shouldEqual` Just "forall a. a -> a"
        checked r \core -> shapes core `shouldEqual` [ "nonrec b", "nonrec a", "nonrec m" ]

    it "forcing a computation whose row is not empty is a mismatch of rows, the right-hand side no boundary" do
      elaborating [ "effect Console where", "  log :: Int ->* Unit", "loud :: Int / {| Console |}", "loud = 1", "w = loud" ] \r ->
        map at r.errors `shouldEqual` [ "rejected" ]

    it "is generalized with the group of declarations it refers to, each member at a scheme of its own" do
      elaborating [ "loop x = loop x", "p x = q x", "q x = p x", "ok = 1" ] \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> schemeOf name r.values) [ "loop", "p", "q", "ok" ] `shouldEqual` map Just
          [ "forall a. forall b. a -> b"
          , "forall a. forall b. forall c. a -> c / b"
          , "forall a. forall b. forall c. a -> c / b"
          , "Int"
          ]
        checked r \core -> shapes core `shouldEqual` [ "rec loop", "rec p q", "nonrec ok" ]

    it "is used at two types by a body with a signature, its group generalized first" do
      elaborating [ "ev n = od n", "od n = ev n", "m :: Tuple Int String", "m = Tuple (ev 1) (od \"s\")" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "rec ev od", "nonrec m" ]

    it "decides the row its group shares once the cycle of its fits is one row" do
      elaborating (shouting <> [ "p x = const (shout x) (q x)", "q x = p x" ]) \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "p" r.values `shouldEqual` Just "Int -> Unit / {| Console |}"
        schemeOf "q" r.values `shouldEqual` Just "Int -> Unit / {| Console |}"

    it "raises what a member it refers to needs where the reference stands, through to Core" do
      elaborating (shouting <> [ "r k n = const (k (shout n)) (s k)", "s k n = r k n" ]) \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> schemeOf name r.values) [ "r", "s" ] `shouldEqual` map Just
          [ "forall a. forall b. … => (Unit -> b / {| ...a |}) -> Int -> b / {| Console, ...a |}"
          , "forall a. forall b. … => (Unit -> b / {| ...a |}) -> Int -> b / {| Console, ...a |}"
          ]
        -- `s` refers to `r` at its own variables, the constraint `r` needs given
        let
          refersConstrained = case _ of
            ConstraintApp _ (TyApp _ (TyApp _ (Global _ g _) _) _) -> g == inM "r"
            TyLam _ _ _ e -> refersConstrained e
            ConstraintLam _ _ e -> refersConstrained e
            Lam _ _ _ _ e -> refersConstrained e
            App _ f x -> refersConstrained f || refersConstrained x
            OpenEff _ _ e -> refersConstrained e
            _ -> false
        map refersConstrained (bodyOf "s" r.values) `shouldEqual` Just true
        checked r \core -> shapes core `shouldEqual` [ "rec shout", "rec r s" ]

    it "reports a member using another at a type its own does not reach, the other left unchecked" do
      elaborating [ "data List a = Nil | Cons a (List a)", "f x = const 0 (g Nil)", "g xs = f ()" ] \r ->
        map at r.errors `shouldEqual` [ "4:18 type undetermined", "5:1 left unchecked" ]

    it "reports what fails at the member it names, the others left unchecked, and leaves nothing to what follows" do
      elaborating [ "p x = q x", "q x = const (p x) (inc ())", "user = p", "ok = \\x -> x" ] \r -> do
        map at r.errors `shouldEqual` [ "4:24 rejected", "3:1 left unchecked", "5:1 left unchecked" ]
        schemeOf "ok" r.values `shouldEqual` Just "forall a. a -> a"
      elaborating [ "bad :: forall a. Int", "bad = 1", "p x = q bad", "q x = p x" ] \r ->
        map at r.errors `shouldEqual` [ "3:15 kind undetermined", "5:1 left unchecked", "6:1 left unchecked" ]

    it "reads, in a recursive group, only the members written before it, generalized or not" do
      elaborating [ "f = g", "g x = f x" ] \r ->
        map at r.errors `shouldEqual` [ "3:5 reads g early" ]
      elaborating [ "g x = f x", "f = g" ] \r ->
        map at r.errors `shouldEqual` []
      elaborating [ "data List a = Nil | Cons a (List a)", "xs = Cons 1 xs" ] \r ->
        map at r.errors `shouldEqual` [ "4:13 reads xs early" ]

    it "leaves a declaration referring to one with no scheme unchecked, and one referring to a body with a signature that failed checked" do
      elaborating
        [ "bad = id id"
        , "user = bad"
        , "signed :: Int"
        , "signed = inc bad"
        , "wrong :: Int"
        , "wrong = inc ()"
        , "fine = wrong"
        ]
        \r -> do
          map at r.errors `shouldEqual` [ "3:1 signature needed", "4:1 left unchecked", "6:1 left unchecked", "8:13 rejected" ]
          schemeOf "fine" r.values `shouldEqual` Just "Int"
      -- a signature that gave no scheme leaves what refers to the value unchecked
      elaborating [ "bad :: forall a. Int", "bad = 1", "user = bad", "signed :: Int", "signed = bad", "ok = user" ] \r -> do
        map at r.errors `shouldEqual` [ "3:15 kind undetermined", "5:1 left unchecked", "8:1 left unchecked", "7:1 left unchecked" ]
        map _.name r.values `shouldEqual` []

  describe "a partial signature" do
    let
      inM' = Qualified (ModuleName "M") <<< Ident
      schemeOf name values = map (\v -> printType (fromCore v.scheme.body)) (Array.find (\x -> x.name == inM' name) values)
      shouting =
        [ "effect Console where"
        , "  log :: Int ->* Unit"
        , "shout :: Int -> Unit / {| Console |}"
        , "shout x = shout x"
        ]
    it "has what it leaves unwritten decided by its body, and nothing generalized" do
      elaborating (shouting <> [ "f :: _ -> Int", "f x = inc x", "g :: forall a. a -> _", "g x = x", "h :: Int -> Int / _", "h x = x", "say :: Int -> _ / _", "say x = shout x" ]) \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> schemeOf name r.values) [ "f", "g", "h", "say" ] `shouldEqual` map Just
          [ "Int -> Int", "forall a. a -> a", "Int -> Int", "Int -> Unit / {| Console |}" ]
        checked r \core -> shapes core `shouldEqual` [ "rec shout", "nonrec f", "nonrec g", "nonrec h", "nonrec say" ]

    it "reports a wildcard its body does not decide where it is written, generalizing nothing, and every hole with what it stands for" do
      elaborating [ "k :: _ -> Int", "k x = 1", "p :: Int -> ?r", "p x = x", "q :: ?a -> ?a", "q x = inc x" ] \r -> do
        map at r.errors `shouldEqual` [ "3:6 type undetermined", "5:13 hole r Int", "7:6 hole a Int" ]
        map _.name r.values `shouldEqual` []

    it "reports a wildcard whose kind is another's it leaves unwritten once, where the wildcard is written" do
      elaborating [ "w :: forall f. f _ -> Int", "w x = 1" ] \r ->
        map at r.errors `shouldEqual` [ "3:18 type undetermined" ]

    it "asks for no signature where its body is no value form, a type the body alone holds ambiguous" do
      elaborating [ "nv :: _", "nv = const 1 (id id)" ] \r ->
        map at r.errors `shouldEqual` [ "4:6 type undetermined", "4:15 type undetermined", "4:18 type undetermined" ]

    it "is read by what refers to it once it is decided, wherever it is written" do
      elaborating [ "m :: Int", "m = f 1", "user = f 2", "f :: _ -> Int", "f x = inc x" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "user" r.values `shouldEqual` Just "Int"

    it "is referred to inside its group at its one type, and not where its signature is a scheme" do
      elaborating [ "count :: _ -> Int", "count x = count (inc x)", "a :: _ -> Int", "a x = b (inc x)", "b y = a y" ] \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> schemeOf name r.values) [ "count", "a", "b" ] `shouldEqual` map Just [ "Int -> Int", "Int -> Int", "Int -> Int" ]
      elaborating [ "poly :: forall a. a -> _", "poly x = poly x" ] \r ->
        map at r.errors `shouldEqual` [ "4:10 outside: a recursive reference to a value whose partial signature is a scheme" ]

    it "may be a computation's" do
      elaborating [ "c :: _ / {||}", "c = 1", "v :: Int", "v = c" ] \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "c" r.values `shouldEqual` Just "Unit -> Int"

    it "keeps the conditions it writes, and gains none it does not" do
      let
        applying =
          [ "effect Console where"
          , "  log :: Int ->* Unit"
          , "apply :: forall s. (Unit -> Unit / {| Console, ...s |}) -> Unit"
          , "apply k = ()"
          , "both :: forall s. (Unit -> Unit / {| ...s |}) -> (Unit -> Unit / {| Console, ...s |}) -> Unit"
          , "both k l = ()"
          ]
      elaborating (applying <> [ "kept :: forall r. (Unit -> Unit / {| Console, ...r |}) -> _", "kept k = apply k" ]) \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "kept" r.values `shouldEqual` Just "forall r. … => (Unit -> Unit / {| Console, ...r |}) -> Unit"
      elaborating (applying <> [ "short :: forall r. (Unit -> Unit / {| ...r |}) -> _", "short k = both k k" ]) \r -> do
        -- `Console ∉ r`, which `short`'s signature does not write, is refused
        -- where `both` asks for it
        map at r.errors `shouldEqual` [ "rejected" ]
        map _.name r.values `shouldEqual` [ inM' "apply", inM' "both" ]

    it "is outside this version where its spine takes a synthesized argument, and in a foreign's" do
      elaborating [ "data Dict a = Dict a", "make :: Int", "make = 1", "sd :: {{ d :: Dict Int by make }} -> _", "sd d = 1" ] \r ->
        map at r.errors `shouldEqual` [ "7:1 outside: a partial signature taking a synthesized argument" ]
      elaborating [ "foreign blob :: _ -> Int" ] \r ->
        map at r.errors `shouldEqual` [ "3:17 outside: a wildcard" ]

  describe "a local binding without a signature" do
    let
      inM' = Qualified (ModuleName "M") <<< Ident
      schemeOf name values = map (\v -> printType (fromCore v.scheme.body)) (Array.find (\x -> x.name == inM' name) values)
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM' name) values)
      shouting =
        [ "effect Console where"
        , "  log :: Int ->* Unit"
        , "shout :: Int -> Unit / {| Console |}"
        , "shout x = shout x"
        ]
    it "is monomorphic, so that using it at two types is a mismatch" do
      elaborating [ "f :: Int", "f = let i = \\x -> x in const (i 1) (i \"s\")" ] \r ->
        map at r.errors `shouldEqual` [ "4:39 rejected" ]

    it "is no occurrence of the row its function shares with the value applying it, which is closed" do
      elaborating [ "f b = let g y = 1 in g b", "m b = let g = \\y -> inc y in g b", "r b = let go y = go y in go b" ] \r -> do
        map at r.errors `shouldEqual` []
        map (\name -> normalSchemeOf name r.values) [ "f", "m", "r" ] `shouldEqual` map Just
          [ "forall a. a -> Int"
          , "Int -> Int"
          , "forall a. forall b. a -> b"
          ]
        checked r \core -> shapes core `shouldEqual` [ "nonrec f", "nonrec m", "nonrec r" ]

    it "is in scope in every right-hand side of its block and in its body, a recursive function a `letrec`, and a `where` a `let`" do
      elaborating [ "f :: Int -> Int", "f n = let go x = go x in go n", "g :: Int -> Int", "g n = h n", "  where", "  h x = inc x" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (Lam _ _ _ _ (LetRec _ [ _ ] (App _ (Var _ _) (Var _ _)))) -> pure unit
          other -> fail ("not a letrec: " <> show other)
        case bodyOf "g" r.values of
          Just (Lam _ _ _ _ (Let _ _ _ (Lam _ _ _ _ _) (App _ (Var _ _) (Var _ _)))) -> pure unit
          other -> fail ("not a let: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f", "nonrec g" ]

    it "stands in the order of what it refers to, what it depends on outside, and the rest as written" do
      elaborating [ "k :: Int", "k = let", "      a = inc b", "      b = 1", "      c = 2", "    in a" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "k" r.values of
          Just (Let _ b _ (Lit _ (LitInt 1)) (Let _ a _ (App _ _ (Var _ b')) (Let _ c _ (Lit _ (LitInt 2)) (Var _ a')))) | b == b' && a == a' && c /= a -> pure unit
          other -> fail ("not in order: " <> show other)

    it "keeps a `_` binding's right-hand side, evaluated where the block stands, and what it performs in the row there" do
      elaborating (shouting <> [ "loud x = let _ = shout 1 in x" ]) \r -> do
        map at r.errors `shouldEqual` []
        schemeOf "loud" r.values `shouldEqual` Just "forall a. a -> a / {| Console |}"
        case bodyOf "loud" r.values of
          Just (TyLam _ _ _ (Lam _ _ _ _ (Let _ _ _ (App _ _ (Lit _ (LitInt 1))) (Var _ _)))) -> pure unit
          other -> fail ("not kept: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "rec shout", "nonrec loud" ]

    it "is a recursive value that is no function where it reads its own group, and refers to one initialized before it as it likes" do
      elaborating [ "n :: Int", "n = let m = inc m in m" ] \r -> do
        map at r.errors `shouldEqual` [ "4:17 m reads local m early" ]
        map printElaborationError r.errors `shouldEqual` [ "`m` is read here while it is being initialized" ]
      -- a top-level member read inside a block it initializes is read by it
      elaborating [ "n :: Int", "n = let m = n in m" ] \r ->
        map at r.errors `shouldEqual` [ "4:13 reads n early" ]
      elaborating [ "p :: Int", "p = let", "      a = inc 1", "      go x = go a", "    in go 0" ] \r ->
        map at r.errors `shouldEqual` []

    it "is initialized in the order written, a member reading only those written before it" do
      elaborating [ "q :: Int", "q = let", "      a = Tuple b 0", "      b :: Tuple Int (Int -> Int)", "      b = Tuple 1 (\\n -> const (snd a) (inc n))", "    in snd a" ] \r -> do
        map at r.errors `shouldEqual` [ "5:17 a reads local b early" ]
        -- the right-hand side reading is not named: it may be a `_`
        map printElaborationError r.errors `shouldEqual` [ "`b` is read here while its recursive group is being initialized, before `b` is" ]
      elaborating [ "q :: Int", "q = let", "      b :: Tuple Int (Int -> Int)", "      b = Tuple 1 (\\n -> const (snd a) (inc n))", "      a = Tuple b 0", "    in snd a" ] \r -> checked r \core ->
        shapes core `shouldEqual` [ "nonrec q" ]

    it "reports a read an application makes immediate where the reference stands and where the application does" do
      elaborating [ "p :: Int", "p = let", "      a :: Tuple Int (Int -> Int)", "      a = Tuple 1 (\\n -> snd b n)", "      b :: Tuple Int (Int -> Int)", "      b = Tuple (snd a 0) (\\n -> n)", "    in snd b 0" ] \r ->
        map at r.errors `shouldEqual` [ "6:30 b reads local b early through 8:18" ]

    it "holds records of closures referring to one another, and a recursive function stored in data" do
      elaborating [ "f :: Int", "f = let", "      fibAnd :: Tuple Int (Int -> Int)", "      fibAnd = Tuple 0 (\\n -> snd fibAnd n)", "    in snd fibAnd 1" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (LetRec _ [ _ ] _) -> pure unit
          other -> fail ("not a letrec: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]
      elaborating [ "g :: Int", "g = let", "      a :: Tuple Int (Int -> Int)", "      a = Tuple 1 (\\n -> snd b n)", "      b :: Tuple Int (Int -> Int)", "      b = Tuple 2 (\\n -> snd a n)", "    in snd a 0" ] \r -> checked r \core ->
        shapes core `shouldEqual` [ "nonrec g" ]

    it "is judged as the source writes it, a signature's η-expansion making no read later" do
      elaborating [ "f :: Int", "f = let", "      go :: forall a. a -> a", "      go = go", "    in go 1" ] \r ->
        map at r.errors `shouldEqual` [ "6:12 go reads local go early" ]

    it "is a recursive group elaborated under the empty row, so that a member that is no function performs nothing" do
      elaborating (shouting <> [ "loud :: Int -> Unit / {| Console |}", "loud x = let u = const (shout x) u in u" ]) \r ->
        map (\e -> joinWith " " (map located (elaborationOrigins e)) <> " " <> printElaborationError e) r.errors
          `shouldEqual` [ "8:25 This performs `{| Console |}`, which is not among the effects allowed here" ]
      -- a function's body performs where it is applied
      elaborating (shouting <> [ "loud :: Int -> Unit / {| Console |}", "loud x = let go n = const (shout n) go in go x" ]) \r -> checked r \core ->
        shapes core `shouldEqual` [ "rec shout", "nonrec loud" ]

    it "is judged a group before those its right-hand sides hold, and those before the ones its body holds" do
      elaborating [ "k :: Int", "k = let", "      a = Tuple (let x = inc x in x) (inc (snd a))", "    in let y = inc y in y" ] \r ->
        map at r.errors `shouldEqual` [ "5:48 a reads local a early", "5:30 x reads local x early", "6:20 y reads local y early" ]

    it "is a function value where an annotation abstracts it over a type or a constraint, as Core's `letrec` admits" do
      elaborating [ "f :: Int", "f = let go = ((\\x -> const x go) :: forall a. a -> a) in 1" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "f" r.values of
          Just (LetRec _ [ { value: TyLam _ _ _ (Lam _ _ _ _ _) } ] _) -> pure unit
          other -> fail ("not a letrec of an abstraction: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]
      elaborating [ "effect Console where", "  log :: Int ->* Unit", "g :: Int", "g = let go = ((\\u -> const u go) :: forall r. Unit -> Unit / {| Console, ...r |}) in 1" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "g" r.values of
          Just (LetRec _ [ { value: TyLam _ _ _ (ConstraintLam _ _ (Lam _ _ _ _ _)) } ] _) -> pure unit
          other -> fail ("not a letrec of an abstraction: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec g" ]

    it "leaves a type only it holds ambiguous, no quantifier of the declaration around it" do
      elaborating [ "u x = let unused y = y in x" ] \r -> do
        map at r.errors `shouldEqual` [ "3:11 type undetermined", "3:18 type undetermined" ]
        map _.name r.values `shouldEqual` []
      elaborating [ "s :: Int", "s = let unused x = x in 1" ] \r ->
        map at r.errors `shouldEqual` [ "4:9 type undetermined", "4:16 type undetermined" ]

  describe "a local binding with a signature" do
    let
      inM' = Qualified (ModuleName "M") <<< Ident
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == inM' name) values)
    it "is checked against its signature, and instantiated where it is referred to, at two types among them" do
      elaborating [ "f :: Tuple Int String", "f = let", "      ident :: forall a. a -> a", "      ident x = x", "    in Tuple (ident 1) (ident \"s\")" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec f" ]

    it "reads the type variables of the signature around it as they are, quantifying only those it mentions beyond them" do
      elaborating [ "g :: forall a. a -> a", "g x = let", "      h :: a -> a", "      h y = y", "    in h x" ] \r -> do
        map at r.errors `shouldEqual` []
        checked r \core -> shapes core `shouldEqual` [ "nonrec g" ]
      elaborating [ "k :: Int", "k = let", "      j :: forall b. b -> Int", "      j y = y", "    in j 1" ] \r ->
        map at r.errors `shouldEqual` [ "6:13 rejected" ]

    it "instantiates a local at a scheme however it came to be one, a parameter's and an annotation's among them, whatever order the block is written in" do
      elaborating [ "apply :: (forall a. a -> a) -> Tuple Int String", "apply g = Tuple (g 1) (g \"s\")" ] \r ->
        map at r.errors `shouldEqual` []
      elaborating [ "p :: Tuple Int String", "p = let ident = ((\\x -> x) :: forall a. a -> a) in Tuple (ident 1) (ident \"s\")" ] \r ->
        map at r.errors `shouldEqual` []
      -- `g` is elaborated first, so `f = g` instantiates it, and `f`, without a
      -- signature, has one type: a mismatch, whichever order the block is
      -- written in
      elaborating [ "q :: Tuple Int String", "q = let", "      f = g", "      g = ((\\x -> x) :: forall a. a -> a)", "    in Tuple (f 1) (f \"s\")" ] \r ->
        map at r.errors `shouldEqual` [ "7:23 rejected" ]
      elaborating [ "r :: Int", "r = let", "      f = g 1", "      g = ((\\x -> x) :: forall a. a -> a)", "    in f" ] \r ->
        map at r.errors `shouldEqual` []

    it "is a function value under the abstractions its signature makes, recursive among them" do
      elaborating [ "c :: Int", "c = let", "      go :: forall a. a -> a", "      go x = go x", "    in go 1" ] \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "c" r.values of
          Just (LetRec _ [ { value: TyLam _ _ _ (Lam _ _ _ _ _) } ] _) -> pure unit
          other -> fail ("not a letrec of an abstraction: " <> show other)

    it "may be partial, what it holds undecided reported once its declaration is settled" do
      elaborating [ "w :: Int", "w = let", "      p :: _ -> Int", "      p y = inc y", "    in p 1" ] \r ->
        map at r.errors `shouldEqual` []
      elaborating [ "h :: Int", "h = let", "      p :: ?t -> Int", "      p y = inc y", "    in p 1" ] \r ->
        map at r.errors `shouldEqual` [ "5:12 hole t Int" ]
      elaborating [ "u :: Int", "u = let", "      q :: forall f. Int", "      q = 1", "    in q" ] \r ->
        map at r.errors `shouldEqual` [ "5:19 kind undetermined", "7:8 type undetermined" ]

    it "is evaluated where its block stands, under the ambient row there, where it is no function" do
      let effects = [ "effect Console where", "  log :: Int ->* Unit", "shout :: Int -> Unit / {| Console |}", "shout x = shout x" ]
      elaborating (effects <> [ "run :: Unit -> Int / {| Console |}", "run u = let", "      n :: Unit", "      n = shout 1", "    in 1" ]) \r ->
        map at r.errors `shouldEqual` []
      elaborating (effects <> [ "quiet :: Unit -> Int", "quiet u = let", "      n :: Unit", "      n = shout 1", "    in 1" ]) \r ->
        map at r.errors `shouldEqual` [ "8:7 outside: implicit-handler resolution at this checking boundary", "6:1 left unchecked" ]

    it "requires of the variables around it what its rows need, where it stands" do

      let effects = [ "effect Console where", "  log :: Int ->* Unit" ]
      elaborating (effects <> [ "o1 :: forall r. Unit -> Unit / {| Console, ...r |}", "o1 u = let", "      h :: Unit -> Unit / {| Console, ...r |}", "      h v = v", "    in h u" ]) \r ->
        map at r.errors `shouldEqual` []
      elaborating (effects <> [ "o2 :: forall r. Unit -> Unit / {| ...r |}", "o2 u = let", "      h :: Unit -> Unit / {| Console, ...r |}", "      h v = v", "    in u" ]) \r ->
        map at r.errors `shouldEqual` [ "7:27 obligation rejected" ]

    it "is outside this version where it binds a kind variable of its own or takes a synthesized argument" do
      elaborating [ "kv :: Int", "kv = let", "      q :: forall (f :: k -> Type). Int", "      q = 1", "    in q" ] \r ->
        map at r.errors `shouldEqual` [ "5:20 outside: a kind variable a local signature binds" ]
      -- reported before anything of the type is read, a kind it would equate
      -- the variable with among it
      elaborating [ "kq :: Int", "kq = let", "      q :: forall (a :: k). a", "      q = q", "    in 1" ] \r ->
        map at r.errors `shouldEqual` [ "5:20 outside: a kind variable a local signature binds" ]

      elaborating [ "data Dict a = Dict a", "make :: Int", "make = 1", "sy :: Int", "sy = let", "      s :: {{ d :: Dict Int by make }} -> Int", "      s d = 1", "    in 1" ] \r ->
        map at r.errors `shouldEqual` [ "9:7 outside: a local signature taking a synthesized argument" ]

  describe "a computation declaration" do
    let
      computations =
        [ "effect Console where"
        , "  log :: Int ->* Unit"
        , "n :: Int / {||}"
        , "n = 1"
        , "loud :: Int / {| Console |}"
        , "loud = n"
        , "louder :: Int / {| Console |}"
        , "louder = loud"
        , "anyRow :: forall e. Int / {| ...e |}"
        , "anyRow = 1"
        , "pairC :: forall a. Tuple Int (a -> a) / {||}"
        , "pairC = Tuple 1 (\\y -> y)"
        , "v :: Int"
        , "v = n"
        , "fromAny :: Int"
        , "fromAny = anyRow"
        , "loudAny :: Int / {| Console |}"
        , "loudAny = anyRow"
        , "paired :: Tuple Int (Int -> Int)"
        , "paired = pairC"
        , "again :: Int / {| Console |}"
        , "again = again"
        ]
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == Qualified (ModuleName "M") (Ident name)) values)
    it "is a thunk its body is checked in at its row, and a reference forces it, applied to `Prim.Unit`" do
      elaborating computations \r -> do
        map at r.errors `shouldEqual` []
        case bodyOf "n" r.values of
          Just (Lam _ _ (TCon u []) _ (Lit _ (LitInt 1))) | u == unitTy -> pure unit
          other -> fail ("not a thunk: " <> show other)
        bodyOf "v" r.values `shouldEqual` Just (App unit (Global unit (Qualified (ModuleName "M") (Ident "n")) []) (Global unit unitCtor []))
        -- a computation referring to itself is a function, its recursion under the thunk
        checked r \core -> shapes core `shouldEqual`
          [ "nonrec n", "nonrec loud", "nonrec louder", "nonrec anyRow", "nonrec pairC", "nonrec v", "nonrec fromAny", "nonrec loudAny", "nonrec paired", "rec again" ]

    it "forced at a value's right-hand side with a row the value's boundary cannot meet asks for an implicit handler there" do
      elaborating [ "effect Console where", "  log :: Int ->* Unit", "loud :: Int / {| Console |}", "loud = 1", "w :: Int", "w = loud" ] \r ->
        map at r.errors `shouldEqual` [ "8:1 outside: implicit-handler resolution at this checking boundary" ]

    it "taking a synthesized argument is read and published to the other bodies, its own body outside this version" do
      elaborating
        [ "data Dict a = Dict a"
        , "make :: Int"
        , "make = 1"
        , "sc :: {{ d :: Dict Int by make }} -> Int / {||}"
        , "sc = 1"
        , "use :: Int"
        , "use = sc"
        ]
        \r -> map at r.errors `shouldEqual` [ "7:1 outside: a computation taking a synthesized argument", "9:7 outside: a reference to a value taking a synthesized argument" ]

  describe "the Core module" do
    it "binds each value after what it refers to, the one written first taken first, and a recursive group as one" do
      elaborating
        [ "x :: Int"
        , "x = inc y"
        , "y :: Int"
        , "y = 1"
        , "even :: Int -> Int"
        , "even n = odd n"
        , "odd :: Int -> Int"
        , "odd n = even n"
        , "loop :: Int -> Int"
        , "loop n = loop n"
        , "pair :: Tuple Int Int"
        , "pair = Tuple 1 2"
        ]
        \r -> checked r \core -> do
          shapes core `shouldEqual` [ "nonrec y", "nonrec x", "rec even odd", "rec loop", "nonrec pair" ]
          core.imports `shouldEqual` [ lib ]

    it "is made of a recursive group initialized in the order written, and of none reading itself" do
      elaborating [ "n :: Int", "n = n", "ok :: Int", "ok = 1" ] \r -> do
        map at r.errors `shouldEqual` [ "4:5 reads n early" ]
        isNothing r.module `shouldEqual` true
      -- a recursive function stored in data, read only under its λ
      elaborating [ "fibAnd :: Tuple Int (Int -> Int)", "fibAnd = Tuple 0 (\\n -> snd fibAnd n)" ] \r -> checked r \core ->
        shapes core `shouldEqual` [ "rec fibAnd" ]

    it "is reported after what each value's local groups read, those in the order of the values" do
      elaborating [ "n :: Int", "n = n", "k :: Int", "k = let m = inc m in m", "j :: Int", "j = let w = inc w in w" ] \r ->
        map at r.errors `shouldEqual` [ "6:17 m reads local m early", "8:17 w reads local w early", "4:5 reads n early" ]

    it "is made of records of closures referring to one another, in any order" do
      elaborating
        [ "a :: Tuple Int (Int -> Int)", "a = Tuple 1 (\\n -> snd b n)", "b :: Tuple Int (Int -> Int)", "b = Tuple 2 (\\n -> snd a n)" ]
        \r -> checked r \core -> shapes core `shouldEqual` [ "rec a b" ]

    it "reports a read an application makes immediate where the reference stands and where the application does" do
      elaborating
        [ "a :: Tuple Int (Int -> Int)", "a = Tuple 1 (\\n -> snd b n)", "b :: Tuple Int (Int -> Int)", "b = Tuple (snd a 0) (\\n -> n)" ]
        \r -> map at r.errors `shouldEqual` [ "4:24 reads b early through 6:12" ]

    it "exports each value reached from outside, and carries every attribute" do
      elaboratingUnder "module M (macro mac, (+++), shown) where"
        [ "infixl 6 plus as +++"
        , "plus :: Int -> Int -> Int"
        , "plus x y = x"
        , "@[macro]"
        , "mac :: Int"
        , "mac = 1"
        , "shown :: Int"
        , "shown = 1"
        , "hidden :: Int"
        , "hidden = 1"
        ]
        \r -> checked r \core -> do
          core.exports `shouldEqual` map (ExportValue <<< Ident) [ "plus", "mac", "shown" ]
          Array.concatMap attributesOf core.decls `shouldEqual`
            [ { name: Qualified (ModuleName "Prim") (Ident "macro"), positional: [], keyword: [] } ]

    it "is made of a module declaring no value" do
      elaborating [] \r -> checked r \core -> do
        core.decls `shouldEqual` []
        core.exports `shouldEqual` []

    it "reports an attribute whose arguments do not check where its declaration stands, and is not made" do
      elaborating [ "@[label 1]", "v :: Int", "v = 1" ] \r -> do
        map at r.errors `shouldEqual` [ "5:1 attribute rejected" ]
        isNothing r.module `shouldEqual` true
      elaborating [ "@[label \"v\"]", "v :: Int", "v = 1" ] \r -> checked r \core ->
        map _.name (Array.concatMap attributesOf core.decls) `shouldEqual` [ Qualified lib (Ident "label") ]

  describe "the bodies once their jobs are run" do
    it "are values only where every equation stated for them holds" do
      let
        -- `f` states an equation that waits, then fails; `g` states one that
        -- holds, which the loop does not reach once it stops at `f`'s; `h`
        -- states none
        afterF = stated "f" 1 "b" (initialState (SessionId 0) 10)
        afterG = stated "g" 2 "a" (snd afterF)
        r = settleBodies primSession (attemptPending primSession) (snd afterG) (map body [ Tuple "f" 1, Tuple "g" 2, Tuple "h" 3 ])
      map at r.errors `shouldEqual` [ "1:1 rejected", "2:1 left unchecked" ]
      map _.name r.values `shouldEqual` [ inM "h" ]

    it "report a hole only in a body that settled, one refused or left unchecked reported by that" do
      let
        -- as above, each body holding a hole that stands for `Int`
        afterF = stated "f" 1 "b" (initialState (SessionId 0) 10)
        afterG = stated "g" 2 "a" (snd afterF)
        holding t = (body t) { holes = [ { origin: origin (snd t), name: "a", type: XCon intTy [], kind: XKType } ] }
        r = settleBodies primSession (attemptPending primSession) (snd afterG) (map holding [ Tuple "f" 1, Tuple "g" 2, Tuple "h" 3 ])
      map at r.errors `shouldEqual` [ "1:1 rejected", "2:1 left unchecked", "3:1 hole a Int" ]
      map _.name r.values `shouldEqual` []

    it "report an expression hole only in a body that settled, as a typed hole" do
      let
        afterF = stated "f" 1 "b" (initialState (SessionId 0) 10)
        afterG = stated "g" 2 "a" (snd afterF)
        holding t = (body t) { expressionHoles = [ { origin: origin (snd t), name: "a", type: XCon intTy [], context: [] } ] }
        r = settleBodies primSession (attemptPending primSession) (snd afterG) (map holding [ Tuple "f" 1, Tuple "g" 2, Tuple "h" 3 ])
      map at r.errors `shouldEqual` [ "1:1 rejected", "2:1 left unchecked", "3:1 expression hole a Int []" ]
      map _.name r.values `shouldEqual` []

    it "report an expression hole nothing noted where it stands, and leave its body no value" do
      let
        holding t = (body t) { body = EHole (origin (snd t)) (XCon intTy []) }
        noted t = (holding t) { expressionHoles = [ { origin: origin (snd t), name: "a", type: XCon intTy [], context: [] } ] }
        unnoted = settleBodies primSession (attemptPending primSession) (initialState (SessionId 0) 10) [ holding (Tuple "f" 1) ]
        reported = settleBodies primSession (attemptPending primSession) (initialState (SessionId 0) 10) [ noted (Tuple "f" 1) ]
      map at unnoted.errors `shouldEqual` [ "1:1 type undetermined" ]
      map _.name unnoted.values `shouldEqual` []
      map at reported.errors `shouldEqual` [ "1:1 expression hole a Int []" ]
      -- a record at another type is no record of this hole
      let elsewhere = settleBodies primSession (attemptPending primSession) (initialState (SessionId 0) 10) [ (noted (Tuple "f" 1)) { expressionHoles = [ { origin: origin 1, name: "a", type: XCon stringTy [], context: [] } ] } ]
      map at elsewhere.errors `shouldEqual` [ "1:1 expression hole a String []", "1:1 type undetermined" ]
      -- and so is one written elsewhere
      let apart = settleBodies primSession (attemptPending primSession) (initialState (SessionId 0) 10) [ (noted (Tuple "f" 1)) { expressionHoles = [ { origin: origin 2, name: "a", type: XCon intTy [], context: [] } ] } ]
      map at apart.errors `shouldEqual` [ "2:1 expression hole a Int []", "1:1 type undetermined" ]

    it "report a place a match leaves uncovered by the record of that match alone, one no record names being the host's defect" do
      let
        uncovered id t = (body t) { body = ECase (origin (snd t)) [ ELit (origin (snd t)) (LitInt 1) ] (XUncovered (CoverageId id)) }
        noted id recorded t = (uncovered id t) { uncovered = [ { id: CoverageId recorded, origin: origin (snd t), witness: [ WitnessAny ] } ] }
        settled bodies = settleBodies primSession (attemptPending primSession) (initialState (SessionId 0) 10) bodies
        reported = settled [ noted 0 0 (Tuple "f" 1) ]
        unrecorded = settled [ uncovered 0 (Tuple "f" 1) ]
        apart = settled [ noted 0 1 (Tuple "f" 1) ]
        defectOf r = case r.errors of
          [ Broken (UncoveredUnrecorded (CoverageId id)) ] -> Just id
          _ -> Nothing
      map at reported.errors `shouldEqual` [ "1:1 non-exhaustive" ]
      map _.name reported.values `shouldEqual` []
      -- a node no record names, and one a record of another match is beside
      defectOf unrecorded `shouldEqual` Just 0
      map _.name unrecorded.values `shouldEqual` []
      defectOf apart `shouldEqual` Just 0
      map _.name apart.values `shouldEqual` []

    it "leave a value every declaration a failed synthesis does not belong to" do
      let
        -- `f` asks a synthesizer that fails; `g` states an equation the loop
        -- does not reach once it stops at `f`'s job; `h` states none
        afterF = runAttempt primSession (createSynthesis (siteIn "f" 1) (XCon intTy []) refusingRef) (initialState (SessionId 0) 10)
        afterG = stated "g" 2 "a" (snd afterF)
        registry = Map.singleton refusingRef (\_ -> F.throw [ TextPart "no" ])
        r = settleBodies primSession (attemptJob primSession registry) (snd afterG) (map body [ Tuple "f" 1, Tuple "g" 2, Tuple "h" 3 ])
      map at r.errors `shouldEqual` [ "1:1 synthesis failed", "2:1 left unchecked" ]
      map _.name r.values `shouldEqual` [ inM "h" ]

    it "report a closing undone by what undid it, and not by the rows left undecided after" do
      let
        -- `f`'s boundary holds `( Console | ?a )` and `( Clock | ?b )`, whose
        -- union is formed only once their tails are closed, and then holds
        -- what `()` cannot
        effect n = XRowEffectEntry (Qualified (ModuleName "M") (EffName n)) []
        afterF = runAttempt primSession
          ( do
              sigma <- openBoundary emptyXContext
              a <- freshTypeMeta emptyXContext (XKRow RowEffect)
              b <- freshTypeMeta emptyXContext (XKRow RowEffect)
              _ <- placeFit (siteIn "f" 1) Wrapping (XRowExtend (effect "Console") a) (XMeta sigma)
              _ <- placeFit (siteIn "f" 1) Wrapping (XRowExtend (effect "Clock") b) (XMeta sigma)
              closeBoundary (siteIn "f" 1) sigma XRowEmpty
          )
          (initialState (SessionId 0) 100)
        r = settleBodies primSession (attemptPending primSession) (snd afterF) (map body [ Tuple "f" 1, Tuple "h" 3 ])
      map at r.errors `shouldEqual` [ "1:1 outside: implicit-handler resolution at this checking boundary" ]
      map _.name r.values `shouldEqual` [ inM "h" ]

    it "closes, a round at a time, a tail a pending `case` comes to need once another's is closed" do
      case runAttempt primSession (Tuple <$> freshTypeMeta emptyXContext rowType <*> freshTypeMeta emptyXContext rowType) (initialState (SessionId 0) 100) of
        Tuple (Done (Tuple first second)) state -> do
          let
            closedIn metas = case _ of
              XMeta m -> case lookupMeta metas m of
                Just (Assigned _) -> true
                _ -> false
              _ -> false
            -- the first closes its tail; the second needs its own closed only
            -- once the first's is, and is built at 2 where it was
            leading = { id: PendingCaseId 0, site: siteIn "f" 1, closable: \ms -> Right (if closedIn ms first then [] else [ first ]), assembled: \_ -> pure (EPendingCase (origin 1) (PendingCaseId 1)) }
            following = { id: PendingCaseId 1, site: siteIn "f" 1, closable: \ms -> Right (if closedIn ms first && not (closedIn ms second) then [ second ] else []), assembled: \ms -> pure (ELit (origin 1) (LitInt (if closedIn ms second then 2 else 1))) }
            r = settleBodies primSession (attemptPending primSession) state [ (body (Tuple "f" 1)) { body = EPendingCase (origin 1) (PendingCaseId 0), pending = [ leading, following ] } ]
          map at r.errors `shouldEqual` []
          map (map (const unit) <<< _.body) r.values `shouldEqual` [ Lit unit (LitInt 2) ]
        _ -> fail "no metavariables made"

    it "reports a declaration whose tail cannot be closed, leaves one still pending unchecked, and settles the rest" do
      let
        -- `f`'s match closes a row holding `a`, which the empty row is not
        failing = { id: PendingCaseId 0, site: siteIn "f" 1, closable: \_ -> Right [ fieldOf "a" ], assembled: \_ -> pure (ELit (origin 1) (LitInt 1)) }
        quiet = { id: PendingCaseId 1, site: siteIn "g" 2, closable: \_ -> Right [], assembled: \_ -> pure (ELit (origin 2) (LitInt 1)) }
        pendingIn (Tuple name line) p = (body (Tuple name line)) { body = EPendingCase (origin line) p.id, pending = [ p ] }
        r = settleBodies primSession (attemptPending primSession) (initialState (SessionId 0) 100)
          [ pendingIn (Tuple "f" 1) failing, pendingIn (Tuple "g" 2) quiet, body (Tuple "h" 3) ]
      map at r.errors `shouldEqual` [ "1:1 rejected", "2:1 left unchecked" ]
      map _.name r.values `shouldEqual` [ inM "h" ]

    it "breaks where a pending `case` and its record do not stand one to one" do
      let
        recorded id = { id: PendingCaseId id, site: siteIn "f" 1, closable: \_ -> Right [], assembled: \_ -> pure (ELit (origin 1) (LitInt 1)) }
        node id = EPendingCase (origin 1) (PendingCaseId id)
        settledWith term pending = (settleBodies primSession (attemptPending primSession) (initialState (SessionId 0) 100) [ (body (Tuple "f" 1)) { body = term, pending = pending } ]).errors
        broken = case _ of
          [ Broken d ] -> Just d
          _ -> Nothing
      broken (settledWith (node 0) []) `shouldEqual` Just (PendingCaseUnrecorded (PendingCaseId 0))
      broken (settledWith (ELit (origin 1) (LitInt 1)) [ recorded 0 ]) `shouldEqual` Just (PendingCaseNodeless (PendingCaseId 0))
      broken (settledWith (EApp (origin 1) (node 0) (node 0)) [ recorded 0 ]) `shouldEqual` Just (PendingCaseRepeated (PendingCaseId 0))

    it "takes a tail of a level outside the one settling as one no match may close" do
      case runAttempt primSession (freshTypeMeta emptyXContext rowType) (initialState (SessionId 0) 100) of
        Tuple (Done tail) state -> do
          let variant = XApp (XCon variantTy []) (XRowExtend (XRowTypeEntry (TagKey (Tag "A")) (XCon unitTy [])) tail)
          (tagsOf 1 state.tentative.metas variant).tail `shouldEqual` External
          (tagsOf 0 state.tentative.metas variant).tail `shouldEqual` Flexible [ tail ]
        _ -> fail "no metavariable made"
  where
  primSession = sessionEnvOf primSignature []
  rowType = XKRow RowType
  fieldOf key = XRowExtend (XRowTypeEntry (SymbolKey (Symbol key)) (XCon intTy [])) XRowEmpty
  origin line = Surface.FromSource (inSource { line, column: 1 } { line, column: 2 })
  refusingRef = Qualified (ModuleName "Synth") (Ident "refusing")
  -- `?v ⊎ ?w ≡ ( a : Int | () )`, which waits, then `?v ≡ ( key : Int | () )`
  -- and `?w ≡ ()`, which decide it
  stated name line key = runAttempt primSession
    ( do
        v <- freshTypeMeta emptyXContext rowType
        w <- freshTypeMeta emptyXContext rowType
        equate (siteIn name line) { kind: rowType, left: XRowUnion v w, right: fieldOf "a" }
        equate (siteIn name line) { kind: rowType, left: v, right: fieldOf key }
        equate (siteIn name line) { kind: rowType, left: w, right: XRowEmpty }
    )
  inM = Qualified (ModuleName "M") <<< Ident
  siteIn name line = { context: emptyXContext, origin: AtSource { declaration: inM name, origin: origin line } }
  body (Tuple name line) = { name: inM name, origin: origin line, ordinal: line, attributes: [], scheme: { kindVars: [], body: int }, spine: plainScheme { kindVars: [], body: int }, body: ELit (origin line) (LitInt 1), holes: [], wildcards: [], unwritten: [], expressionHoles: [], uncovered: [], pending: [], regions: [], references: [] }
