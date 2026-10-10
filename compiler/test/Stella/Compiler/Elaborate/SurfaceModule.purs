-- | Data and value declarations written in source, resolved, elaborated
-- | against what their imports reach, and handed to the Core checker.
module Test.Stella.Compiler.Elaborate.SurfaceModule (spec) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing)
import Data.Set as Set
import Data.String (joinWith)
import Data.Tuple (Tuple(..), snd)
import Effect.Aff (Aff)
import Stella.Compiler.CST (parseModule, printSyntaxError)
import Stella.Compiler.CST.Types (inSource)
import Stella.Compiler.Surface.Decl (Observation(..))
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Term (XExpr(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XRowEntry(..), XType(..), fromCore)
import Stella.Compiler.Elaborate.Driver.Attempt (attemptPending, runAttempt)
import Stella.Compiler.Elaborate.Driver.Synthesis (attemptJob)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Environment.Imported (importedCatalog, importedSignature, sessionEnvOf)
import Stella.Compiler.Elaborate.Environment.Surface (importedSurface)
import Stella.Compiler.Elaborate.Kernel.Elab (closeBoundary, createSynthesis, equate, freshTypeMeta, initialState, openBoundary, placeFit)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitUse(..))
import Stella.Compiler.Elaborate.Surface.Module (ElaboratedValue, ElaborationError(..), elaborateModule, settleBodies)
import Stella.Compiler.Elaborate.Surface.Report (printType)
import Stella.Compiler.Elaborate.Surface.Type (Unsupported(..))
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeEntity(..), TypeSort(..), ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Scheme (plainScheme)
import Stella.Compiler.Resolve.Module (resolveModule)
import Stella.Compiler.Surface.Origin (rangeOf)
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore (Attribute, DataDecl, Decl(..), Declared, Export(..), Expr(..), Module, primSignature)
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), KindVar(..), ModuleName(..), Qualified(..), Symbol(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (intTy, pureFn, stringTy, unitCtor, unitTy)
import Stella.Compiler.TypedCore.Type (RowKey(..), Type(..))
import Stella.Compiler.TypedCore.Term (Literal(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

lib :: ModuleName
lib = ModuleName "Lib"

int :: Type
int = TCon intTy []

-- | `Lib`: `inc : Int -> Int`, `id : forall a. a -> a`, and
-- | `const : forall a b. a -> b -> a`; `data Tuple a b = Tuple a b` and
-- | `snd : forall a b. Tuple a b -> b`; and `foreign type Phantom` at
-- | `forall k. Type`; and `attribute label (text :: String)`.
libInterface :: ModuleInterface
libInterface =
  { name: lib
  , imports: []
  , exports: emptyExports
      { values = Map.fromFoldable (map (\n -> Tuple n { entity: Qualified lib (Ident n), via: Declared }) [ "inc", "id", "const", "snd", "Tuple" ])
      , types = Map.fromFoldable
          [ Tuple "Phantom" { entity: TypeEntity (Qualified lib (TyName "Phantom")), via: Declared, members: [] }
          , Tuple "Tuple" { entity: TypeEntity (Qualified lib (TyName "Tuple")), via: Declared, members: [ Ident "Tuple" ] }
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

environment :: Either String BuildEnvironment
environment = case addInterface libInterface initialEnvironment of
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
elaboratingUnder header body k = case environment of
  Left err -> fail err
  Right env -> case parseModule (joinWith "\n" ([ header, "import Lib" ] <> body)) of
    Left err -> fail (printSyntaxError err)
    Right cst -> do
      let resolved = resolveModule env cst
      case resolved.errors, viewFor [ lib ] env of
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
  SignatureNeeded o _ -> located o <> " signature needed"
  ConstraintEscapes o _ -> located o <> " constraint escapes"
  SynthesisUndecided o -> located o <> " synthesis undecided"
  KindUndetermined o -> located o <> " kind undetermined"
  Rejected (EquationFailed (AtSource s) _) -> located s.origin <> " rejected"
  Rejected (SynthesisFailed { goal: { origin: AtSource s } }) -> located s.origin <> " synthesis failed"
  Rejected _ -> "rejected"
  EquationUndecided _ -> "undecided"
  TypeUndetermined o -> located o <> " type undetermined"
  LeftUnchecked o _ -> located o <> " left unchecked"
  AttributeRejected o _ -> located o <> " attribute rejected"
  ForeignRefused o _ r -> located o <> " foreign refused " <> show r.position <> " " <> show r.refusal
  TypeHoleStands o name t -> located o <> " hole " <> name <> " " <> printType t
  ValueFormNeeded o -> located o <> " value form needed"
  EffectRowAmbiguous _ os -> joinWith " " (map located os) <> " effect row ambiguous"
  CoreRefused _ -> "the Core checker refused it"
  InternalEntryMismatch _ -> "an internal entry mismatched"
  Broken _ -> "broken"
  AttemptPostponed -> "postponed"
  where
  located o = let r = rangeOf o in show r.start.line <> ":" <> show r.start.column

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

  describe "what is not elaborated" do
    it "is reported where it stands, and leaves the rest elaborated" do
      elaborating
        [ "k = 1"
        , "bad :: Int"
        , "bad = inc"
        , "lam :: Int"
        , "lam = (1, 2)"
        , "open :: Int"
        , "open = const 1 id"
        , "ok :: Int"
        , "ok = 1"
        ]
        \r -> do
          map at r.errors `shouldEqual`
            [ "5:7 rejected"
            , "7:8 outside: this form"
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

    it "is outside what this version elaborates where only generalizing would decide a parameter's kind" do
      elaborating [ "data App f a = App (f a)", "ok :: Int", "ok = 1" ] \r -> do
        map at r.errors `shouldEqual`
          [ "3:10 outside: a type parameter whose kind is decided only by generalizing it; its kind must be written"
          , "3:12 outside: a type parameter whose kind is decided only by generalizing it; its kind must be written"
          ]
        -- a data declaration that does not elaborate leaves the values unread
        r.values `shouldEqual` []
      elaborating [ "data Proxy a = Proxy" ] \r ->
        map at r.errors `shouldEqual` [ "3:12 outside: a type parameter whose kind is decided only by generalizing it; its kind must be written" ]

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

  describe "what a quantifier encloses" do
    let
      bodyOf name values = map (map (const unit) <<< _.body) (Array.find (\x -> x.name == Qualified (ModuleName "M") (Ident name)) values)
      idOf = Qualified lib (Ident "id")
      tupleOf = Qualified lib (Ident "Tuple")
      -- `Λ a. λ x. id [a] x`, whatever the names
      expanded = case _ of
        Just (TyLam _ a _ (Lam _ x _ (App _ (TyApp _ (Global _ g _) (TVar a')) (Var _ x')))) -> g == idOf && a == a' && x == x'
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
            Just (Lam _ _ _ inner) -> expanded (Just inner) `shouldEqual` true
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
            Just (TyLam _ _ _ (Lam _ _ _ (App _ (OpenEff _ _ (TyApp _ (Global _ g _) _)) _))) | g == idOf -> pure unit
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
            Just (Lam _ _ _ (TyLam _ _ _ (App _ (TyApp _ (TyApp _ (Global _ c _) _) _) (Lit _ (LitInt 1))))) | c == tupleOf -> pure unit
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
          Just (TyLam _ _ _ (TyLam _ _ _ (Lam _ _ _ (App _ (OpenEff _ _ _) _)))) -> pure unit
          other -> fail ("not widened under the λ: " <> show other)
        checked r \core -> shapes core `shouldEqual` [ "nonrec spread" ]

    it "is reported where it is no value form and is not expanded, a function's parameter asked for" do
      elaborating [ "bad :: forall a. a -> a", "bad = const id 1" ] \r ->
        map at r.errors `shouldEqual` [ "4:1 value form needed" ]
      elaborating [ "pair :: forall a. Tuple Int (a -> a)", "pair = Tuple (inc 1) id" ] \r ->
        map at r.errors `shouldEqual` [ "4:1 value form needed" ]

    it "keeps a reference made before any λ immediate once expanded, a recursive value no function" do
      elaborating [ "loop :: forall a. a -> a", "loop = loop" ] \r ->
        map at r.errors `shouldEqual` [ "4:1 outside: a recursive value that is no function" ]
      elaborating [ "p :: forall a. a -> a", "p = q", "q :: forall a. a -> a", "q = p" ] \r ->
        map at r.errors `shouldEqual` [ "4:1 outside: a recursive value that is no function", "6:1 outside: a recursive value that is no function" ]

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
          Just (TyLam _ a _ (Lam _ x _ (App _ (TyApp _ (Global _ _ _) (TVar a')) (Var _ x')))) | a == a' && x == x' -> pure unit
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

    it "is outside this version where it is recursive" do
      elaborating [ "loop x = loop x", "p x = q x", "q x = p x", "ok = 1" ] \r -> do
        map at r.errors `shouldEqual`
          [ "3:1 outside: a recursive declaration without a signature"
          , "4:1 outside: a recursive declaration without a signature"
          , "5:1 outside: a recursive declaration without a signature"
          ]
        map _.name r.values `shouldEqual` [ inM "ok" ]

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
      elaborating [ "bad :: _", "bad = 1", "user = bad", "signed :: Int", "signed = bad", "ok = user" ] \r -> do
        map at r.errors `shouldEqual` [ "3:8 outside: a wildcard", "5:1 left unchecked", "8:1 left unchecked", "7:1 left unchecked" ]
        map _.name r.values `shouldEqual` []

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
          Just (Lam _ _ (TCon u []) (Lit _ (LitInt 1))) | u == unitTy -> pure unit
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

    it "is not made of a recursive value that is no function, which this version does not elaborate" do
      elaborating [ "n :: Int", "n = n", "ok :: Int", "ok = 1" ] \r -> do
        map at r.errors `shouldEqual` [ "4:1 outside: a recursive value that is no function" ]
        isNothing r.module `shouldEqual` true
      -- a recursive function stored in data is no different yet
      elaborating [ "fibAnd :: Tuple Int (Int -> Int)", "fibAnd = Tuple 0 (\\n -> snd fibAnd n)" ] \r -> do
        map at r.errors `shouldEqual` [ "4:1 outside: a recursive value that is no function" ]
        isNothing r.module `shouldEqual` true

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
  body (Tuple name line) = { name: inM name, origin: origin line, ordinal: line, attributes: [], scheme: { kindVars: [], body: int }, spine: plainScheme { kindVars: [], body: int }, body: ELit (origin line) (LitInt 1), holes: [], wildcards: [] }
