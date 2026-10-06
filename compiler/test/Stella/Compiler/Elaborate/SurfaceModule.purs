-- | Value declarations written in source, resolved, elaborated against what
-- | their imports reach, and handed to the Core checker.
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
import Stella.Compiler.Elaborate.CorePlus.Type (XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Driver.Attempt (attemptPending, runAttempt)
import Stella.Compiler.Elaborate.Driver.Synthesis (attemptJob)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Environment.Imported (importedCatalog, importedSignature, sessionEnvOf)
import Stella.Compiler.Elaborate.Kernel.Elab (createSynthesis, equate, freshTypeMeta, initialState)
import Stella.Compiler.Elaborate.Surface.Module (ElaboratedValue, ElaborationError(..), elaborateModule, settleBodies)
import Stella.Compiler.Elaborate.Surface.Type (Unsupported(..))
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeEntity(..), TypeSort(..), ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Scheme (plainScheme)
import Stella.Compiler.Resolve.Module (resolveModule)
import Stella.Compiler.Surface.Origin (rangeOf)
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore (Attribute, Decl(..), Declared, Export(..), Module, primSignature)
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (Ident(..), KindVar(..), ModuleName(..), Qualified(..), Symbol(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (intTy, pureFn, stringTy)
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
            let elaborated = elaborateModule signature (importedCatalog env view) resolved.module resolved.exports
            k case elaborated.result of
              Left errors -> { values: elaborated.values, errors: NonEmptyArray.toArray errors, module: Nothing }
              Right made -> { values: elaborated.values, errors: [], module: Just made }
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
  WithoutSignature o _ -> located o <> " without a signature"
  KindUndetermined o -> located o <> " kind undetermined"
  Rejected (EquationFailed (AtSource s) _) -> located s.origin <> " rejected"
  Rejected (SynthesisFailed { goal: { origin: AtSource s } }) -> located s.origin <> " synthesis failed"
  Rejected _ -> "rejected"
  EquationUndecided _ -> "undecided"
  TypeUndetermined o -> located o <> " type undetermined"
  LeftUnchecked o _ -> located o <> " left unchecked"
  AttributeRejected o _ -> located o <> " attribute rejected"
  CoreRefused _ -> "the Core checker refused it"
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
        , "lam = (\\x -> x) 1"
        , "open :: Int"
        , "open = const 1 id"
        , "data T = T"
        , "ok :: Int"
        , "ok = 1"
        ]
        \r -> do
          map at r.errors `shouldEqual`
            [ "3:1 without a signature"
            , "10:6 outside: this declaration"
            , "5:7 rejected"
            , "7:9 outside: a λ whose type is not known where it stands"
            , "9:8 type undetermined"
            , "9:16 type undetermined"
            ]
          map _.name r.values `shouldEqual` [ Qualified (ModuleName "M") (Ident "ok") ]

    it "reports a constructor whose kind arguments nothing decides, and leaves its declaration out" do
      elaborating [ "p :: Phantom -> Int", "p x = 1", "ok :: Int", "ok = 1" ] \r -> do
        map at r.errors `shouldEqual` [ "3:6 kind undetermined" ]
        map _.name r.values `shouldEqual` [ Qualified (ModuleName "M") (Ident "ok") ]

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
        r = settleBodies (attemptPending primSession) (snd afterG) (map body [ Tuple "f" 1, Tuple "g" 2, Tuple "h" 3 ])
      map at r.errors `shouldEqual` [ "1:1 rejected", "2:1 left unchecked" ]
      map _.name r.values `shouldEqual` [ inM "h" ]

    it "leave a value every declaration a failed synthesis does not belong to" do
      let
        -- `f` asks a synthesizer that fails; `g` states an equation the loop
        -- does not reach once it stops at `f`'s job; `h` states none
        afterF = runAttempt primSession (createSynthesis (siteIn "f" 1) (XCon intTy []) refusingRef Nothing) (initialState (SessionId 0) 10)
        afterG = stated "g" 2 "a" (snd afterF)
        registry = Map.singleton refusingRef (\_ -> F.throw [ TextPart "no" ])
        r = settleBodies (attemptJob primSession registry) (snd afterG) (map body [ Tuple "f" 1, Tuple "g" 2, Tuple "h" 3 ])
      map at r.errors `shouldEqual` [ "1:1 synthesis failed", "2:1 left unchecked" ]
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
  body (Tuple name line) = { name: inM name, origin: origin line, ordinal: line, attributes: [], scheme: { kindVars: [], body: int }, body: ELit (origin line) (LitInt 1) }
