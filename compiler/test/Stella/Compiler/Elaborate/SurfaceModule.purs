-- | Value declarations written in source, resolved, elaborated against what
-- | their imports reach, and handed to the Core checker.
module Test.Stella.Compiler.Elaborate.SurfaceModule (spec) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
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
import Stella.Compiler.Elaborate.Surface.Module (ElaboratedValue, ElaborationError(..), elaborateValues, settleBodies)
import Stella.Compiler.Elaborate.Surface.Type (Unsupported(..))
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeEntity(..), TypeSort(..), ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Scheme (plainScheme)
import Stella.Compiler.Resolve.Module (resolveModule)
import Stella.Compiler.Surface.Origin (rangeOf)
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore (Decl(..), Module, declare, primSignature)
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (Ident(..), KindVar(..), ModuleName(..), Qualified(..), Symbol(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (intTy, pureFn)
import Stella.Compiler.TypedCore.Signature (Signature)
import Stella.Compiler.TypedCore.Type (RowKey(..), Type(..))
import Stella.Compiler.TypedCore.Term (Literal(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

lib :: ModuleName
lib = ModuleName "Lib"

int :: Type
int = TCon intTy []

-- | `Lib`: `inc : Int -> Int`, `id : forall a. a -> a`, and
-- | `const : forall a b. a -> b -> a`; and `foreign type Phantom` at
-- | `forall k. Type`.
libInterface :: ModuleInterface
libInterface =
  { name: lib
  , imports: []
  , exports: emptyExports
      { values = Map.fromFoldable (map (\n -> Tuple n { entity: Qualified lib (Ident n), via: Declared }) [ "inc", "id", "const" ])
      , types = Map.singleton "Phantom" { entity: TypeEntity (Qualified lib (TyName "Phantom")), via: Declared, members: [] }
      }
  , declarations: emptyDeclarations
      { values = Map.fromFoldable
          [ value "inc" (pureFn int int)
          , value "id" (TForall a KType (pureFn (TVar a) (TVar a)))
          , value "const" (TForall a KType (TForall b KType (pureFn (TVar a) (pureFn (TVar b) (TVar a)))))
          ]
      , types = Map.singleton (TyName "Phantom") { kind: { kindVars: [ KindVar "k" ], body: KType }, sort: ForeignType, attributes: [] }
      }
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }
  where
  a = TyVar "a"
  b = TyVar "b"
  value n ty = Tuple (Ident n) { sort: SortForeign MayObserve, scheme: plainScheme (monoScheme ty), attributes: [] }

environment :: Either String BuildEnvironment
environment = case addInterface libInterface initialEnvironment of
  Right env -> Right env
  Left err -> Left (show err)

type Ran = { values :: Array ElaboratedValue, errors :: Array ElaborationError, signature :: Signature }

-- | The module `M`, importing `Lib`, declaring the lines given; elaborated.
elaborating :: Array String -> (Ran -> Aff Unit) -> Aff Unit
elaborating body k = case environment of
  Left err -> fail err
  Right env -> case parseModule (joinWith "\n" ([ "module M where", "import Lib" ] <> body)) of
    Left err -> fail (printSyntaxError err)
    Right cst -> do
      let resolved = resolveModule env cst
      case resolved.errors, viewFor [ lib ] env of
        [], Right view -> case importedSignature env view of
          Left err -> fail (show err)
          Right signature -> do
            let elaborated = elaborateValues signature (importedCatalog env view) resolved.module
            k { values: elaborated.values, errors: elaborated.errors, signature }
        errors, _ -> fail ("not resolved: " <> show errors)

-- | The values as a Core module, in the order written, which the Core checker
-- | is to accept.
checked :: Ran -> Aff Unit
checked r = case declare r.signature coreModule of
  Left err -> fail ("the Core checker refused it: " <> show err.error)
  Right _ -> pure unit
  where
  coreModule :: Module Surface.Origin
  coreModule =
    { annotation: case Array.head r.values of
        Just v -> v.origin
        Nothing -> Surface.FromSource (inSource { line: 0, column: 0 } { line: 0, column: 0 })
    , name: ModuleName "M"
    , imports: [ lib ]
    , exports: []
    , decls: map (\v -> DeclNonRec v.origin { name: nameOf v.name, scheme: v.scheme, value: v.body, attributes: [] }) r.values
    }
  nameOf (Qualified _ n) = n

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
          checked r

    it "may refer to a value the module declares after it, itself among them" do
      elaborating [ "a :: Int -> Int", "a x = b (a x)", "b :: Int -> Int", "b y = a y" ] \r -> do
        map at r.errors `shouldEqual` []
        map _.name r.values `shouldEqual` map (Qualified (ModuleName "M") <<< Ident) [ "a", "b" ]

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
  body (Tuple name line) = { name: inM name, origin: origin line, scheme: { kindVars: [], body: int }, body: ELit (origin line) (LitInt 1) }
