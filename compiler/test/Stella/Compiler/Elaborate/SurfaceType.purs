-- | A signature of the Surface AST elaborated into Core⁺: its kinds inferred
-- | from what it applies, its unwritten kinds required solved once it is done,
-- | and what this version does not read reported where it stands.
module Test.Stella.Compiler.Elaborate.SurfaceType (spec) where

import Prelude
import Prim hiding (Type)

import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.CST.Types (inSource)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.Environment.Imported (sessionEnvOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Outcome(..), emptySessionEnv, equateKinds, freshKindMeta, initialState, runElabIn)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (KindRequirement(..), UnifyError(..))
import Data.Set as Set
import Data.Array as Array
import Stella.Compiler.Elaborate.CorePlus.Type (XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Surface.Report (printType)
import Stella.Compiler.Elaborate.Surface.Type (Elaborated, Unsupported(..), elaborateSignature, settledScheme, xFunction)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Surface.Name (BindingId(..), TypeVar(..))
import Stella.Compiler.Surface.Origin as Surface
import Data.Foldable (foldr)
import Stella.Compiler.Surface.Type (EffectApplication, EffectRowItem(..), Kind(..), RecordRowItem(..), Type(..), TypeOperatorTarget(..), VariantRowItem(..))
import Stella.Compiler.TypedCore (Decl(..), Module, declare, primSignature)
import Stella.Compiler.TypedCore.Kind (Kind(..)) as Core
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), KindVar(..), ModuleName(..), OpName(..), Qualified(..), Symbol(..), Tag(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (fn, intTy, pureFn, recordTy, unitTy, variantTy)
import Stella.Compiler.TypedCore.Type (RowEntry(..), Type(..), TypeScheme) as Core
import Stella.Compiler.TypedCore.Type (RowKey(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

lib :: ModuleName
lib = ModuleName "Lib"

-- | `data Box a = Box a`, `data Pair a b = Pair a b`, `data Phantom = Phantom` at
-- | `forall k. Type`, `effect Console`, and `effect State (s :: Type)`.
libCore :: Module Unit
libCore =
  { annotation: unit
  , name: lib
  , imports: []
  , exports: []
  , decls:
      [ DeclData unit { name: TyName "Box", kindVars: [], params: [ { name: TyVar "a", kind: Core.KType } ], constructors: [ { name: Ident "Box", tag: 0, fields: [ Core.TVar (TyVar "a") ] } ], isNewtype: false, attributes: [] }
      , DeclData unit { name: TyName "Phantom", kindVars: [ KindVar "k" ], params: [], constructors: [ { name: Ident "Phantom", tag: 0, fields: [] } ], isNewtype: false, attributes: [] }
      , DeclData unit { name: TyName "Pair", kindVars: [], params: [ { name: TyVar "a", kind: Core.KType }, { name: TyVar "b", kind: Core.KType } ], constructors: [ { name: Ident "Pair", tag: 0, fields: [ Core.TVar (TyVar "a"), Core.TVar (TyVar "b") ] } ], isNewtype: false, attributes: [] }
      , DeclEffect unit { name: EffName "Console", params: [], operations: [ { name: OpName "log", tyBinders: [], argument: coreInt, resumesWith: Core.TCon unitTy [] } ], attributes: [] }
      , DeclEffect unit { name: EffName "State", params: [ { name: TyVar "s", kind: Core.KType } ], operations: [ { name: OpName "get", tyBinders: [], argument: Core.TCon unitTy [], resumesWith: Core.TVar (TyVar "s") } ], attributes: [] }
      ]
  }

-- | A position of line 1, standing for where a node was written.
at :: Int -> Surface.Origin
at c = Surface.FromSource (inSource { line: 1, column: c } { line: 1, column: c + 1 })

var :: Int -> String -> TypeVar
var n name = TypeVar { id: BindingId n, name: TyVar name }

a :: TypeVar
a = var 0 "a"

f :: TypeVar
f = var 1 "f"

v :: TypeVar -> Type
v x = TypeVariable (at 1) x

box :: Type
box = TypeConstructor (at 2) (Qualified lib (TyName "Box"))

int :: Type
int = TypeConstructor (at 3) intTy

arrow :: Type -> Type -> Type
arrow x y = TypeFunction (at 4) x y Nothing

app :: Type -> Type -> Type
app = TypeApp (at 5)

declaration :: Qualified Ident
declaration = Qualified (ModuleName "M") (Ident "f")

type Ran = { outcome :: Outcome Elaborated, scheme :: Either (Array Surface.Origin) Core.TypeScheme }

-- | The signature elaborated in a session of `Lib`, and its scheme settled.
elaborating :: Array TypeVar -> Type -> (Ran -> Aff Unit) -> Aff Unit
elaborating implicit body k = case declare primSignature libCore of
  Left err -> fail (show err.error)
  Right sig -> do
    let Tuple outcome state = runElabIn (sessionEnvOf sig []) (initialState (SessionId 0) 10) (elaborateSignature declaration { implicit, body })
    k
      { outcome
      , scheme: case outcome of
          Done e -> case settledScheme state.tentative.metas e of
            Left places -> Left (NonEmptyArray.toArray places)
            Right scheme -> Right scheme
          _ -> Left []
      }

coreBox :: Core.Type -> Core.Type
coreBox = Core.TApp (Core.TCon (Qualified lib (TyName "Box")) [])

coreInt :: Core.Type
coreInt = Core.TCon intTy []

rowVar :: TypeVar
rowVar = var 2 "e"

consoleName :: Qualified EffName
consoleName = Qualified lib (EffName "Console")

stateName :: Qualified EffName
stateName = Qualified lib (EffName "State")

pairName :: Qualified TyName
pairName = Qualified lib (TyName "Pair")

console :: Int -> EffectApplication
console c = { origin: at c, effect: consoleName, arguments: [] }

state :: Int -> Array Type -> EffectApplication
state c arguments = { origin: at c, effect: stateName, arguments }

-- | `Record` of the closed row given.
record :: Array (Tuple RowKey Core.Type) -> Core.Type
record fields = Core.TApp (Core.TCon recordTy []) (foldr (\(Tuple k t) rest -> Core.TRowExtend (Core.RowTypeEntry k t) rest) Core.TRowEmpty fields)

spec :: Spec Unit
spec = describe "Stella.Compiler.Elaborate.Surface.Type" do
  describe "a signature" do
    it "quantifies its implicit variables, their kinds read off what it applies" do
      elaborating [ a ] (arrow (v a) (app box (v a))) \r ->
        r.scheme `shouldEqual` Right
          { kindVars: [], body: Core.TForall (TyVar "a") Core.KType (pureFn (Core.TVar (TyVar "a")) (coreBox (Core.TVar (TyVar "a")))) }
      elaborating [ f, a ] (arrow (app (v f) (v a)) (app (v f) int)) \r ->
        r.scheme `shouldEqual` Right
          { kindVars: []
          , body: Core.TForall (TyVar "f") (Core.KFun Core.KType Core.KType)
              (Core.TForall (TyVar "a") Core.KType (pureFn (Core.TApp (Core.TVar (TyVar "f")) (Core.TVar (TyVar "a"))) (Core.TApp (Core.TVar (TyVar "f")) coreInt)))
          }
      -- `f a -> Int` decides `f` at `? -> Type` and nothing of `a`
      elaborating [ f, a ] (arrow (app (v f) (v a)) int) \r ->
        r.scheme `shouldEqual` Left [ at 1 ]

    it "binds a forall's variables at the kinds written" do
      elaborating [] (TypeForall (at 6) [ { origin: at 7, var: f, kind: Just (KindArrow (at 8) (KindType (at 8)) (KindType (at 8))) } ] (arrow (app (v f) int) int)) \r ->
        r.scheme `shouldEqual` Right
          { kindVars: []
          , body: Core.TForall (TyVar "f") (Core.KFun Core.KType Core.KType) (pureFn (Core.TApp (Core.TVar (TyVar "f")) coreInt) coreInt)
          }

    it "refuses an application at the wrong kind, where it stands" do
      elaborating [] (arrow (app box box) int) \r -> case r.outcome of
        Failed (EquationFailed (AtSource o) _) -> o.origin `shouldEqual` at 5
        _ -> fail "not refused"

    it "introduces a type variable only at a kind it may be, written or decided" do
      -- `Row Type` may be quantified over, `Effect` and what produces it may not
      elaborating [] (TypeForall (at 6) [ { origin: at 7, var: a, kind: Just (KindRow (at 8) RowType) } ] int) \r ->
        r.scheme `shouldEqual` Right { kindVars: [], body: Core.TForall (TyVar "a") (Core.KRow RowType) coreInt }
      elaborating [] (TypeForall (at 6) [ { origin: at 7, var: a, kind: Just (KindEffect (at 8)) } ] int) \r -> case r.outcome of
        Failed (EquationFailed (AtSource o) (KindNotQuantifiable _)) -> o.origin `shouldEqual` at 7
        _ -> fail "not refused"
      elaborating [] (TypeForall (at 6) [ { origin: at 7, var: f, kind: Just (KindArrow (at 8) (KindType (at 8)) (KindEffect (at 8))) } ] int) \r -> case r.outcome of
        Failed (EquationFailed _ (KindNotQuantifiable _)) -> pure unit
        _ -> fail "not refused"
      -- a kind left unwritten, then decided to be one a variable may not be
      let
        site = { context: emptyXContext, origin: InDeclaration declaration }
        deciding kind = runElabIn emptySessionEnv (initialState (SessionId 0) 10) do
          k <- freshKindMeta Set.empty (Set.singleton Quantifiable)
          equateKinds site k kind
      case deciding XKEffect of
        Tuple (Failed (EquationFailed _ (KindNotQuantifiable _))) _ -> pure unit
        _ -> fail "decided to be Effect"
      case deciding (XKRow RowType) of
        Tuple (Done _) _ -> pure unit
        _ -> fail "not decided to be Row Type"

    it "names the binder whose kind nothing decides" do
      elaborating [] (TypeForall (at 6) [ { origin: at 7, var: a, kind: Nothing } ] int) \r ->
        r.scheme `shouldEqual` Left [ at 7 ]

    it "names a constructor whose kind arguments nothing decides" do
      -- `Phantom` is at `forall k. Type`, and nothing it stands in says what `k` is
      elaborating [] (arrow (TypeConstructor (at 11) (Qualified lib (TyName "Phantom"))) int) \r ->
        r.scheme `shouldEqual` Left [ at 11 ]

    it "reports what this version does not read, and reads what surrounds it" do
      elaborating [ a ] (arrow (TypeRecord (at 9) [ RecordField (at 9) (Symbol "x") (v a), RecordSpread (at 12) Nothing ]) (TypeSynonym (at 10) (Qualified lib (TyName "S")))) \r -> case r.outcome of
        Done e -> e.unsupported `shouldEqual` [ OutsideSubset (at 12) "a spread", OutsideSubset (at 10) "a type synonym" ]
        _ -> fail "not elaborated"

  describe "a row" do
    it "is read in the bracket it is written in: a record's and a variant's at Row Type, a tuple's keyed by position" do
      elaborating [] (arrow (TypeRecord (at 9) [ RecordField (at 9) (Symbol "name") int ]) int) \r ->
        r.scheme `shouldEqual` Right { kindVars: [], body: pureFn (record [ Tuple (SymbolKey (Symbol "name")) coreInt ]) coreInt }
      elaborating [ a ] (arrow (TypeTuple (at 9) [ int, app box (v a) ]) int) \r ->
        r.scheme `shouldEqual` Right
          { kindVars: []
          , body: Core.TForall (TyVar "a") Core.KType (pureFn (record [ Tuple (PositionKey 0) coreInt, Tuple (PositionKey 1) (coreBox (Core.TVar (TyVar "a"))) ]) coreInt)
          }
      elaborating [] (arrow (TypeVariant (at 9) [ VariantTag (at 9) (Tag "Ok") int, VariantLabel (at 10) (Symbol "err") int ]) int) \r ->
        r.scheme `shouldEqual` Right
          { kindVars: []
          , body: pureFn (Core.TApp (Core.TCon variantTy []) (Core.TRowExtend (Core.RowTypeEntry (TagKey (Tag "Ok")) coreInt) (Core.TRowExtend (Core.RowTypeEntry (SymbolKey (Symbol "err")) coreInt) Core.TRowEmpty))) coreInt
          }

    it "of effects is the row an arrow carries, each effect applied at the kinds of its parameters" do
      let
        row = TypeEffectRow (at 9) [ EffectElement (console 9), EffectInstance (at 10) (Symbol "cache") (state 10 [ int ]) ]
      elaborating [] (TypeFunction (at 4) int int (Just row)) \r ->
        r.scheme `shouldEqual` Right
          { kindVars: []
          , body: fn coreInt (Core.TRowExtend (Core.RowEffectEntry consoleName []) (Core.TRowExtend (Core.RowLabelledEffectEntry (Symbol "cache") stateName [ coreInt ]) Core.TRowEmpty)) coreInt
          }
      -- a variable standing for the row is one at `Row Effect`
      elaborating [ rowVar ] (TypeFunction (at 4) int int (Just (v rowVar))) \r ->
        r.scheme `shouldEqual` Right { kindVars: [], body: Core.TForall (TyVar "e") (Core.KRow RowEffect) (fn coreInt (Core.TVar (TyVar "e")) coreInt) }

    it "refuses an effect applied to more or to fewer arguments than it has parameters" do
      elaborating [] (TypeFunction (at 4) int int (Just (TypeEffectRow (at 9) [ EffectElement (state 9 []) ]))) \r -> case r.outcome of
        Failed (EquationFailed (AtSource o) _) -> o.origin `shouldEqual` at 9
        _ -> fail "not refused"
      elaborating [] (TypeFunction (at 4) int int (Just (TypeEffectRow (at 9) [ EffectElement (console 9) { arguments = [ int ] } ]))) \r -> case r.outcome of
        Failed (EquationFailed (AtSource o) _) -> o.origin `shouldEqual` at 3
        _ -> fail "not refused"

  describe "a type shown to an author" do
    it "is written as source writes it: an arrow with its row, a record, a tuple, a variant, and an effect row" do
      let
        x = XCon intTy []
        row entries = Array.foldr XRowExtend XRowEmpty entries
        effects = row [ XRowEffectEntry consoleName [], XRowLabelledEffectEntry (Symbol "cache") stateName [ x ] ]
      printType (xFunction x effects (xFunction x XRowEmpty x)) `shouldEqual` "Int -> (Int -> Int) / {| Console, cache :: State Int |}"
      printType (xFunction x (XVar (TyVar "e")) x) `shouldEqual` "Int -> Int / e"
      printType (XApp (XCon recordTy []) (XRowExtend (XRowTypeEntry (SymbolKey (Symbol "name")) x) (XVar (TyVar "r")))) `shouldEqual` "{ name :: Int, ...r }"
      printType (XApp (XCon recordTy []) (row [ XRowTypeEntry (PositionKey 0) x, XRowTypeEntry (PositionKey 1) x ])) `shouldEqual` "(Int, Int)"
      printType (XApp (XCon variantTy []) (row [ XRowTypeEntry (TagKey (Tag "Ok")) x, XRowTypeEntry (SymbolKey (Symbol "err")) x ])) `shouldEqual` "[ 'Ok :: Int, err :: Int ]"
      printType (XApp (XCon recordTy []) XRowEmpty) `shouldEqual` "{}"

  describe "a type operator" do
    it "naming a type constructor is that constructor applied to its two operands" do
      elaborating [ a ] (arrow (TypeOperator (at 12) { origin: at 13, target: TargetTypeConstructor pairName } int (v a)) int) \r ->
        r.scheme `shouldEqual` Right
          { kindVars: [], body: Core.TForall (TyVar "a") Core.KType (pureFn (Core.TApp (Core.TApp (Core.TCon pairName []) coreInt) (Core.TVar (TyVar "a"))) coreInt) }

    it "naming an effect is no type, and one naming a synonym is not read yet" do
      elaborating [] (arrow (TypeOperator (at 12) { origin: at 13, target: TargetEffect stateName } int int) (TypeOperator (at 14) { origin: at 15, target: TargetTypeSynonym (Qualified lib (TyName "S")) } int int)) \r -> case r.outcome of
        Done done -> done.unsupported `shouldEqual` [ EffectAsType (at 13) stateName, OutsideSubset (at 15) "a type synonym" ]
        _ -> fail "not elaborated"
