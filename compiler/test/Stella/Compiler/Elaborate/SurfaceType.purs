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
import Stella.Compiler.Elaborate.Surface.Type (Elaborated, Unsupported(..), elaborateSignature, settledScheme)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Surface.Name (BindingId(..), TypeVar(..))
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.Surface.Type (Kind(..), Type(..))
import Stella.Compiler.TypedCore (Decl(..), Module, declare, primSignature)
import Stella.Compiler.TypedCore.Kind (Kind(..)) as Core
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Name (Ident(..), KindVar(..), ModuleName(..), Qualified(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (intTy, pureFn)
import Stella.Compiler.TypedCore.Type (Type(..), TypeScheme) as Core
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

lib :: ModuleName
lib = ModuleName "Lib"

-- | `data Box a = Box a`, and `data Phantom = Phantom` at `forall k. Type`.
libCore :: Module Unit
libCore =
  { annotation: unit
  , name: lib
  , imports: []
  , exports: []
  , decls:
      [ DeclData unit { name: TyName "Box", kindVars: [], params: [ { name: TyVar "a", kind: Core.KType } ], constructors: [ { name: Ident "Box", tag: 0, fields: [ Core.TVar (TyVar "a") ] } ], isNewtype: false, attributes: [] }
      , DeclData unit { name: TyName "Phantom", kindVars: [ KindVar "k" ], params: [], constructors: [ { name: Ident "Phantom", tag: 0, fields: [] } ], isNewtype: false, attributes: [] }
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
      elaborating [ a ] (arrow (TypeRecord (at 9) []) (TypeSynonym (at 10) (Qualified lib (TyName "S")))) \r -> case r.outcome of
        Done e -> e.unsupported `shouldEqual` [ OutsideSubset (at 9) "a record type", OutsideSubset (at 10) "a type synonym" ]
        _ -> fail "not elaborated"
