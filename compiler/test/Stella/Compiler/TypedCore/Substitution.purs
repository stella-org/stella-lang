-- | Substituting types for type variables: all at once, a binder shadowing the
-- | variable it binds, and no binder capturing a variable of what is substituted.
module Test.Stella.Compiler.TypedCore.Substitution (spec) where

import Prelude
import Prim hiding (Type)

import Data.Either (Either(..))
import Data.Map as Map
import Data.Tuple (Tuple(..))
import Stella.Compiler.TypedCore (Constraint(..), Decl(..), Expr(..), Ident(..), Kind(..), Module, ModuleName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), Symbol(..), TyVar(..), Type(..), declare, monoScheme, primSignature, pureFn)
import Stella.Compiler.TypedCore.Type (substituteType)
import Stella.Compiler.TypedCore.Prim (intTy)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

a :: TyVar
a = TyVar "a"

b :: TyVar
b = TyVar "b"

r :: TyVar
r = TyVar "r"

int :: Type
int = TCon intTy []

-- | `( x : τ | ρ )`.
field :: Type -> Type -> Type
field t = TRowExtend (RowTypeEntry (SymbolKey (Symbol "x")) t)

main :: ModuleName
main = ModuleName "Main"

-- | `pair : forall a. forall b. a -> b -> a`, and a use of it at `[b, a]` inside
-- | a function quantifying `a` and `b` of its own: `pair [b] [a]` is
-- | `b -> a -> b`, which the use applies at its own `b` and `a`.
instantiating :: Module Int
instantiating =
  { annotation: 0
  , name: main
  , imports: []
  , exports: []
  , decls:
      [ DeclNonRec 1
          { name: Ident "pair"
          , scheme: monoScheme (TForall a KType (TForall b KType (pureFn (TVar a) (pureFn (TVar b) (TVar a)))))
          , value: TyLam 1 a KType (TyLam 1 b KType (Lam 1 (Ident "x") (TVar a) (Lam 1 (Ident "y") (TVar b) (Var 1 (Ident "x")))))
          , attributes: []
          }
      , DeclNonRec 2
          { name: Ident "flipped"
          , scheme: monoScheme (TForall a KType (TForall b KType (pureFn (TVar b) (pureFn (TVar a) (TVar b)))))
          , value: TyLam 2 a KType $ TyLam 2 b KType $ Lam 2 (Ident "y") (TVar b) $ Lam 2 (Ident "z") (TVar a) $
              App 2 (App 2 (TyApp 2 (TyApp 2 (Global 2 (Qualified main (Ident "pair")) []) (TVar b)) (TVar a)) (Var 2 (Ident "y"))) (Var 2 (Ident "z"))
          , attributes: []
          }
      ]
  }

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore.substituteType" do
  it "leaves a variable a binder shadows alone beneath it" do
    substituteType (Map.singleton a int) (TForall a KType (TVar a)) `shouldEqual` TForall a KType (TVar a)

  it "renames a binder that would capture a variable substituted in" do
    substituteType (Map.singleton a (TVar b)) (TForall b KType (pureFn (TVar a) (TVar b)))
      `shouldEqual` TForall (TyVar "b1") KType (pureFn (TVar b) (TVar (TyVar "b1")))

  it "renames a binder hiding one substitution and capturing another's value" do
    substituteType (Map.fromFoldable [ Tuple a (TVar b), Tuple b int ]) (TForall b KType (TVar a))
      `shouldEqual` TForall (TyVar "b1") KType (TVar b)

  it "substitutes all at once" do
    substituteType (Map.fromFoldable [ Tuple a (TVar b), Tuple b (TVar a) ]) (pureFn (TVar a) (TVar b))
      `shouldEqual` pureFn (TVar b) (TVar a)

  it "captures nothing inside a constraint, a row's entry, or a row's tail" do
    substituteType (Map.singleton a (TVar r))
      (TForall r (KRow RowType) (TConstrained (Lacks (SymbolKey (Symbol "x")) (TVar r)) (field (TVar a) (TVar r))))
      `shouldEqual`
        TForall (TyVar "r1") (KRow RowType)
          (TConstrained (Lacks (SymbolKey (Symbol "x")) (TVar (TyVar "r1"))) (field (TVar r) (TVar (TyVar "r1"))))

  it "lets a scheme be instantiated at the type variables of the term using it" do
    case declare primSignature instantiating of
      Right _ -> pure unit
      Left e -> fail (show e)
