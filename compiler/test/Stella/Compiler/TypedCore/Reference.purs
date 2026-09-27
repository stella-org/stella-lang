-- | The global names a Core term refers to.
-- |
-- | What these cases are for is that **`Global` is the whole of it**: names a
-- | term carries for another purpose — the constructor a dispatch selects, the
-- | effect a handler removes — are no reference to a value declaration.
module Test.Stella.Compiler.TypedCore.Reference (spec) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (DecisionTree(..), EffName(..), Expr(..), Ident(..), Literal(..), ModuleName(..), OpClause(..), OpName(..), Occurrence(..), Qualified(..), RowEntry(..), TyName(..), Type(..), globalsOf)
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

main' :: ModuleName
main' = ModuleName "Main"

global :: P.String -> Qualified Ident
global name = Qualified main' (Ident name)

unitTy :: Type
unitTy = TCon (Qualified (ModuleName "Prim") (TyName "Unit")) []

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore.Reference" do
  it "names the globals of a dispatch's branches and not the constructors dispatched on" do
    let
      term =
        Case 0 [ Var 0 (Ident "xs") ]
          ( SwitchCtor (OccScrutinee 0)
              [ { ctor: global "Nil", tree: Leaf (Global 0 (global "f") []) }
              , { ctor: global "Cons", tree: Leaf (Lit 0 (LitInt 0)) }
              ]
              Nothing
          )
    globalsOf term `shouldEqual` Set.singleton (global "f")

  it "names the globals of a handler's clauses and not the effect it handles" do
    let
      handler =
        { element: RowEffectEntry (Qualified main' (EffName "Counter")) []
        , cells: Nothing
        , returnClause: { binder: Ident "x", ty: unitTy, body: Global 0 (global "g") [] }
        , opClauses:
            [ FastClause
                { op: OpName "next"
                , tyBinders: []
                , argBinder: { name: Ident "u", ty: unitTy }
                , body: App 0 (Global 0 (global "h") []) (Var 0 (Ident "u"))
                }
            ]
        }
    globalsOf (Handle 0 (Var 0 (Ident "e")) handler [])
      `shouldEqual` Set.fromFoldable [ global "g", global "h" ]
