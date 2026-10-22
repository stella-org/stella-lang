-- | The global names a Core term refers to, and the modules a module's terms
-- | depend on when it runs.
-- |
-- | What the cases of `globalsOf` are for is that **`Global` is the whole of
-- | it**: names a term carries for another purpose — the constructor a dispatch
-- | selects, the effect a handler removes — are no reference to a value
-- | declaration. A module a dispatch selects a constructor of is one the terms
-- | depend on when they run.
module Test.Stella.Compiler.TypedCore.Reference (spec) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (DecisionTree(..), EffName(..), Expr(..), Ident(..), Literal(..), ModuleName(..), OpClause(..), OpName(..), Occurrence(..), Qualified(..), RegionName(..), RowEntry(..), RowKey(..), Symbol(..), TyName(..), Type(..), globalsOf)
import Stella.Compiler.TypedCore.Reference (runtimeDependencies)
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
    globalsOf (Handle 0 (Var 0 (Ident "e")) handler)
      `shouldEqual` Set.fromFoldable [ global "g", global "h" ]

  it "names the globals of a region's initial values and its body" do
    globalsOf (Region 0 (RegionName "r") [ { key: SymbolKey (Symbol "n"), ty: unitTy } ] [ Global 0 (global "i") [] ] (WriteCell 0 (RegionName "r") (SymbolKey (Symbol "n")) (Global 0 (global "b") [])))
      `shouldEqual` Set.fromFoldable [ global "i", global "b" ]

  it "depends at run time on the modules of the globals and of the constructors dispatched on, the module itself and Prim aside, in the order of their names' scalar values" do
    let
      -- `U+E000` stands below an astral character by scalar value, and above it
      -- by UTF-16 code unit
      inModule m x = Qualified (ModuleName m) (Ident x)
      term =
        Case 0 [ Global 0 (inModule "M\x1F600" "xs") [] ]
          ( SwitchCtor (OccScrutinee 0)
              [ { ctor: inModule "Lists" "Nil", tree: Leaf (Global 0 (global "f") []) }
              , { ctor: inModule "Prim" "Unit", tree: Leaf (Global 0 (inModule "M\xE000" "y") []) }
              ]
              Nothing
          )
    runtimeDependencies main' [ term ] `shouldEqual` map ModuleName [ "Lists", "M\xE000", "M\x1F600" ]
