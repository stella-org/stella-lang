-- | The module catalog a compile-time session resolves names against.
-- |
-- | What these cases are for is that **what a search reads does not depend on
-- | the order it was assembled in**: imported and local entries are found alike,
-- | and the names carrying an attribute come back in one order.
module Test.Stella.Compiler.Elaborate.Catalog (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Environment.Catalog (CatalogEntry, EntrySort(..), catalogOf, lookupEntry, namesWithAttr)
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..))
import Stella.Compiler.TypedCore (AttrValue(..), Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

xInt :: XType
xInt = XCon (Qualified (ModuleName "Prim") (TyName "Int")) []

entry :: P.String -> P.String -> P.Array P.String -> CatalogEntry
entry moduleName name keys =
  { name: Qualified (ModuleName moduleName) (Ident name)
  , sort: ValueEntry
  , scheme: { kindVars: [], body: xInt }
  , attributes: map (\key -> { key, value: AttrUnit }) keys
  }

-- | An instance imported from another module, one declared here, and a value
-- | carrying no attribute.
entries :: P.Array CatalogEntry
entries =
  [ entry "Main" "showMine" [ "typeclass.instance" ]
  , entry "Data.Show" "showInt" [ "typeclass.instance" ]
  , entry "Main" "helper" []
  ]

spec :: Spec Unit
spec = describe "Elaborate.Catalog" do
  it "finds an imported entry and a local one alike" do
    map _.name (lookupEntry (catalogOf entries) (Qualified (ModuleName "Data.Show") (Ident "showInt")))
      `shouldEqual` Just (Qualified (ModuleName "Data.Show") (Ident "showInt"))
    map _.name (lookupEntry (catalogOf entries) (Qualified (ModuleName "Main") (Ident "helper")))
      `shouldEqual` Just (Qualified (ModuleName "Main") (Ident "helper"))
    lookupEntry (catalogOf entries) (Qualified (ModuleName "Main") (Ident "absent")) `shouldEqual` Nothing

  it "lists the names carrying an attribute in one order, whatever order they were given in" do
    let
      expected =
        [ Qualified (ModuleName "Data.Show") (Ident "showInt")
        , Qualified (ModuleName "Main") (Ident "showMine")
        ]
    namesWithAttr (catalogOf entries) "typeclass.instance" `shouldEqual` expected
    namesWithAttr (catalogOf (Array.reverse entries)) "typeclass.instance" `shouldEqual` expected
