-- | A module's values grouped by what they refer to, in a stable dependency
-- | order.
module Test.Stella.Compiler.Elaborate.Group (spec) where

import Prelude

import Data.Set as Set
import Stella.Compiler.Elaborate.Surface.Group (groups)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: Spec Unit
spec = describe "Stella.Compiler.Elaborate.Surface.Group" do
  it "puts a group after what it refers to, and otherwise the one holding the first ordinal first" do
    groups [ Set.singleton 1, Set.empty, Set.empty ] `shouldEqual`
      [ { members: [ 1 ], recursive: false }, { members: [ 0 ], recursive: false }, { members: [ 2 ], recursive: false } ]
    groups [ Set.empty, Set.singleton 0 ] `shouldEqual`
      [ { members: [ 0 ], recursive: false }, { members: [ 1 ], recursive: false } ]

  it "groups a cycle as one recursive group, its members in order" do
    groups [ Set.singleton 2, Set.empty, Set.singleton 0 ] `shouldEqual`
      [ { members: [ 0, 2 ], recursive: true }, { members: [ 1 ], recursive: false } ]
    groups [ Set.empty, Set.fromFoldable [ 1, 2 ], Set.singleton 1 ] `shouldEqual`
      [ { members: [ 0 ], recursive: false }, { members: [ 1, 2 ], recursive: true } ]

  it "takes a node referring to itself for a recursive group" do
    groups [ Set.singleton 0 ] `shouldEqual` [ { members: [ 0 ], recursive: true } ]

  it "makes no group of no node" do
    groups [] `shouldEqual` []

  it "ignores a reference to no node" do
    groups [ Set.singleton 5 ] `shouldEqual` [ { members: [ 0 ], recursive: false } ]
