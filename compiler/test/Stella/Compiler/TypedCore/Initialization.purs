-- | Whether a recursive group is initialization-safe, and where what it reads
-- | too early is seen.
-- |
-- | Each term is annotated with a label, so a violation names the reference it
-- | is located at and the form that promoted it by theirs.
module Test.Stella.Compiler.TypedCore.Initialization (spec) where

import Prelude

import Prim as P

import Data.Map as Map
import Data.Maybe (Maybe(..))
import Stella.Compiler.TypedCore.Initialization (localViolations, topLevelViolations)
import Stella.Compiler.TypedCore.Kind (monoScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), JoinName(..), ModuleName(..), Qualified(..), RegionName(..), Symbol(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (pureFn)
import Stella.Compiler.TypedCore.Signature (Signature, emptySignature)
import Stella.Compiler.TypedCore.Term (DecisionTree(..), Expr(..), Literal(..), Occurrence(..))
import Stella.Compiler.TypedCore.Type (RowEntry(..), RowKey(..), Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

main' :: ModuleName
main' = ModuleName "Main"

global :: P.String -> Qualified Ident
global name = Qualified main' (Ident name)

unitTy :: Type
unitTy = TCon (Qualified (ModuleName "Prim") (TyName "Unit")) []

-- | `Pair` of two fields, and `store`, a foreign of one argument.
sig :: Signature
sig = emptySignature
  { ctors = Map.singleton (global "Pair")
      { owner: Qualified main' (TyName "P"), tag: 0, params: [], fields: [ unitTy, unitTy ], scheme: monoScheme unitTy }
  , values = Map.singleton (global "store") { scheme: monoScheme (pureFn unitTy unitTy), isForeign: true }
  }

ref :: P.String -> P.String -> Expr P.String
ref label name = Global label (global name) []

var :: P.String -> P.String -> Expr P.String
var label name = Var label (Ident name)

lam :: P.String -> Expr P.String -> Expr P.String
lam x body = Lam "λ" (Ident x) unitTy body

lit :: Expr P.String
lit = Lit "lit" (LitInt 0)

app :: P.String -> Expr P.String -> Expr P.String -> Expr P.String
app = App

pair :: Expr P.String -> Expr P.String -> Expr P.String
pair a b = App "pair" (App "pair'" (Global "Pair" (global "Pair") []) a) b

-- | The violations of a top-level group, as the right-hand side and the member
-- | read by position, and the labels of the reference and of what promoted it.
judged :: P.Array { name :: P.String, value :: Expr P.String } -> P.Array { initializer :: P.Int, read :: P.Int, at :: P.String, through :: Maybe P.String }
judged members = topLevelViolations sig (map (\m -> { name: global m.name, value: m.value }) members)

judgedLocally :: P.Array { name :: P.String, value :: Expr P.String } -> P.Array { initializer :: P.Int, read :: P.Int, at :: P.String, through :: Maybe P.String }
judgedLocally members = localViolations sig (map (\m -> { name: Ident m.name, value: m.value }) members)

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore.Initialization" do
  describe "a group" do
    it "admits a member read only under a λ, and a group of functions" do
      judged [ { name: "fibAnd", value: pair lit (lam "n" (app "call" (ref "r" "fibAnd") (var "n" "n"))) } ] `shouldEqual` []
      judged [ { name: "f", value: lam "x" (ref "rg" "g") }, { name: "g", value: lam "x" (ref "rf" "f") } ] `shouldEqual` []

    it "refuses a member reading itself, and one reading a member written after it" do
      judged [ { name: "x", value: ref "r" "x" } ] `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Nothing } ]
      judged [ { name: "xs", value: pair lit (ref "ys" "ys") }, { name: "ys", value: pair lit (ref "xs" "xs") } ]
        `shouldEqual` [ { initializer: 0, read: 1, at: "ys", through: Nothing } ]

    it "reports a read reached through what a member calls, as its summary reaches it" do
      -- `a = g 1; g x = c x; c y = a + y`
      judged
        [ { name: "a", value: app "call" (ref "rg" "g") lit }
        , { name: "g", value: lam "x" (app "inner" (ref "rc" "c") (var "x" "x")) }
        , { name: "c", value: lam "y" (ref "ra" "a") }
        ]
        `shouldEqual`
          [ { initializer: 0, read: 0, at: "ra", through: Just "call" }
          , { initializer: 0, read: 1, at: "rg", through: Nothing }
          , { initializer: 0, read: 2, at: "rc", through: Just "call" }
          ]

  describe "an application" do
    it "promotes what its callee and its argument may read later" do
      judged [ { name: "x", value: app "app" (lam "u" (ref "r" "x")) lit } ] `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Just "app" } ]

    it "of a constructor or a foreign no deeper than its arity promotes nothing, and one beyond it does" do
      judged [ { name: "x", value: app "store" (ref "s" "store") (lam "u" (ref "r" "x")) } ] `shouldEqual` []
      judged [ { name: "x", value: app "over" (app "store" (ref "s" "store") (lam "u" (ref "r" "x"))) lit } ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Just "over" } ]

    it "of a closure taken out of an earlier member's value promotes what it reads" do
      judged
        [ { name: "a", value: RecordExtend "record" (SymbolKey (Symbol "next")) (lam "u" (ref "rb" "b")) (RecordEmpty "empty") }
        , { name: "b", value: app "call" (RecordSelect "select" (SymbolKey (Symbol "next")) (ref "ra" "a")) lit }
        ]
        `shouldEqual` [ { initializer: 1, read: 1, at: "rb", through: Just "call" } ]

  describe "a binder" do
    it "gives a `let`'s variable, and a pattern's, what the value bound may read later" do
      judged [ { name: "x", value: Let "let" (Ident "y") unitTy (lam "u" (ref "r" "x")) (app "app" (var "y" "y") lit) } ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Just "app" } ]
      judged
        [ { name: "x"
          , value: Case "case" [ pair lit (lam "u" (ref "r" "x")) ]
              (Bind (Ident "y") (OccField (OccScrutinee 0) (global "Pair") 1) (Leaf (app "app" (var "y" "y") lit)))
          }
        ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Just "app" } ]

    it "shadows a member of a local group it binds the name of" do
      judgedLocally [ { name: "x", value: var "r" "x" } ] `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Nothing } ]
      judgedLocally [ { name: "x", value: Let "let" (Ident "x") unitTy lit (var "r" "x") } ] `shouldEqual` []
      judgedLocally [ { name: "x", value: app "app" (Lam "λ" (Ident "x") unitTy (var "r" "x")) lit } ] `shouldEqual` []

  describe "a decision tree" do
    it "reads its guard" do
      judged [ { name: "x", value: Case "case" [ lit ] (Guard (ref "r" "x") (Leaf lit) (Leaf lit)) } ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Nothing } ]

  describe "a join point" do
    it "is read where it is jumped to, under what every jump hands it" do
      let j = JoinName "j"
      judged [ { name: "x", value: LetJoin "join" j [] unitTy (ref "r" "x") lit } ] `shouldEqual` []
      judged [ { name: "x", value: LetJoin "join" j [] unitTy (ref "r" "x") (Jump "jump" j []) } ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Nothing } ]
      judged
        [ { name: "x"
          , value: LetJoin "join" j [ { name: Ident "p", ty: unitTy } ] unitTy (app "app" (var "p" "p") lit) (Jump "jump" j [ lam "u" (ref "r" "x") ])
          }
        ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Just "app" } ]

    it "jumping to itself is part of the same fixed point" do
      let j = JoinName "j"
      judged
        [ { name: "x"
          , value: LetJoin "join" j [ { name: Ident "p", ty: unitTy } ] unitTy
              (Case "case" [ lit ] (Guard lit (Leaf (app "app" (var "p" "p") lit)) (Leaf (Jump "again" j [ lam "u" (ref "r" "x") ]))))
              (Jump "jump" j [ lit ])
          }
        ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Just "app" } ]

  describe "a handling expression and a region" do
    it "keep what a part reads as it stands, and count everything else they hold as read through them" do
      judged [ { name: "x", value: Region "region" (RegionName "l") [] [] (ref "r" "x") } ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Nothing } ]
      judged [ { name: "x", value: Region "region" (RegionName "l") [] [] (Let "let" (Ident "y") unitTy (lam "u" (ref "r" "x")) (app "app" (var "y" "y") lit)) } ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Just "region" } ]

    it "count everything they hold as read" do
      judged [ { name: "x", value: Region "region" (RegionName "l") [] [] (Let "let" (Ident "y") unitTy (lam "u" (ref "r" "x")) lit) } ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Just "region" } ]
      judged
        [ { name: "x"
          , value: Handle "handle" (Let "let" (Ident "y") unitTy (lam "u" (ref "r" "x")) lit)
              { element: RowEffectEntry (Qualified main' (EffName "E")) []
              , returnClause: { binder: Ident "v", ty: unitTy, body: var "v" "v" }
              , opClauses: []
              }
          }
        ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "r", through: Just "handle" } ]

  describe "a nested group" do
    it "reports to the group around it only what it reads of that group" do
      let
        nested = LetRec "letrec" [ { name: Ident "y", ty: unitTy, value: pair lit (lam "u" (ref "ra" "a")) } ] (var "y" "y")
        reading = LetRec "letrec" [ { name: Ident "y", ty: unitTy, value: ref "ra" "a" } ] (var "y" "y")
      judged [ { name: "a", value: nested } ] `shouldEqual` []
      judged [ { name: "a", value: reading } ] `shouldEqual` [ { initializer: 0, read: 0, at: "ra", through: Nothing } ]

    it "is judged in its own order, apart from the group around it" do
      let
        inner = [ { name: "y", value: var "rz" "z" }, { name: "z", value: lit } ]
        outer = LetRec "letrec" (map (\m -> { name: Ident m.name, ty: unitTy, value: m.value }) inner) (var "y" "y")
      judgedLocally inner `shouldEqual` [ { initializer: 0, read: 1, at: "rz", through: Nothing } ]
      judged [ { name: "a", value: outer } ] `shouldEqual` []

  describe "a witness" do
    it "is the first reference in the group, a read as it stands before a promoted one" do
      judged [ { name: "x", value: pair (ref "first" "x") (ref "second" "x") } ] `shouldEqual` [ { initializer: 0, read: 0, at: "first", through: Nothing } ]
      judged [ { name: "x", value: pair (app "app" (lam "u" (ref "inner" "x")) lit) (ref "direct" "x") } ]
        `shouldEqual` [ { initializer: 0, read: 0, at: "inner", through: Just "app" } ]
