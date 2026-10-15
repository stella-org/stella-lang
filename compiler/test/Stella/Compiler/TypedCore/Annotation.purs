-- | The types checking records on the term it accepts.
-- |
-- | Checking already computes a type for every node and the `Ω` every dispatch
-- | is checked under. What these cases pin down is that both reach the term that
-- | comes back, so that a later stage reads them rather than deriving them
-- | again: a second, independent inference is a different judgement, checking
-- | using an expected type where inference has none.
module Test.Stella.Compiler.TypedCore.Annotation (spec) where

import Prelude

import Prim as P

-- Everything the annotation API offers is reached through the facade, which is
-- what a later stage imports. A member missing from its re-export list fails
-- this module rather than going unnoticed.
import Stella.Compiler.TypedCore (CheckedGroup, DecisionTree(..), Expr(..), Ident(..), Literal(..), ModuleName(..), Occurrence(..), Qualified(..), RowEntry(..), RowKey(..), Symbol(..), TyName(..), Type(..), Typed, check, declare, declareAnnotated, emptyContext, envOf, exprAnnotation, infer, intTy, primSignature, pureFn, stringTy, typeOf, withAnnotation)
import Stella.Compiler.TypedCore.Context (bindVar)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Test.Stella.Compiler.TypedCore.VerticalSlice (intModule, verticalSlice)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

int :: Type
int = TCon intTy []

string :: Type
string = TCon stringTy []

listOf :: Type -> Type
listOf a = TApp (TCon (Qualified mainModuleName (TyName "List")) []) a

cons :: Qualified Ident
cons = Qualified mainModuleName (Ident "Cons")

nameKey :: RowKey
nameKey = SymbolKey (Symbol "name")

record :: Type -> Type
record row = TApp (TCon (Qualified (ModuleName "Prim") (TyName "Record")) []) row

-- | The vertical slice, checked. Its `sum` is the term the Translation document
-- | works through.
groups :: Either P.String (P.Array (CheckedGroup P.Int))
groups = case declare primSignature intModule of
  Left _ -> Left "Base.Int did not declare"
  Right s1 -> case declareAnnotated s1 verticalSlice of
    Left _ -> Left "the slice did not declare"
    Right declared -> Right declared.values

-- | The right-hand side of a top-level value, by name.
valueOf :: P.String -> Either P.String (Expr (Typed P.Int))
valueOf name = do
  gs <- groups
  case Array.find (\b -> b.name == Ident name) (Array.concatMap _.bindings gs) of
    Just binding -> Right binding.value
    Nothing -> Left ("no binding named " <> name)

-- | The `Case` inside `λ (xs : List Int). case (xs) of dt`.
sumCase :: Either P.String (Expr (Typed P.Int))
sumCase = do
  value <- valueOf "sum"
  case value of
    Lam _ _ _ _ body -> Right body
    _ -> Left "sum is not a lambda"

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore.Check » what checking records" do

  describe "the type of a node" do

    it "is the scheme's own type at the root of a declaration" do
      -- checked against the scheme, so the root carries what checking was asked
      -- for rather than a type re-derived from the lambda
      map typeOf (valueOf "sum") `shouldEqual` Right (pureFn (listOf int) int)

    it "is the result of a dispatch at the `case` it stands in" do
      map typeOf sumCase `shouldEqual` Right int

    it "reaches nodes beneath the root" do
      let
        leafType = do
          body <- sumCase
          case body of
            Case _ scrutinees _ -> case Array.head scrutinees of
              Just scrutinee -> Right (typeOf scrutinee)
              Nothing -> Left "no scrutinee"
            _ -> Left "not a case"
      leafType `shouldEqual` Right (listOf int)

    it "is the expected type where checking delegates to inference" do
      -- a literal synthesizes its own type, and the node still records the one
      -- checking was given, the two being equal
      let checked = check (envOf primSignature emptyContext) TRowEmpty int (Lit unit (LitInt 1))
      map typeOf checked `shouldEqual` Right int

    it "is the synthesized type under inference" do
      let inferred = infer (envOf primSignature emptyContext) TRowEmpty (Lit unit (LitInt 1))
      map typeOf inferred `shouldEqual` Right int

    it "is replaced at the root alone by `withAnnotation`" do
      -- the dual of `exprAnnotation`, where `map` would reach every node
      let
        term = Lam unit (Ident "x") int TRowEmpty (Var unit (Ident "x"))
        result = case infer (envOf primSignature emptyContext) TRowEmpty term of
          Left _ -> Left "did not check"
          Right checked -> case withAnnotation ((exprAnnotation checked) { ty = string }) checked of
            Lam ann _ _ _ body -> Right (Tuple ann.ty (typeOf body))
            _ -> Left "not a lambda"
      result `shouldEqual` Right (Tuple string int)

  describe "the occurrences a decision tree projects" do

    it "holds the scrutinee and the fields each branch takes apart" do
      map occurrencesOf sumCase `shouldEqual` Right
        ( Map.fromFoldable
            [ Tuple (OccScrutinee 0) (listOf int)
            , Tuple (OccField (OccScrutinee 0) cons 0) int
            , Tuple (OccField (OccScrutinee 0) cons 1) (listOf int)
            ]
        )

    it "holds a record field, which no dispatch establishes" do
      -- `o . k` reaches Ω by being resolved rather than by a branch, a record
      -- having an element at every key of its row
      let
        row = TRowExtend (RowTypeEntry nameKey string) TRowEmpty
        env = envOf primSignature (bindVar emptyContext (Ident "r") (record row))
        term =
          Case unit [ Var unit (Ident "r") ]
            (Bind (Ident "n") (OccRecordField (OccScrutinee 0) nameKey) (Leaf (Var unit (Ident "n"))))
      map occurrencesOf (infer env TRowEmpty term) `shouldEqual` Right
        ( Map.fromFoldable
            [ Tuple (OccScrutinee 0) (record row)
            , Tuple (OccRecordField (OccScrutinee 0) nameKey) string
            ]
        )

    it "is empty at a node that is not a `case`" do
      let inferred = infer (envOf primSignature emptyContext) TRowEmpty (Lit unit (LitInt 1))
      map occurrencesOf inferred `shouldEqual` Right Map.empty

  describe "the value declarations" do

    it "come back in declaration order, each saying whether it recurses" do
      map (map (\g -> Tuple g.recursive (map _.name g.bindings))) groups `shouldEqual` Right
        [ Tuple true [ Ident "sum" ]
        , Tuple false [ Ident "result" ]
        ]

occurrencesOf :: forall a. Expr (Typed a) -> Map Occurrence Type
occurrencesOf = _.occurrences <<< exprAnnotation
