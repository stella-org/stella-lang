-- | The AST is exercised by building the worked examples of the specification.
-- | Whether they can be written at all is what this checks; their well-typedness
-- | is the Core type checker's business.
module Test.Stella.Compiler.TypedCore (spec) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore (Constraint(..), Decl(..), DecisionTree(..), EffName(..), EffectDecl, Expr(..), Ident(..), Kind(..), ModuleName(..), OpClause(..), OpName(..), Qualified(..), RowElemKind(..), RowEntry(..), RowKey(..), RowPayload(..), Symbol(..), Tag(..), TyName(..), TyVar(..), Type(..), declAnnotation, exprAnnotation, opClauseBody, rowEntryKey, rowEntryPayload)
import Data.Array (index)
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Stella.Compiler.TypedCore.VerticalSlice (verticalSlice)
import Test.Spec.Assertions (shouldEqual)

-- Names used by the examples.

prim :: ModuleName
prim = ModuleName "Prim"

example :: ModuleName
example = ModuleName "Example"

tInt :: Type
tInt = TCon (Qualified prim (TyName "Int")) []

tUnit :: Type
tUnit = TCon (Qualified prim (TyName "Unit")) []

-- | `τ1 -{ρ}-> τ2`, that is, `Prim.Function τ1 ρ τ2`. Core has no arrow syntax.
fn :: Type -> Type -> Type -> Type
fn arg row result =
  TApp (TApp (TApp (TCon (Qualified prim (TyName "Function")) []) arg) row) result

-- | The `Partial` handler of the Examples document, annotated with the line each
-- | node stands on, so that a traversal over annotations is observable.
toMaybe :: Expr P.Int
toMaybe =
  TyLam 1 (TyVar "e") (KRow RowEffect)
    $ ConstraintLam 2 (Lacks (EffectKey partialEff) (TVar (TyVar "e")))
    $ TyLam 3 (TyVar "a") KType
    $ Lam 4 (Ident "thunk") thunkTy
    $
      Handle 5 (App 6 (Var 7 (Ident "thunk")) (Global 8 primUnit []))
        { element: RowEffectEntry partialEff []
        , cells: Nothing
        , returnClause:
            { binder: Ident "x"
            , ty: TVar (TyVar "a")
            , body: App 9 (TyApp 10 (Global 11 just []) (TVar (TyVar "a"))) (Var 12 (Ident "x"))
            }
        , opClauses:
            [ FullClause
                { op: OpName "abort"
                , tyBinders: [ { name: TyVar "b", kind: KType } ]
                , argBinder: { name: Ident "_", ty: tUnit }
                , contBinder:
                    { name: Ident "k"
                    , ty: fn (TVar (TyVar "b")) (TVar (TyVar "e")) (maybeOf (TVar (TyVar "a")))
                    }
                , body: TyApp 13 (Global 14 nothing []) (TVar (TyVar "a"))
                }
            ]
        }
        []
  where
  thunkTy =
    fn tUnit (TRowExtend (RowEffectEntry partialEff []) (TVar (TyVar "e"))) (TVar (TyVar "a"))

partialEff :: Qualified EffName
partialEff = Qualified prim (EffName "Partial")

stateEff :: Qualified EffName
stateEff = Qualified prim (EffName "State")

primUnit :: Qualified Ident
primUnit = Qualified prim (Ident "Unit")

just :: Qualified Ident
just = Qualified example (Ident "Just")

nothing :: Qualified Ident
nothing = Qualified example (Ident "Nothing")

maybeOf :: Type -> Type
maybeOf a = TApp (TCon (Qualified example (TyName "Maybe")) []) a

-- | `effect State s where get : Unit ->* s ; put : s ->* Unit`, which binds no
-- | kind variable, as no effect constructor does.
stateEffect :: EffectDecl
stateEffect =
  { name: EffName "State"
  , params: [ { name: TyVar "s", kind: KType } ]
  , operations:
      [ { name: OpName "get", tyBinders: [], argument: tUnit, resumesWith: TVar (TyVar "s") }
      , { name: OpName "put", tyBinders: [], argument: TVar (TyVar "s"), resumesWith: tUnit }
      ]
  , attributes: []
  }

-- | The annotation of an operation clause's body, reached through the handler
-- | record rather than through a constructor field.
clauseBodyAnnotation :: forall a. Expr a -> Maybe a
clauseBodyAnnotation = case _ of
  Handle _ _ h _ -> map (exprAnnotation <<< opClauseBody) (index h.opClauses 0)
  _ -> Nothing

handlerOf :: forall a. Expr a -> Maybe (Expr a)
handlerOf = case _ of
  TyLam _ _ _ e -> handlerOf e
  ConstraintLam _ _ e -> handlerOf e
  Lam _ _ _ e -> handlerOf e
  e@(Handle _ _ _ _) -> Just e
  _ -> Nothing

spec :: Spec Unit
spec = describe "Stella.Compiler.TypedCore" do
  describe "the vertical slice" do
    it "is a module of three declarations" do
      map declKind verticalSlice.decls `shouldEqual` [ "data", "rec", "nonrec" ]

    it "dispatches on the tag and binds the fields in the decision tree" do
      case verticalSlice.decls `index` 1 of
        Just (DeclRec _ [ binding ]) ->
          treeShape binding.value `shouldEqual`
            Just [ "switchCtor Main.Nil", "switchCtor Main.Cons" ]
        _ -> "expected a rec group of one binding" `shouldEqual` "…"

    it "exhausts the constructors, so no default branch is present" do
      case verticalSlice.decls `index` 1 of
        Just (DeclRec _ [ binding ]) -> hasDefault binding.value `shouldEqual` Just false
        _ -> "expected a rec group of one binding" `shouldEqual` "…"

  describe "annotations" do
    it "are read off any expression node" do
      exprAnnotation toMaybe `shouldEqual` 1

    it "are carried by a declaration and by the module itself" do
      verticalSlice.annotation `shouldEqual` 0
      map declAnnotation verticalSlice.decls `shouldEqual` [ 1, 2, 3 ]

    it "are mapped inside a handler's clauses, which sit behind a record" do
      clauseBodyAnnotation (handlerOf' toMaybe) `shouldEqual` Just 13
      clauseBodyAnnotation (handlerOf' (void toMaybe)) `shouldEqual` Just unit

  describe "effect declarations" do
    it "give an operation an argument and a resumption type, not a function type" do
      map _.argument stateEffect.operations `shouldEqual` [ tUnit, TVar (TyVar "s") ]
      map _.resumesWith stateEffect.operations `shouldEqual` [ TVar (TyVar "s"), tUnit ]

  describe "row keys" do
    it "are written at Row Type, in any of the structural constructors" do
      rowEntryKey (RowTypeEntry (SymbolKey (Symbol "name")) tInt)
        `shouldEqual` SymbolKey (Symbol "name")
      rowEntryKey (RowTypeEntry (TagKey (Tag "Some")) tInt)
        `shouldEqual` TagKey (Tag "Some")
      rowEntryKey (RowTypeEntry (PositionKey 0) tInt)
        `shouldEqual` PositionKey 0

    it "come from the head constructor at Row Effect where none is written" do
      rowEntryKey (RowEffectEntry partialEff []) `shouldEqual` EffectKey partialEff

    it "come from the written Symbol where one is, which is what lets an effect repeat" do
      rowEntryKey (RowLabelledEffectEntry (Symbol "cache") stateEff [ tInt ])
        `shouldEqual` SymbolKey (Symbol "cache")

    it "leave the payload to name the protocol, whichever key stands over it" do
      -- A `perform` reads its operation's signature from the payload; the two
      -- elements below differ in key and agree in everything else
      rowEntryPayload (RowLabelledEffectEntry (Symbol "cache") stateEff [ tInt ])
        `shouldEqual` EffectPayload stateEff [ tInt ]
      rowEntryPayload (RowEffectEntry stateEff [ tInt ])
        `shouldEqual` EffectPayload stateEff [ tInt ]

-- Helpers that summarise a structure as something comparable.

handlerOf' :: forall a. Expr a -> Expr a
handlerOf' e = case handlerOf e of
  Just h -> h
  Nothing -> e

declKind :: forall a. Decl a -> P.String
declKind = case _ of
  DeclData _ _ -> "data"
  DeclEffect _ _ -> "effect"
  DeclForeign _ _ -> "foreign"
  DeclNonRec _ _ -> "nonrec"
  DeclRec _ _ -> "rec"
  DeclAttribute _ _ -> "attribute"

treeShape :: forall a. Expr a -> Maybe (P.Array P.String)
treeShape = case _ of
  Lam _ _ _ (Case _ _ (SwitchCtor _ branches _)) ->
    Just (map (\b -> "switchCtor " <> showQualified b.ctor) branches)
  _ -> Nothing

hasDefault :: forall a. Expr a -> Maybe P.Boolean
hasDefault = case _ of
  Lam _ _ _ (Case _ _ (SwitchCtor _ _ def)) ->
    Just case def of
      Just _ -> true
      Nothing -> false
  _ -> Nothing

showQualified :: Qualified Ident -> P.String
showQualified (Qualified (ModuleName m) (Ident n)) = m <> "." <> n
