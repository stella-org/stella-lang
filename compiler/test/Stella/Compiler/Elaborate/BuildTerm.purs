-- | The kernel's term builders, and what every one of them shares.
-- |
-- | Three things are what these cases are for. **A term is built in a build
-- | scope and used only where that scope is visible**, by the rule a type is
-- | held to. **A leaf is claimed at the one type it can have**, computed by the
-- | host and carried with the scope it was built in. And **a name a builder
-- | binds is fresh where it is bound**, not merely unlike what an author could
-- | write, and a rolled-back attempt gives back the names it drew.
module Test.Stella.Compiler.Elaborate.BuildTerm (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Build (openForall, rootScope)
import Stella.Compiler.Elaborate.BuildScope (usableTermIn)
import Stella.Compiler.Elaborate.BuildTerm (globalRef, literal, localVariable)
import Stella.Compiler.Elaborate.Constructors (emptyConstructorEnv)
import Stella.Compiler.Elaborate.Effects (emptyEffectEnv)
import Stella.Compiler.Elaborate.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Context (Origin(..), XContext, bindTyVar, bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Elab (Elab, Frame, Outcome(..), SessionEnv, SolverState, freshIdent, initialState, issue, resolveExpr, resolveScope, resolveType, runElabIn, raiseDiagnostic, transact, withFrame)
import Stella.Compiler.Elaborate.Handle (Handle, HandleObject(..), ScopeId(..), SessionId(..))
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (KindingEnv, KindingFault(..))
import Stella.Compiler.Elaborate.Observe (typeOf)
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Term (XExpr(..))
import Stella.Compiler.Elaborate.Type (XType(..))
import Stella.Compiler.Elaborate.Unify (UnifyError(..))
import Stella.Compiler.Elaborate.View (KindView(..))
import Stella.Compiler.TypedCore as Core
import Stella.Compiler.TypedCore (Ident(..), Kind(..), Literal(..), ModuleName(..), Qualified(..), TyName(..), TyVar(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..), fst)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

prim :: ModuleName
prim = ModuleName "Prim"

tyName :: P.String -> Qualified TyName
tyName name = Qualified prim (TyName name)

con :: P.String -> XType
con name = XCon (tyName name) []

xInt :: XType
xInt = con "Int"

listOf :: XType -> XType
listOf element = XApp (con "List") element

kinding :: KindingEnv
kinding =
  { types: Map.fromFoldable
      [ Tuple (tyName "Int") { kindVars: [], body: KType }
      , Tuple (tyName "Number") { kindVars: [], body: KType }
      , Tuple (tyName "Boolean") { kindVars: [], body: KType }
      , Tuple (tyName "List") { kindVars: [], body: KFun KType KType }
      ]
  , effects: Map.empty
  }

global :: P.String -> Qualified Ident
global name = Qualified (ModuleName "Main") (Ident name)

k :: Core.KindVar
k = Core.KindVar "k"

a :: TyVar
a = TyVar "a"

-- | One scheme polymorphic in a kind, and one mentioning a type variable it
-- | does not declare, which the site happens to bind.
session :: SessionEnv
session =
  { catalog: catalogOf
      [ entry "poly" [ k ] (XForall (TyVar "v") (XKVar k) xInt)
      , entry "free" [] (listOf (XVar a))
      ]
  , kinding
  , constructors: emptyConstructorEnv
  , effects: emptyEffectEnv
  }
  where
  entry name kindVars body = { name: global name, sort: ValueEntry, scheme: { kindVars, body }, attributes: [] }

y :: Ident
y = Ident "y"

-- | A site binding `a : Type` and `y : List a`.
context :: XContext
context = bindVar (bindTyVar emptyXContext a XKType) y (listOf (XVar a))

site :: Site
site = { context, origin: InDeclaration (Qualified prim (Ident "decl")) }

frame :: Frame
frame = { site, goal: Nothing }

start :: SolverState
start = initialState (SessionId 0) 10

runIn :: forall a. Frame -> Elab a -> Tuple (Outcome a) SolverState
runIn f action = runElabIn session start (withFrame f action)

outcomeOf :: forall a. Elab a -> Outcome a
outcomeOf action = fst (runIn frame action)

done :: forall a. Show a => Elab a -> (a -> Aff Unit) -> Aff Unit
done action check = case outcomeOf action of
  Done value -> check value
  other -> fail ("the request did not complete: " <> show other)

refuses :: forall a. Show a => Elab a -> (BuildError -> Aff Unit) -> Aff Unit
refuses action check = case outcomeOf action of
  Broke (BuildRejected err) -> check err
  other -> fail ("the request was not refused: " <> show other)

scopeViolation :: BuildError -> Aff Unit
scopeViolation = case _ of
  ScopeViolation _ -> pure unit
  other -> fail ("not a scope violation: " <> show other)

failure :: Diagnostic
failure = EquationFailed site.origin (TypeNotEqual xInt xInt)

-- | The term a handle holds, what it is claimed at, and where it was built.
termOf :: Handle -> Elab { term :: XExpr Unit, claimed :: XType, builtIn :: Maybe ScopeId }
termOf handle = resolveExpr handle <#> \o -> { term: o.term, claimed: o.claimed, builtIn: o.builtIn }

spec :: Spec Unit
spec = describe "Elaborate.BuildTerm" do
  describe "localVariable" do
    it "refers to a variable the scope binds, at the type it is bound at" do
      done (rootScope >>= \root -> localVariable root y >>= termOf) \o -> do
        o.term `shouldEqual` EVar unit y
        o.claimed `shouldEqual` listOf (XVar a)
        o.builtIn `shouldEqual` Just (ScopeId 0)

    it "refuses a name the scope does not bind" do
      refuses (rootScope >>= \root -> localVariable root (Ident "z")) (_ `shouldEqual` UnboundVariable (Ident "z"))

  describe "globalRef" do
    it "refers to a catalog entry at the kinds given, claimed at its scheme so instantiated" do
      done (rootScope >>= \root -> globalRef root (global "poly") [ KindType ] >>= termOf) \o -> do
        o.term `shouldEqual` EGlobal unit (global "poly") [ XKType ]
        o.claimed `shouldEqual` XForall (TyVar "v") XKType xInt

    it "refuses what instantiateScheme refuses, by the same judgement" do
      refuses (rootScope >>= \root -> globalRef root (global "absent") []) (_ `shouldEqual` UnknownScheme (global "absent"))
      refuses (rootScope >>= \root -> globalRef root (global "poly") []) (_ `shouldEqual` SchemeArity (global "poly") 1 0)
      refuses (rootScope >>= \root -> globalRef root (global "poly") [ KindEffect ]) case _ of
        IllKinded (NotQuantifiable _) -> pure unit
        other -> fail ("not NotQuantifiable: " <> show other)
      case outcomeOf (rootScope >>= \root -> globalRef root (global "free") []) of
        Broke (KindingFailed (UnboundTyVar v)) -> v `shouldEqual` a
        other -> fail ("expected the scheme to be refused: " <> show other)

  describe "literal" do
    it "is claimed at the type of its kind of literal" do
      let
        claimedAt lit = rootScope >>= \root -> literal root lit >>= termOf <#> _.claimed
      done (claimedAt (LitInt 1)) (_ `shouldEqual` xInt)
      done (claimedAt (LitNumber 1.5)) (_ `shouldEqual` con "Number")
      done (claimedAt (LitBoolean true)) (_ `shouldEqual` con "Boolean")

  describe "a leaf's claimed type" do
    it "is observed where the leaf was built, with the scope it is kinded under" do
      let
        observed = do
          root <- rootScope
          opened <- openForall root "t" KindType
          term <- globalRef opened.bodyScope (global "poly") [ KindType ]
          claimed <- typeOf term >>= resolveType
          pure { builtIn: claimed.builtIn, bound: Map.member (TyVar "t#0") claimed.scope.tyVars }
      done observed (_ `shouldEqual` { builtIn: Just (ScopeId 1), bound: true })

  describe "a term's scope" do
    it "is usable where it was built and below, and nowhere else" do
      let
        inChild = do
          root <- rootScope
          outer <- openForall root "t" KindType
          inner <- openForall outer.bodyScope "u" KindType
          sibling <- openForall root "s" KindType
          term <- literal outer.bodyScope (LitInt 0)
          pure { root, outer: outer.bodyScope, inner: inner.bodyScope, sibling: sibling.bodyScope, term }
        usedIn pick = do
          c <- inChild
          scope <- resolveScope (pick c)
          void (usableTermIn scope c.term)
      done (usedIn _.outer) (_ `shouldEqual` unit)
      done (usedIn _.inner) (_ `shouldEqual` unit)
      refuses (usedIn _.root) scopeViolation
      refuses (usedIn _.sibling) scopeViolation

    it "refuses a term built in no build scope" do
      let
        unscoped = do
          root <- rootScope >>= resolveScope
          term <- issue (ExprObject { term: ELit unit (LitInt 0), claimed: xInt, scope: { kindVars: Set.empty, tyVars: Map.empty }, builtIn: Nothing, region: Nothing })
          void (usableTermIn root term)
      refuses unscoped scopeViolation

  describe "a fresh name" do
    it "is fresh where it is bound, skipping one the context already holds" do
      let
        drawn = do
          first <- freshIdent (Set.singleton (Ident "x#0")) "x"
          second <- freshIdent Set.empty "x"
          pure (Tuple first second)
      done drawn (_ `shouldEqual` Tuple (Ident "x#1") (Ident "x#2"))

    it "is drawn again, the same, after a rollback" do
      let
        again = do
          _ <- transact (freshIdent Set.empty "x" *> raiseDiagnostic failure)
          freshIdent Set.empty "x"
      done again (_ `shouldEqual` Ident "x#0")

    it "for a type binder skips one the scope already binds" do
      let
        crowded = frame { site = site { context = bindTyVar context (TyVar "t#0") XKType } }
        opened = do
          root <- rootScope
          binder <- openForall root "t" KindType
          resolveType binder.variable <#> _.type
      case fst (runIn crowded opened) of
        Done ty -> ty `shouldEqual` XVar (TyVar "t#1")
        other -> fail (show other)
