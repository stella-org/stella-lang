-- | The kernel's requests over metavariables and constraints.
-- |
-- | Three things are what these cases are for. **Each request reads what it
-- | decides against from the build scope it is given**: a metavariable's scope,
-- | an equation's context, the assumptions a constraint is entailed from or
-- | required with. **Only types the scope may use reach the solver**, so nothing
-- | observed in no build scope is equated, required, or asked for. And **what a
-- | request does goes through the mechanism**, so an equation that breaks an
-- | obligation leaves nothing behind, and entailment never takes a flexible tail
-- | for a fact.
module Test.Stella.Compiler.Elaborate.Solve (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Build (emptyRow, extendRow, openConstraint, openForall, rootScope, typeConstructor, typeVariable)
import Stella.Compiler.Elaborate.Constructors (emptyConstructorEnv)
import Stella.Compiler.Elaborate.Effects (emptyEffectEnv)
import Stella.Compiler.Elaborate.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Context (Origin(..), XContext, bindTyVar, emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Elab (Elab, Frame, Outcome(..), SessionEnv, SolverState, currentMetas, initialState, issue, resolveType, runElabIn, throw, transact, withFrame)
import Stella.Compiler.Elaborate.Handle (Handle, HandleObject(..), ScopeId(..), SessionId(..))
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (KindEvidence(..), KindingEnv, KindingFault(..))
import Stella.Compiler.Elaborate.Obligation (Basis(..), Breach(..))
import Stella.Compiler.Elaborate.Observe (typeOf, viewType)
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Scheduler (isInitial, lookupPending, readyIds)
import Stella.Compiler.Elaborate.Solve (entails, freshMetaType, isAssigned, require, subgoal, unify)
import Stella.Compiler.Elaborate.Type (MetaVar, XType(..))
import Stella.Compiler.Elaborate.Unify (MetaBinding(..), UnifyError(..), lookupMeta, substitute)
import Stella.Compiler.Elaborate.View (ConstraintView(..), KindView(..), PayloadView(..), TypeView(..))
import Stella.Compiler.TypedCore (Ident(..), Kind(..), ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyName(..), TyVar(..))
import Data.Array as Array
import Data.Either (Either(..))
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

xInt :: XType
xInt = XCon (tyName "Int") []

kinding :: KindingEnv
kinding =
  { types: Map.fromFoldable
      [ Tuple (tyName "Int") { kindVars: [], body: KType }
      , Tuple (tyName "List") { kindVars: [], body: KFun KType KType }
      ]
  , effects: Map.empty
  }

session :: SessionEnv
session = { catalog: catalogOf [], kinding, constructors: emptyConstructorEnv, effects: emptyEffectEnv }

resolver :: Qualified Ident
resolver = Qualified (ModuleName "Typeclass") (Ident "resolve")

a :: TyVar
a = TyVar "a"

r :: TyVar
r = TyVar "r"

keyN :: RowKey
keyN = SymbolKey (Symbol "n")

-- | A site binding `a : Type` and `r : Row Type`, and assuming nothing.
context :: XContext
context = bindTyVar (bindTyVar emptyXContext a XKType) r (XKRow RowType)

site :: Site
site = { context, origin: InDeclaration (Qualified prim (Ident "decl")) }

frame :: Frame
frame = { site, goal: Nothing }

start :: SolverState
start = initialState (SessionId 0) 10

run :: forall a. SolverState -> Elab a -> Tuple (Outcome a) SolverState
run s action = runElabIn session s (withFrame frame action)

outcomeOf :: forall a. Elab a -> Outcome a
outcomeOf action = fst (run start action)

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

kindsDiffer :: BuildError -> Aff Unit
kindsDiffer = case _ of
  KindsDiffer _ _ -> pure unit
  other -> fail ("not KindsDiffer: " <> show other)

notAType :: BuildError -> Aff Unit
notAType = case _ of
  NotAType _ -> pure unit
  other -> fail ("not NotAType: " <> show other)

rejectsObligation :: forall a. Show a => Elab a -> Basis -> Breach -> Aff Unit
rejectsObligation action basis breach = case outcomeOf action of
  Failed (ObligationRejected rejected) -> do
    rejected.basis `shouldEqual` basis
    rejected.breach `shouldEqual` breach
  other -> fail ("expected a rejected obligation: " <> show other)

failure :: Diagnostic
failure = EquationFailed site.origin (TypeNotEqual xInt xInt)

int :: Handle -> Elab Handle
int scope = typeConstructor scope (tyName "Int") []

list :: Handle -> Elab Handle
list scope = typeConstructor scope (tyName "List") []

-- | `( n : Int | rest )`, built in the scope.
withN :: Handle -> Handle -> Elab Handle
withN scope rest = int scope >>= \i -> extendRow scope keyN (TypePayload i) rest

-- | The type a handle holds, with what `Ψ` has solved applied, as an
-- | observation reads it.
zonked :: Handle -> Elab XType
zonked handle = substitute <$> currentMetas <*> (_.type <$> resolveType handle)

-- | The metavariable a type handle stands for.
metaOf :: Handle -> Elab MetaVar
metaOf handle = resolveType handle >>= \object -> case object.type of
  XMeta m -> pure m
  _ -> throw failure

-- | The `Meta` handle the view of a metavariable's type gives.
metaHandleOf :: Handle -> Elab Handle
metaHandleOf handle = viewType handle >>= case _ of
  MetaType m -> pure m
  _ -> throw failure

spec :: Spec Unit
spec = describe "Elaborate.Solve" do
  describe "freshMetaType" do
    it "creates a metavariable under the variables of the scope it is given" do
      let
        created = do
          root <- rootScope
          atRoot <- freshMetaType root KindType >>= metaOf
          opened <- openForall root "t" KindType
          inBody <- freshMetaType opened.bodyScope KindType >>= metaOf
          pure (Tuple atRoot inBody)
      case run start created of
        Tuple (Done (Tuple atRoot inBody)) s -> do
          scopeOf s atRoot `shouldEqual` Just (Set.fromFoldable [ a, r ])
          scopeOf s inBody `shouldEqual` Just (Set.fromFoldable [ a, r, TyVar "t#0" ])
        Tuple other _ -> fail (show other)

    it "gives a type built in that scope, at the kind asked" do
      let
        created = do
          root <- rootScope
          opened <- openForall root "t" KindType
          freshMetaType opened.bodyScope (KindRow RowType) >>= resolveType
      done created \object -> do
        object.kind `shouldEqual` ExactKind (XKRow RowType)
        object.builtIn `shouldEqual` Just (ScopeId 1)

    it "refuses a kind no type variable could stand at" do
      let
        notQuantifiable = case _ of
          IllKinded (NotQuantifiable _) -> pure unit
          other -> fail ("not NotQuantifiable: " <> show other)
      refuses (rootScope >>= \root -> freshMetaType root KindEffect) notQuantifiable
      refuses (rootScope >>= \root -> freshMetaType root (KindFun KindType (KindRow RowType))) notQuantifiable
      refuses (rootScope >>= \root -> freshMetaType root KindAnyRow) (_ `shouldEqual` AnyRowAsKind)

    it "creates one no solution can reach a variable of a narrower scope through" do
      let
        escaping = do
          root <- rootScope
          m <- freshMetaType root KindType
          opened <- openForall root "t" KindType
          unify opened.bodyScope m opened.variable
      case outcomeOf escaping of
        Failed (EquationFailed _ _) -> pure unit
        other -> fail ("expected the equation to fail: " <> show other)

  describe "isAssigned" do
    it "reads whether the metavariable is solved now" do
      let
        reading = do
          root <- rootScope
          m <- freshMetaType root KindType
          meta <- metaHandleOf m
          before <- isAssigned meta
          int root >>= unify root m
          after <- isAssigned meta
          pure (Tuple before after)
      done reading (_ `shouldEqual` Tuple false true)

  describe "unify" do
    it "equates at the kind the evidence gives, a row at any kind meeting one at its own" do
      let
        solved = do
          root <- rootScope
          m <- freshMetaType root KindType
          int root >>= unify root m
          row <- freshMetaType root (KindRow RowType)
          e <- emptyRow root
          unify root e row
          e' <- emptyRow root
          unify root e e'
          Tuple <$> zonked m <*> zonked row
      done solved \(Tuple m row) -> do
        m `shouldEqual` xInt
        row `shouldEqual` XRowEmpty

    it "refuses evidence that cannot meet, before anything is unified" do
      refuses (rootScope >>= \root -> join (unify root <$> int root <*> list root)) kindsDiffer
      refuses (rootScope >>= \root -> join (unify root <$> int root <*> emptyRow root)) kindsDiffer

    it "refuses a type the scope may not use" do
      let
        underBinder = do
          root <- rootScope
          whole <- issue (TypeObject { type: XForall (TyVar "b") XKType (XVar (TyVar "b")), kind: ExactKind XKType, scope: { kindVars: Set.empty, tyVars: context.tyVars }, builtIn: Just (ScopeId 0) })
          viewType whole >>= case _ of
            ForallType _ _ body -> int root >>= unify root body
            _ -> throw failure
        fromSibling = do
          root <- rootScope
          left <- openForall root "t" KindType
          right <- openForall root "u" KindType
          unify right.bodyScope right.variable left.variable
      refuses underBinder scopeViolation
      refuses fromSibling scopeViolation

    it "fails where an assignment breaks an obligation, and leaves nothing behind" do
      let
        breaking = do
          root <- rootScope
          t <- freshMetaType root (KindRow RowType)
          meta <- metaHandleOf t
          _ <- withN root t
          solution <- emptyRow root >>= withN root
          caught <- transact (unify root t solution)
          assigned <- isAssigned meta
          pure (Tuple (isLeft caught) assigned)
      done breaking (_ `shouldEqual` Tuple true false)

  describe "entails" do
    it "takes no flexible tail for a fact, and answers once the tail is solved" do
      let
        asked = do
          root <- rootScope
          t <- freshMetaType root (KindRow RowType)
          before <- entails root (LacksView keyN t)
          emptyRow root >>= unify root t
          after <- entails root (LacksView keyN t)
          pure (Tuple before after)
      done asked (_ `shouldEqual` Tuple false true)

    it "proves from the assumptions opened around the scope, and from those only" do
      let
        asked = do
          root <- rootScope
          rv <- typeVariable root r
          atRoot <- entails root (LacksView keyN rv)
          opened <- openConstraint root (LacksView keyN rv)
          inBody <- entails opened.bodyScope (LacksView keyN rv)
          pure (Tuple atRoot inBody)
      done asked (_ `shouldEqual` Tuple false true)

    it "answers false of what the facts refute, and under assumptions that contradict" do
      let
        refuted = do
          root <- rootScope
          n <- emptyRow root >>= withN root
          entails root (LacksView keyN n)
        contradicted = do
          root <- rootScope
          n <- emptyRow root >>= withN root
          opened <- openConstraint root (LacksView keyN n)
          e <- emptyRow opened.bodyScope
          entails opened.bodyScope (LacksView keyN e)
      done refuted (_ `shouldEqual` false)
      done contradicted (_ `shouldEqual` false)

    it "changes nothing" do
      let
        asked = do
          root <- rootScope
          t <- freshMetaType root (KindRow RowType)
          entails root (LacksView keyN t)
        Tuple _ before = run start (rootScope >>= \root -> freshMetaType root (KindRow RowType))
        Tuple _ after = run start asked
      after.tentative.metas.next `shouldEqual` before.tentative.metas.next
      Map.size after.tentative.obligations.entries `shouldEqual` Map.size before.tentative.obligations.entries

  describe "require" do
    it "fails on a constraint already broken where it is introduced" do
      let
        broken = do
          root <- rootScope
          n <- emptyRow root >>= withN root
          require root (LacksView keyN n)
        unproved = do
          root <- rootScope
          rv <- typeVariable root r
          require root (LacksView keyN rv)
      rejectsObligation broken Required (SolutionCarriesKey keyN)
      rejectsObligation unproved Required (LacksUnprovenAtSite keyN r)

    it "is decided against the assumptions opened around the scope" do
      let
        underAssumption = do
          root <- rootScope
          rv <- typeVariable root r
          opened <- openConstraint root (LacksView keyN rv)
          require opened.bodyScope (LacksView keyN rv)
      done underAssumption (_ `shouldEqual` unit)

    it "holds a requirement over a flexible tail, which an assignment must keep" do
      let
        held = do
          root <- rootScope
          t <- freshMetaType root (KindRow RowType)
          require root (LacksView keyN t)
          emptyRow root >>= withN root >>= unify root t
      case outcomeOf held of
        Failed (ObligationBroken broken) -> broken.basis `shouldEqual` Required
        other -> fail ("expected the obligation to break: " <> show other)

  describe "subgoal" do
    it "creates the job and its target under the scope's context, and the term in the scope" do
      let
        asked = do
          root <- rootScope
          opened <- openForall root "t" KindType
          goal <- int opened.bodyScope
          subgoal opened.bodyScope goal resolver >>= typeOf >>= resolveType
      case run start asked of
        Tuple (Done claimed) s -> do
          claimed.type `shouldEqual` xInt
          claimed.builtIn `shouldEqual` Just (ScopeId 1)
          case Array.head (readyIds s.tentative.scheduler) of
            Just id -> do
              isInitial s.tentative.scheduler id `shouldEqual` true
              map (Map.member (TyVar "t#0") <<< _.site.context.tyVars) (lookupPending s.tentative.scheduler id)
                `shouldEqual` Just true
            Nothing -> fail "no job was queued"
        Tuple other _ -> fail (show other)

    it "refuses a goal type that does not stand at Type, or that the scope may not use" do
      refuses (rootScope >>= \root -> list root >>= \l -> subgoal root l resolver) notAType
      refuses (rootScope >>= \root -> emptyRow root >>= \e -> subgoal root e resolver) notAType
      let
        fromChild = do
          root <- rootScope
          opened <- openForall root "t" KindType
          subgoal root opened.variable resolver
      refuses fromChild scopeViolation

    it "is rolled back with the attempt that asked for it" do
      let
        discarded = do
          root <- rootScope
          i <- int root
          void (transact (subgoal root i resolver *> throw failure))
      case run start discarded of
        Tuple (Done _) s -> do
          readyIds s.tentative.scheduler `shouldEqual` []
          Map.size s.tentative.metas.termBindings `shouldEqual` 0
        Tuple other _ -> fail (show other)

-- | The type variables a metavariable's solution may mention.
scopeOf :: SolverState -> MetaVar -> Maybe (Set.Set TyVar)
scopeOf s m = case lookupMeta s.tentative.metas m of
  Just (Unsolved info) -> Just info.scope.types
  _ -> Nothing

isLeft :: forall e a. Either e a -> P.Boolean
isLeft = case _ of
  Left _ -> true
  Right _ -> false
