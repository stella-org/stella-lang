-- | The kernel's term binders and applications.
-- |
-- | Four things are what these cases are for. **A binder's variable stays under
-- | it**: a term built in a body's scope is refused outside it, through every
-- | builder that takes a term. **A compound term is claimed at the type the Core
-- | rule gives it**, read off the claims of its parts, and waits only on the
-- | metavariable that decides whether the shape it needs is there. **A claim is
-- | not a proof**: a term whose parts disagree is built, and the Core type
-- | checker is what refuses it. And **the names the host binds pass that
-- | checker**.
module Test.Stella.Compiler.Elaborate.Binders (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Build (emptyRow, extendRow, openConstraint, openForall, rootScope, typeConstructor, typeVariable)
import Stella.Compiler.Elaborate.BuildTerm (closeConstraintAbs, closeLambda, closeLet, closeLetRec, closeTypeAbs, constraintApply, literal, openConstraintAbs, openLambda, openLet, openLetRec, openTypeAbs, termApply, typeApply)
import Stella.Compiler.Elaborate.Build as Build
import Stella.Compiler.Elaborate.Constructors (emptyConstructorEnv)
import Stella.Compiler.Elaborate.Effects (emptyEffectEnv)
import Stella.Compiler.Elaborate.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Context (Origin(..), XContext, bindTyVar, emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Elab (Cause(..), Elab, Frame, Outcome(..), SessionEnv, SolverState, initialState, issue, resolveExpr, runElabIn, throw, withFrame)
import Stella.Compiler.Elaborate.Handle (Handle, HandleObject(..), ScopeId(..), SessionId(..))
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (KindingEnv, kindingOf)
import Stella.Compiler.Elaborate.Obligation (Basis(..), Breach(..))
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Run (runAttempt)
import Stella.Compiler.Elaborate.Solve (freshMetaType)
import Stella.Compiler.Elaborate.Term (XExpr(..), toCoreExpr)
import Stella.Compiler.Elaborate.Type (MetaVar, XConstraint(..), XType(..))
import Stella.Compiler.Elaborate.Unify (UnifyError(..), emptyContext, freshMeta)
import Stella.Compiler.Elaborate.View (ConstraintView(..), KindView(..), PayloadView(..))
import Stella.Compiler.TypedCore (Decl(..), Ident(..), Kind(..), Literal(..), Module, ModuleName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), monoScheme)
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (intTy, primSignature, pureFn)
import Stella.Compiler.TypedCore as Core
import Data.Either (Either(..), isRight)
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
xInt = XCon intTy []

-- | `argument -{row}-> result`.
fnType :: XType -> XType -> XType -> XType
fnType argument row result = XApp (XApp (XApp (XCon (tyName "Function") []) argument) row) result

-- | `Prim`'s type constructors, which a function type and a literal need, and
-- | `List`.
kinding :: KindingEnv
kinding =
  (kindingOf primSignature)
    { types = Map.insert (tyName "List") { kindVars: [], body: KFun KType KType } (kindingOf primSignature).types }

session :: SessionEnv
session = { catalog: catalogOf [], kinding, constructors: emptyConstructorEnv, effects: emptyEffectEnv }

r :: TyVar
r = TyVar "r"

keyN :: RowKey
keyN = SymbolKey (Symbol "n")

-- | A site binding `r : Row Type`.
context :: XContext
context = bindTyVar emptyXContext r (XKRow RowType)

site :: Site
site = { context, origin: InDeclaration (Qualified prim (Ident "decl")) }

frame :: Frame
frame = { site, goal: Nothing }

start :: SolverState
start = initialState (SessionId 0) 10

-- | Unsolved metavariables that may head a claim: `?f : Type -> Type` and
-- | `?m : Type`, which a solution can make a function type, and
-- | `?g : Row Type -> Type` and `?h : Type -> Type -> Type -> Type -> Type`,
-- | which applied to one and to four arguments no solution can.
withMetas :: { state :: SolverState, f :: MetaVar, m :: MetaVar, g :: MetaVar, h :: MetaVar }
withMetas =
  let
    fresh kind = freshMeta { kind, scope: { types: Set.empty, kinds: Set.empty } }
    Tuple f metas1 = fresh (XKFun XKType XKType) emptyContext
    Tuple m metas2 = fresh XKType metas1
    Tuple g metas3 = fresh (XKFun (XKRow RowType) XKType) metas2
    Tuple h metas4 = fresh (XKFun XKType (XKFun XKType (XKFun XKType (XKFun XKType XKType)))) metas3
  in
    { state: start { tentative = start.tentative { metas = metas4 } }, f, m, g, h }

outcomeIn :: forall a. SolverState -> Elab a -> Outcome a
outcomeIn s action = fst (runElabIn session s (withFrame frame action))

outcomeOf :: forall a. Elab a -> Outcome a
outcomeOf = outcomeIn start

-- | The term a handle holds, what it is claimed at, and where it was built.
termOf :: Handle -> Elab { term :: XExpr Unit, claimed :: XType, builtIn :: Maybe ScopeId }
termOf handle = resolveExpr handle <#> \o -> { term: o.term, claimed: o.claimed, builtIn: o.builtIn }

builds :: Elab Handle -> ({ term :: XExpr Unit, claimed :: XType, builtIn :: Maybe ScopeId } -> Aff Unit) -> Aff Unit
builds action check = case outcomeOf (action >>= termOf) of
  Done o -> check o
  other -> fail ("the builder did not complete: " <> show other)

refuses :: forall a. Show a => Elab a -> (BuildError -> Aff Unit) -> Aff Unit
refuses action check = case outcomeOf action of
  Broke (BuildRejected err) -> check err
  other -> fail ("the builder did not refuse: " <> show other)

scopeViolation :: BuildError -> Aff Unit
scopeViolation = case _ of
  ScopeViolation _ -> pure unit
  other -> fail ("not a scope violation: " <> show other)

binderMisuse :: BuildError -> Aff Unit
binderMisuse = case _ of
  BinderMisuse _ -> pure unit
  other -> fail ("not a binder misuse: " <> show other)

failure :: Diagnostic
failure = EquationFailed site.origin (TypeNotEqual xInt xInt)

int :: Handle -> Elab Handle
int scope = typeConstructor scope intTy []

litOne :: Handle -> Elab Handle
litOne scope = literal scope (LitInt 1)

-- | `λ(x : Int). x`, closed in the root at the empty row.
intIdentity :: Elab Handle
intIdentity = do
  root <- rootScope
  opened <- int root >>= openLambda root "x"
  emptyRow root >>= closeLambda root opened.binder opened.variable

x0 :: Ident
x0 = Ident "x#0"

spec :: Spec Unit
spec = describe "Elaborate.BuildTerm, binders and applications" do
  describe "a lambda" do
    it "binds a fresh variable in its body, and is claimed at an arrow over the row given" do
      builds intIdentity \o -> do
        o.term `shouldEqual` ELam unit x0 xInt (EVar unit x0)
        o.claimed `shouldEqual` fnType xInt XRowEmpty xInt
        o.builtIn `shouldEqual` Just (ScopeId 0)

    it "keeps its variable under it, whatever builder it is given to" do
      let
        applied = do
          root <- rootScope
          opened <- int root >>= openLambda root "x"
          f <- intIdentity
          termApply root f opened.variable
        letBound = do
          root <- rootScope
          opened <- int root >>= openLambda root "x"
          openLet root "v" opened.variable
        acrossSiblings = do
          root <- rootScope
          left <- int root >>= openLambda root "x"
          right <- int root >>= openLambda root "y"
          emptyRow root >>= closeLambda root right.binder left.variable
      refuses applied scopeViolation
      refuses letBound scopeViolation
      refuses acrossSiblings scopeViolation

    it "takes its row from the scope it was opened in, at Row Effect" do
      let
        closedWith row = do
          root <- rootScope
          opened <- int root >>= openLambda root "x"
          row root opened.bodyScope >>= closeLambda root opened.binder opened.variable
      refuses (closedWith \_ body -> emptyRow body) scopeViolation
      refuses (closedWith \root _ -> freshMetaType root (KindRow RowType)) case _ of
        NotAnEffectRow _ -> pure unit
        other -> fail ("not NotAnEffectRow: " <> show other)
      builds (closedWith \root _ -> freshMetaType root (KindRow RowEffect)) \o ->
        case o.claimed of
          XApp (XApp (XApp _ _) (XMeta _)) _ -> pure unit
          other -> fail ("not an arrow over the row metavariable: " <> show other)

    it "binds only a type at Type" do
      refuses (rootScope >>= \root -> typeConstructor root (tyName "List") [] >>= openLambda root "x") case _ of
        NotAType _ -> pure unit
        other -> fail ("not NotAType: " <> show other)

  describe "termApply" do
    it "is claimed at the result of the function's claim, whatever the argument is claimed at" do
      builds (intIdentity >>= \f -> rootScope >>= \root -> litOne root >>= termApply root f) \o -> do
        o.term `shouldEqual` EApp unit (ELam unit x0 xInt (EVar unit x0)) (ELit unit (LitInt 1))
        o.claimed `shouldEqual` xInt
      builds (intIdentity >>= \f -> rootScope >>= \root -> literal root (LitBoolean true) >>= termApply root f) \o ->
        o.claimed `shouldEqual` xInt

    it "waits on the metavariable heading the function's claim, and on nothing inside an arrow" do
      let
        claimedAt ty = do
          root <- rootScope
          f <- issue (ExprObject { term: EVar unit (Ident "f"), claimed: ty, scope: { kindVars: Set.empty, tyVars: context.tyVars }, builtIn: Just (ScopeId 0), region: Nothing })
          litOne root >>= termApply root f
      case outcomeIn withMetas.state (claimedAt (XApp (XMeta withMetas.f) xInt)) of
        Postponed (ExplicitPostponement ms) -> ms `shouldEqual` Set.singleton withMetas.f
        other -> fail ("expected a postponement: " <> show other)
      case outcomeIn withMetas.state (claimedAt (XMeta withMetas.m)) of
        Postponed (ExplicitPostponement ms) -> ms `shouldEqual` Set.singleton withMetas.m
        other -> fail ("expected a postponement: " <> show other)
      case outcomeIn withMetas.state (claimedAt (fnType (XMeta withMetas.m) XRowEmpty xInt) >>= termOf) of
        Done o -> o.claimed `shouldEqual` xInt
        other -> fail ("expected the application: " <> show other)

    it "refuses a claim headed by a metavariable no solution can make a function" do
      let
        claimedAt ty = do
          root <- rootScope
          f <- issue (ExprObject { term: EVar unit (Ident "f"), claimed: ty, scope: { kindVars: Set.empty, tyVars: context.tyVars }, builtIn: Just (ScopeId 0), region: Nothing })
          litOne root >>= termApply root f
        notAFunction = case _ of
          Broke (BuildRejected (NotAFunction _)) -> pure unit
          other -> fail ("not NotAFunction: " <> show other)
      notAFunction (outcomeIn withMetas.state (claimedAt (XApp (XMeta withMetas.g) XRowEmpty)))
      notAFunction (outcomeIn withMetas.state (claimedAt (XApp (XApp (XApp (XApp (XMeta withMetas.h) xInt) xInt) xInt) xInt)))

    it "refuses a function claim no solution can make a function" do
      refuses (rootScope >>= \root -> litOne root >>= \o -> termApply root o o) case _ of
        NotAFunction _ -> pure unit
        other -> fail ("not NotAFunction: " <> show other)

  describe "a type abstraction and its application" do
    it "is claimed at a forall over the body's claim, and instantiated by typeApply" do
      let
        polyIdentity = do
          root <- rootScope
          t <- openTypeAbs root "t" KindType
          x <- openLambda t.bodyScope "x" t.variable
          lam <- emptyRow t.bodyScope >>= closeLambda t.bodyScope x.binder x.variable
          closeTypeAbs root t.binder lam
        t0 = TyVar "t#0"
      builds polyIdentity \o ->
        o.claimed `shouldEqual` XForall t0 XKType (fnType (XVar t0) XRowEmpty (XVar t0))
      builds (polyIdentity >>= \p -> rootScope >>= \root -> int root >>= typeApply root p) \o ->
        o.claimed `shouldEqual` fnType xInt XRowEmpty xInt
      refuses (polyIdentity >>= \p -> rootScope >>= \root -> emptyRow root >>= typeApply root p) case _ of
        IllKinded _ -> pure unit
        other -> fail ("not ill-kinded: " <> show other)
      refuses (rootScope >>= \root -> litOne root >>= \o -> int root >>= typeApply root o) case _ of
        NotAForall _ -> pure unit
        other -> fail ("not NotAForall: " <> show other)

  describe "a constraint abstraction and its application" do
    let
      lacksNR root = typeVariable root r >>= \rv -> pure (LacksView keyN rv)
      guarded = do
        root <- rootScope
        c <- lacksNR root
        opened <- openConstraintAbs root c
        litOne opened.bodyScope >>= closeConstraintAbs root opened.binder

    it "is claimed at the constraint over the body's claim" do
      builds guarded \o -> o.claimed `shouldEqual` XConstrained (XLacks keyN (XVar r)) xInt

    it "requires the constraint of the scope it is applied in, together with the term" do
      case outcomeOf (guarded >>= \g -> rootScope >>= \root -> constraintApply root g) of
        Failed (ObligationRejected rejected) -> do
          rejected.basis `shouldEqual` Required
          rejected.breach `shouldEqual` LacksUnprovenAtSite keyN r
        other -> fail ("expected the requirement to be rejected: " <> show other)
      let
        underAssumption = do
          g <- guarded
          root <- rootScope
          c <- lacksNR root
          opened <- openConstraint root c
          constraintApply opened.bodyScope g
      case outcomeOf (underAssumption >>= termOf) of
        Done o -> o.claimed `shouldEqual` xInt
        other -> fail ("expected the application: " <> show other)

    it "fails where it closes over a constraint that cannot hold, and refuses a claim that is not constrained" do
      let
        contradiction = do
          root <- rootScope
          i <- int root
          n <- emptyRow root >>= extendRow root keyN (TypePayload i)
          opened <- openConstraintAbs root (LacksView keyN n)
          litOne opened.bodyScope >>= closeConstraintAbs root opened.binder
      case outcomeOf contradiction of
        Failed (ObligationRejected rejected) -> rejected.basis `shouldEqual` Assumed
        other -> fail ("expected the assumption to be rejected: " <> show other)
      refuses (rootScope >>= \root -> litOne root >>= constraintApply root) case _ of
        NotConstrained _ -> pure unit
        other -> fail ("not NotConstrained: " <> show other)

  describe "let and letrec" do
    it "binds a let's variable at its right-hand side's claim, and is claimed at the body's" do
      let
        bound = do
          root <- rootScope
          opened <- litOne root >>= openLet root "v"
          closeLet root opened.binder opened.variable
        v0 = Ident "v#0"
      builds bound \o -> do
        o.term `shouldEqual` ELet unit v0 xInt (ELit unit (LitInt 1)) (EVar unit v0)
        o.claimed `shouldEqual` xInt

    it "binds every letrec name in every right-hand side and in the body" do
      let
        group = do
          root <- rootScope
          i <- int root
          opened <- openLetRec root [ { hint: "a", type: i }, { hint: "b", type: i } ]
          case opened.variables of
            [ va, vb ] -> closeLetRec root opened.binder [ vb, va ] va
            _ -> throw failure
        a0 = Ident "a#0"
        b1 = Ident "b#1"
      builds group \o ->
        o.term `shouldEqual`
          ELetRec unit
            [ { name: a0, ty: xInt, value: EVar unit b1 }, { name: b1, ty: xInt, value: EVar unit a0 } ]
            (EVar unit a0)

    it "refuses a letrec closed with another number of right-hand sides, or litOne from outside the group" do
      let
        closedWith rhss = do
          root <- rootScope
          i <- int root
          opened <- openLetRec root [ { hint: "a", type: i } ]
          outside <- int root >>= openLambda root "x"
          rhs <- rhss root outside.variable opened.variables
          case opened.variables of
            [ v ] -> closeLetRec root opened.binder rhs v
            _ -> throw failure
      refuses (closedWith \_ _ _ -> pure []) case _ of
        LetRecArity _ 1 0 -> pure unit
        other -> fail ("not LetRecArity: " <> show other)
      refuses (closedWith \_ outside _ -> pure [ outside ]) scopeViolation

  describe "binders of every sort" do
    it "refuse being closed by the operation for another sort" do
      let
        letAsLambda = do
          root <- rootScope
          opened <- litOne root >>= openLet root "v"
          emptyRow root >>= closeLambda root opened.binder opened.variable
        lambdaAsForall = do
          root <- rootScope
          opened <- int root >>= openLambda root "x"
          int root >>= Build.closeForall root opened.binder
        forallAsTypeAbs = do
          root <- rootScope
          opened <- openForall root "t" KindType
          litOne root >>= closeTypeAbs root opened.binder
      refuses letAsLambda binderMisuse
      refuses lambdaAsForall binderMisuse
      refuses forallAsTypeAbs binderMisuse

    it "are held open until closed, at the attempt root" do
      case fst (runAttempt session (withFrame frame (rootScope >>= \root -> int root >>= openLambda root "x")) start) of
        Broke (BindersLeftOpen open) -> open `shouldEqual` Set.singleton (ScopeId 1)
        other -> fail ("expected the attempt to halt: " <> show other)

  describe "the Core type checker" do
    it "accepts what was built, the names the host bound included, and refuses a claim the term does not bear out" do
      let
        applied argument = do
          f <- intIdentity
          root <- rootScope
          argument root >>= termApply root f
        coreOf action = case outcomeOf (action >>= termOf) of
          Done o -> case toCoreExpr o.term of
            Right core -> Just core
            Left _ -> Nothing
          _ -> Nothing
      case coreOf intIdentity, coreOf (applied litOne), coreOf (applied \root -> literal root (LitBoolean true)) of
        Just lam, Just good, Just bad -> do
          isRight (verdict (moduleOf lam good)) `shouldEqual` true
          isRight (verdict (moduleOf lam bad)) `shouldEqual` false
        _, _, _ -> fail "a term did not cross the boundary"

-- | The module declaring the intIdentity and its application.
moduleOf :: Core.Expr Unit -> Core.Expr Unit -> Module Unit
moduleOf lam applied =
  { annotation: unit
  , name: ModuleName "Main"
  , imports: []
  , exports: []
  , decls:
      [ DeclNonRec unit { name: Ident "ident", scheme: monoScheme (pureFn coreInt coreInt), value: lam, attributes: [] }
      , DeclNonRec unit { name: Ident "applied", scheme: monoScheme coreInt, value: applied, attributes: [] }
      ]
  }
  where
  coreInt = Core.TCon intTy []

verdict :: Module Unit -> Either P.String Unit
verdict m = case declare primSignature m of
  Left e -> Left (show e.error)
  Right _ -> Right unit
