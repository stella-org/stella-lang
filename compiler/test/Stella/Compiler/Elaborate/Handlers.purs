-- | The kernel's `perform`, handler, and cell builders.
-- |
-- | Four things are what these cases are for. **A `perform` is claimed at what
-- | its operation resumes with**, read off the effect's declaration at the
-- | element it is given. **A handler's clauses bind what the Core rule binds**,
-- | fresh, at the types the declaration gives, and are closed together. **A
-- | region is a binder**: a cell is named by the region's binder, reached in any
-- | scope the region stands around, and a goal asked for there may read it. And
-- | **what is built passes the Core type checker**.
module Test.Stella.Compiler.Elaborate.Handlers (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Vocabulary.Trace (Tracing(..))
import Stella.Compiler.Elaborate.Kernel.Builder.Type (emptyRow, extendRow, openConstraint, rootScope, typeConstructor, typeVariable)
import Stella.Compiler.Elaborate.Kernel.Builder.Handler (closeHandle, closeRegion, openHandle, openRegion, perform, readCell, writeCell)
import Stella.Compiler.Elaborate.Kernel.Builder.Term (closeLambda, jump, literal, localVariable, openJoin, openLambda)
import Stella.Compiler.Elaborate.Environment.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), XContext, bindTyVar, bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (BuildError(..), Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Environment.Effects (effectsOf, emptyEffectEnv)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Frame, Outcome(..), SessionEnv, SolverState, assignTerm, freshTermMeta, initialState, resolveExpr, runElabIn, raiseDiagnostic, withFrame)
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle, SessionId(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (KindingFault(..), kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Kernel.Solve (require, subgoal)
import Stella.Compiler.Elaborate.CorePlus.Term (XExpr(..), XOpClause(..), toCoreExpr)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (TermError(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..), toCore)
import Stella.Compiler.Elaborate.Mechanism.Unify (UnifyError(..))
import Stella.Compiler.Elaborate.Vocabulary.View (ConstraintView(..), PayloadView(..))
import Stella.Compiler.TypedCore (Decl(..), EffName(..), Ident(..), Literal(..), Module, ModuleName(..), OpName(..), Qualified(..), RegionName(..), RowElemKind(..), RowKey(..), Symbol(..), TyVar(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore as Core
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (booleanTy, functionTy, intTy, primSignature, unitTy)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Either (Either(..), either, isRight)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple, fst)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

main :: ModuleName
main = ModuleName "Main"

effect :: P.String -> Qualified EffName
effect name = Qualified main (EffName name)

state :: Qualified EffName
state = effect "State"

counter :: Qualified EffName
counter = effect "Counter"

poly :: Qualified EffName
poly = effect "Poly"

get :: OpName
get = OpName "get"

put :: OpName
put = OpName "put"

next :: OpName
next = OpName "next"

ident :: OpName
ident = OpName "ident"

cellN :: RowKey
cellN = SymbolKey (Symbol "n")

xInt :: XType
xInt = XCon intTy []

xUnit :: XType
xUnit = XCon unitTy []

coreInt :: Type
coreInt = TCon intTy []

coreUnit :: Type
coreUnit = TCon unitTy []

fnType :: XType -> XType -> XType -> XType
fnType argument row result = XApp (XApp (XApp (XCon functionTy []) argument) row) result

-- | `effect State (s : Type) { get : Unit ->* s; put : s ->* Unit }`,
-- | `effect Counter { next : Unit ->* Int }`, and
-- | `effect Poly { ident : forall (b : Type). b ->* b }`.
effectsModule :: Module P.Int
effectsModule =
  { annotation: 0
  , name: main
  , imports: []
  , exports: []
  , decls:
      [ DeclEffect 1
          { name: EffName "State"
          , params: [ { name: TyVar "s", kind: Core.KType } ]
          , operations:
              [ { name: get, tyBinders: [], argument: coreUnit, resumesWith: TVar (TyVar "s") }
              , { name: put, tyBinders: [], argument: TVar (TyVar "s"), resumesWith: coreUnit }
              ]
          , attributes: []
          }
      , DeclEffect 2
          { name: EffName "Counter"
          , params: []
          , operations: [ { name: next, tyBinders: [], argument: coreUnit, resumesWith: coreInt } ]
          , attributes: []
          }
      , DeclEffect 3
          { name: EffName "Poly"
          , params: []
          , operations:
              [ { name: ident, tyBinders: [ { name: TyVar "b", kind: Core.KType } ], argument: TVar (TyVar "b"), resumesWith: TVar (TyVar "b") } ]
          , attributes: []
          }
      ]
  }

declared :: Either P.String Signature
declared = either (Left <<< show <<< _.error) Right (declare primSignature effectsModule)

signature :: Signature
signature = either (const primSignature) identity declared

session :: SessionEnv
session =
  { catalog: catalogOf []
  , kinding: kindingOf signature
  , constructors: constructorsOf signature
  , effects: effectsOf signature
  , tracing: TraceDisabled
  }

e :: TyVar
e = TyVar "e"

-- | A site binding `e : Row Effect`, `u : Unit`, and `c : Int`.
context :: XContext
context = bindVar (bindVar (bindTyVar emptyXContext e (XKRow RowEffect)) (Ident "u") xUnit) (Ident "c") xInt

site :: Site
site = { context, origin: InDeclaration (Qualified main (Ident "decl")) }

frame :: Frame
frame = { site, goal: Nothing }

start :: SolverState
start = initialState (SessionId 0) 10

runIn :: forall a. SessionEnv -> Elab a -> Tuple (Outcome a) SolverState
runIn s action = runElabIn s start (withFrame frame action)

outcomeOf :: forall a. Elab a -> Outcome a
outcomeOf action = fst (runIn session action)

claims :: Elab Handle -> (XType -> Aff Unit) -> Aff Unit
claims action check = case outcomeOf (action >>= resolveExpr <#> _.claimed) of
  Done ty -> check ty
  other -> fail ("the builder did not complete: " <> show other)

refuses :: forall a. Show a => Elab a -> (BuildError -> P.Boolean) -> Aff Unit
refuses action test = case outcomeOf action of
  Broke (BuildRejected err) | test err -> pure unit
  other -> fail ("not the refusal expected: " <> show other)

failure :: Diagnostic
failure = EquationFailed site.origin (TypeNotEqual xInt xInt)

var :: Handle -> P.String -> Elab Handle
var scope name = localVariable scope (Ident name)

int :: Handle -> Elab Handle
int scope = typeConstructor scope intTy []

statePayload :: Handle -> Elab PayloadView
statePayload scope = int scope <#> \i -> EffectPayload state [ i ]

-- | A region opened with its binder, the name it binds, and its body scope.
type Opened = { binder :: Handle, name :: RegionName, bodyScope :: Handle }

-- | `region [ℓ] ( n : Int ) @ ( 0 ) in handle 0 with { Counter; return x -> x;
-- | next u -> body }`, answering `Int` with the residual row given, the row and
-- | the clause's body built given the region.
counted
  :: (Opened -> Handle -> Elab Handle)
  -> (Opened -> Handle -> Elab Handle)
  -> Elab Handle
counted residual body = do
  root <- rootScope
  i <- int root
  region <- openRegion root [ { key: cellN, type: i } ]
  zero <- literal region.bodyScope (LitInt 0)
  rho <- residual region region.bodyScope
  opened <- openHandle region.bodyScope zero (EffectKey counter) (EffectPayload counter []) i rho [ { op: next, full: false } ]
  case opened.clauses of
    [ clause ] -> do
      b <- body region clause.scope
      handled <- closeHandle region.bodyScope opened.binder opened.returnClause.variable [ b ]
      initial <- literal root (LitInt 0)
      closeRegion root region.binder handled [ initial ]
    _ -> raiseDiagnostic failure

-- | `( region ℓ )`, the region given alone.
regionRow :: Opened -> Handle -> Elab Handle
regionRow region scope = emptyRow scope >>= extendRow scope (RegionKey region.name) (RegionPayload region.name)

spec :: Spec Unit
spec = describe "Elaborate.BuildHandler" do
  it "is given a signature declaring its effects" do
    isRight declared `shouldEqual` true

  describe "perform" do
    it "is claimed at what the operation resumes with, the effect's parameters instantiated" do
      claims (rootScope >>= \root -> statePayload root >>= \p -> var root "u" >>= perform root (EffectKey state) p get []) (_ `shouldEqual` xInt)
      claims (rootScope >>= \root -> statePayload root >>= \p -> var root "u" >>= perform root (SymbolKey (Symbol "cache")) p get []) (_ `shouldEqual` xInt)

    it "instantiates the operation's own type binders at the type arguments given" do
      claims
        ( do
            root <- rootScope
            boolean <- typeConstructor root booleanTy []
            arg <- literal root (LitBoolean true)
            perform root (EffectKey poly) (EffectPayload poly []) ident [ boolean ] arg
        )
        (_ `shouldEqual` XCon booleanTy [])

    it "refuses an operation the effect lacks, type arguments it does not bind, and an element its key does not make" do
      let
        performing key payload op = rootScope >>= \root -> payload root >>= \p -> var root "u" >>= perform root key p op []
      refuses (performing (EffectKey state) statePayload (OpName "absent")) case _ of
        UnknownOperation _ _ -> true
        _ -> false
      refuses (performing (EffectKey poly) (\_ -> pure (EffectPayload poly [])) ident) case _ of
        OperationArity _ 1 0 -> true
        _ -> false
      refuses (performing (EffectKey counter) statePayload get) case _ of
        EntryMismatch _ -> true
        _ -> false
      refuses (performing (EffectKey state) (\_ -> pure (EffectPayload state [])) get) case _ of
        IllKinded _ -> true
        _ -> false
      refuses (performing (RegionKey (RegionName "r")) (\_ -> pure (RegionPayload (RegionName "r"))) get) case _ of
        RegionEntryForbidden -> true
        _ -> false

    it "halts where the kinding environment declares an effect the table lacks" do
      case fst (runIn (session { effects = emptyEffectEnv }) (rootScope >>= \root -> statePayload root >>= \p -> var root "u" >>= perform root (EffectKey state) p get [])) of
        Broke (EffectTableMismatch name) -> name `shouldEqual` state
        other -> fail ("expected a host defect: " <> show other)

  describe "a handler" do
    it "binds the return clause's variable at the computation's claim, and is claimed at its answer" do
      let
        handled = do
          root <- rootScope
          c <- var root "c"
          i <- int root
          rho <- emptyRow root
          opened <- openHandle root c (EffectKey counter) (EffectPayload counter []) i rho [ { op: next, full: false } ]
          case opened.clauses of
            [ clause ] -> do
              b <- literal clause.scope (LitInt 1)
              closeHandle root opened.binder opened.returnClause.variable [ b ]
            _ -> raiseDiagnostic failure
      case outcomeOf (handled >>= resolveExpr) of
        Done o -> do
          o.claimed `shouldEqual` xInt
          case o.term of
            EHandle _ (EVar _ (Ident "c")) h ->
              h.returnClause.body `shouldEqual` EVar unit h.returnClause.binder
            other -> fail ("not the handle expected: " <> show other)
        other -> fail (show other)

    it "binds a full clause's continuation at the resumption into the answer, over the clauses' row" do
      let
        continuation = do
          root <- rootScope
          c <- var root "c"
          i <- int root
          rho <- emptyRow root
          opened <- openHandle root c (EffectKey counter) (EffectPayload counter []) i rho [ { op: next, full: true } ]
          case opened.clauses of
            [ { continuation: Just k } ] -> resolveExpr k <#> _.claimed
            _ -> raiseDiagnostic failure
      case outcomeOf continuation of
        Done ty -> ty `shouldEqual` fnType xInt XRowEmpty xInt
        other -> fail (show other)

    it "names every operation of its effect once, and refuses a computation that jumps" do
      let
        withClauses clauses = rootScope >>= \root -> do
          c <- var root "c"
          i <- int root
          rho <- emptyRow root
          p <- statePayload root
          openHandle root c (EffectKey state) p i rho clauses
      refuses (withClauses [ { op: get, full: false } ]) case _ of
        MissingClause op -> op == put
        _ -> false
      refuses (withClauses [ { op: get, full: false }, { op: get, full: false }, { op: put, full: false } ]) case _ of
        DuplicateClause op -> op == get
        _ -> false
      let
        jumping = do
          root <- rootScope
          i <- int root
          j <- openJoin root "j" [] i
          jumped <- jump j.bodyScope j.join []
          rho <- emptyRow j.bodyScope
          openHandle j.bodyScope jumped (EffectKey counter) (EffectPayload counter []) i rho [ { op: next, full: false } ]
      refuses jumping case _ of
        JoinOutOfScope _ -> true
        _ -> false

    it "is closed with one body per clause, each under its own" do
      let
        closedWith bodies = do
          root <- rootScope
          c <- var root "c"
          i <- int root
          rho <- emptyRow root
          opened <- openHandle root c (EffectKey counter) (EffectPayload counter []) i rho [ { op: next, full: false } ]
          bs <- bodies opened
          closeHandle root opened.binder opened.returnClause.variable bs
      refuses (closedWith (\_ -> pure [])) case _ of
        ClauseCount _ 1 0 -> true
        _ -> false
      refuses (closedWith (\o -> pure [ o.returnClause.variable ])) case _ of
        ScopeViolation _ -> true
        _ -> false

  describe "a region" do
    it "binds a fresh name over its body, and is claimed at what its body is" do
      case outcomeOf (counted regionRow (\r scope -> readCell scope r.binder cellN) >>= resolveExpr) of
        Done o -> do
          o.claimed `shouldEqual` xInt
          case o.term of
            ERegion _ name [ cell ] [ ELit _ (LitInt 0) ] (EHandle _ _ _) -> do
              cell.key `shouldEqual` cellN
              name `shouldEqual` RegionName "r#0"
            other -> fail ("not the region expected: " <> show other)
        other -> fail (show other)

    it "stands where a residual row has a tail bound outside it, needing nothing of that tail" do
      case outcomeOf (counted (\r scope -> typeVariable scope e >>= extendRow scope (RegionKey r.name) (RegionPayload r.name)) (\r scope -> readCell scope r.binder cellN)) of
        Done _ -> pure unit
        other -> fail (show other)

    it "is closed with one initial value per cell" do
      let
        closedWith initials = do
          root <- rootScope
          i <- int root
          region <- openRegion root [ { key: cellN, type: i } ]
          body <- literal region.bodyScope (LitInt 1)
          is <- initials root
          closeRegion root region.binder body is
      refuses (closedWith (\_ -> pure [])) case _ of
        InitialValueCount _ 1 0 -> true
        _ -> false

    it "refuses a body claimed at a type mentioning the region" do
      let
        escaping = do
          root <- rootScope
          i <- int root
          region <- openRegion root [ { key: cellN, type: i } ]
          lam <- openLambda region.bodyScope "y" i
          read <- readCell lam.bodyScope region.binder cellN
          row <- regionRow region region.bodyScope
          f <- closeLambda region.bodyScope lam.binder read row
          initial <- literal root (LitInt 0)
          closeRegion root region.binder f [ initial ]
      refuses escaping case _ of
        RegionEscapes _ -> true
        _ -> false

    it "refuses its region's key in a constraint where the region is not in scope, by either path" do
      let
        ghost = RegionKey (RegionName "ghost")
        unbound = case _ of
          IllKinded (UnboundRegion (RegionName "ghost")) -> true
          _ -> false
      refuses (rootScope >>= \root -> emptyRow root >>= \row -> openConstraint root (LacksView ghost row)) unbound
      refuses (rootScope >>= \root -> emptyRow root >>= \row -> require root (LacksView ghost row)) unbound
      let
        inScope = do
          root <- rootScope
          i <- int root
          region <- openRegion root [ { key: cellN, type: i } ]
          row <- emptyRow region.bodyScope
          _ <- openConstraint region.bodyScope (LacksView (RegionKey region.name) row)
          require region.bodyScope (LacksView (RegionKey region.name) row)
      case outcomeOf inScope of
        Done _ -> pure unit
        other -> fail ("a key of a region in scope was refused: " <> show other)

    it "jumps to no join point outside, whether built inside its body or handed in as one" do
      let
        outer bodyOf = do
          root <- rootScope
          i <- int root
          j <- openJoin root "j" [] i
          region <- openRegion j.bodyScope [ { key: cellN, type: i } ]
          body <- bodyOf j region
          initial <- literal j.bodyScope (LitInt 0)
          closeRegion j.bodyScope region.binder body [ initial ]
        outOfScope = case _ of
          JoinOutOfScope _ -> true
          _ -> false
      refuses (outer \j region -> jump region.bodyScope j.join []) outOfScope
      refuses (outer \j _ -> jump j.bodyScope j.join []) outOfScope

    it "refuses a layout giving one key twice" do
      refuses (rootScope >>= \root -> int root >>= \i -> openRegion root [ { key: cellN, type: i }, { key: cellN, type: i } ]) case _ of
        DuplicateCell _ -> true
        _ -> false

  describe "a cell" do
    it "is read and written wherever its region stands around, a clause and a lambda there included" do
      let
        inClause f = counted regionRow f
      case outcomeOf (inClause (\r scope -> readCell scope r.binder cellN)) of
        Done _ -> pure unit
        other -> fail (show other)
      case outcomeOf (inClause \r scope -> readCell scope r.binder cellN >>= \v -> writeCell scope r.binder cellN v >>= resolveExpr >>= \w -> if w.claimed == xUnit then readCell scope r.binder cellN else raiseDiagnostic failure) of
        Done _ -> pure unit
        other -> fail (show other)
      let
        underLambda r scope = do
          i <- int scope
          lam <- openLambda scope "y" i
          read <- readCell lam.bodyScope r.binder cellN
          _ <- regionRow r scope >>= closeLambda scope lam.binder read
          readCell scope r.binder cellN
      case outcomeOf (inClause underLambda) of
        Done _ -> pure unit
        other -> fail (show other)

    it "is refused outside its region, and where the layout lacks its key" do
      let
        outside = do
          root <- rootScope
          i <- int root
          region <- openRegion root [ { key: cellN, type: i } ]
          readCell root region.binder cellN
      refuses outside case _ of
        NoRegion _ -> true
        _ -> false
      refuses (counted regionRow (\r scope -> readCell scope r.binder (SymbolKey (Symbol "absent")))) case _ of
        CellAbsent _ -> true
        _ -> false

    it "names its own region, an inner region holding a cell of the same key notwithstanding" do
      let
        nested = counted regionRow \outer outerClause -> do
          i <- int outerClause
          inner <- openRegion outerClause [ { key: cellN, type: i } ]
          read <- readCell inner.bodyScope outer.binder cellN
          initial <- literal outerClause (LitInt 0)
          closeRegion outerClause inner.binder read [ initial ]
      case outcomeOf (nested >>= resolveExpr) of
        Done o -> case o.term of
          ERegion _ outerName _ _ (EHandle _ _ h) -> case h.opClauses of
            [ XFastClause c ] -> case c.body of
              ERegion _ innerName _ _ (EReadCell _ read _) -> do
                (innerName /= outerName) `shouldEqual` true
                read `shouldEqual` outerName
              other -> fail ("not the inner region expected: " <> show other)
            other -> fail ("not the clause expected: " <> show other)
          other -> fail ("not the region expected: " <> show other)
        other -> fail (show other)

  describe "a goal asked for in a region" do
    it "has the region in its target's scope, and an assignment reading a cell outside one is refused" do
      let
        asked = counted regionRow \r scope -> do
          i <- int scope
          goal <- subgoal scope i (Qualified main (Ident "resolve"))
          o <- resolveExpr goal
          case o.term of
            ETermMeta _ target -> assignTerm site target (EReadCell unit r.name cellN)
            _ -> raiseDiagnostic failure
          pure goal
      case outcomeOf asked of
        Done _ -> pure unit
        other -> fail ("an assignment reading the region's cell was refused: " <> show other)
      let
        outside = do
          m <- freshTermMeta context xInt
          assignTerm site m (EReadCell unit (RegionName "r") cellN)
      case outcomeOf outside of
        Failed (TermAssignmentFailed _ (TermEscapingRegion _ name)) -> name `shouldEqual` RegionName "r"
        other -> fail ("expected the assignment to fail: " <> show other)

  describe "the Core type checker" do
    it "accepts a region around a handler whose clause reads its cell, built by the kernel" do
      case outcomeOf (counted regionRow (\r scope -> readCell scope r.binder cellN) >>= resolveExpr) of
        Done o -> case toCore o.claimed, toCoreExpr o.term of
          Just scheme, Right value ->
            isRight
              ( declare signature
                  { annotation: unit
                  , name: ModuleName "User"
                  , imports: [ main ]
                  , exports: []
                  , decls: [ DeclNonRec unit { name: Ident "counted", scheme: monoScheme scheme, value, attributes: [] } ]
                  }
              ) `shouldEqual` true
          _, _ -> fail "the region did not cross the boundary"
        other -> fail (show other)
