-- | The kernel's `perform`, handler, and cell builders.
-- |
-- | Four things are what these cases are for. **A `perform` is claimed at what
-- | its operation resumes with**, read off the effect's declaration at the
-- | element it is given. **A handler's clauses bind what the Core rule binds**,
-- | fresh, at the types the declaration gives, and are closed together. **A
-- | region of cells is lexical**: only the operation clauses of the handler
-- | owning it, and what they open, stand in it — and so does a goal asked for
-- | there, wherever it is attempted. And **what is built passes the Core type
-- | checker**.
module Test.Stella.Compiler.Elaborate.Handlers (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Vocabulary.Trace (Tracing(..))
import Stella.Compiler.Elaborate.Kernel.Builder.Type (emptyRow, rootScope, typeConstructor, typeVariable)
import Stella.Compiler.Elaborate.Kernel.Builder.Handler (closeHandle, openHandle, perform, readCell, writeCell)
import Stella.Compiler.Elaborate.Kernel.Builder.Term (closeLambda, closeLet, jump, literal, localVariable, openJoin, openLambda, openLet)
import Stella.Compiler.Elaborate.Environment.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Environment.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), XContext, bindTyVar, bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (BuildError(..), Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Environment.Effects (effectsOf, emptyEffectEnv)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Frame, Outcome(..), SessionEnv, SolverState, assignTerm, freshTermMeta, initialState, resolveExpr, runElabIn, raiseDiagnostic, withFrame)
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle, SessionId(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Mechanism.Obligation (Basis(..), Breach(..))
import Stella.Compiler.Elaborate.Mechanism.Pending (Pending, Site)
import Stella.Compiler.Elaborate.Driver.Attempt (Attempt(..), attemptPendingWith)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (readyIds, takeReady)
import Stella.Compiler.Elaborate.Kernel.Solve (subgoal)
import Stella.Compiler.Elaborate.CorePlus.Term (XExpr(..), toCoreExpr)
import Stella.Compiler.Elaborate.Mechanism.TermMeta (TermError(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..), toCore)
import Stella.Compiler.Elaborate.Mechanism.Unify (UnifyError(..))
import Stella.Compiler.Elaborate.Vocabulary.View (PayloadView(..))
import Stella.Compiler.TypedCore (Decl(..), EffName(..), Ident(..), Literal(..), Module, ModuleName(..), OpName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyVar(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore as Core
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (booleanTy, functionTy, intTy, primSignature, unitTy)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Array as Array
import Data.Either (Either(..), either, isRight)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst)
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

-- | `handle c with { Counter; cells [r] ( n : Int ); return x -> x; next u -> body }
-- | @ ( 0 )`, answering `Int` with the residual row given, the clause's body
-- | built in its scope.
counted
  :: (Handle -> Elab Handle)
  -> (Handle -> Elab Handle)
  -> Elab Handle
counted residual body = do
  root <- rootScope
  c <- var root "c"
  i <- int root
  rho <- residual root
  opened <- openHandle root c (EffectKey counter) (EffectPayload counter []) (Just [ { key: cellN, type: i } ]) i rho [ { op: next, full: false } ]
  case opened.clauses of
    [ clause ] -> do
      b <- body clause.scope
      zero <- literal root (LitInt 0)
      closeHandle root opened.binder opened.returnClause.variable [ b ] [ zero ]
    _ -> raiseDiagnostic failure

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

    it "halts where the kinding environment declares an effect the table lacks" do
      case fst (runIn (session { effects = emptyEffectEnv }) (rootScope >>= \root -> statePayload root >>= \p -> var root "u" >>= perform root (EffectKey state) p get [])) of
        Broke (EffectTableMismatch name) -> name `shouldEqual` state
        other -> fail ("expected a host defect: " <> show other)

  describe "a handler" do
    it "binds the return clause's variable at the computation's claim, and is claimed at its answer" do
      let
        handled = counted emptyRow (\scope -> readCell scope cellN)
      case outcomeOf (handled >>= resolveExpr) of
        Done o -> do
          o.claimed `shouldEqual` xInt
          case o.term of
            EHandle _ (EVar _ (Ident "c")) h [ ELit _ (LitInt 0) ] -> do
              map _.var h.cells `shouldEqual` Just (TyVar "r#0")
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
          opened <- openHandle root c (EffectKey counter) (EffectPayload counter []) Nothing i rho [ { op: next, full: true } ]
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
          openHandle root c (EffectKey state) p Nothing i rho clauses
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
          openHandle j.bodyScope jumped (EffectKey counter) (EffectPayload counter []) Nothing i rho [ { op: next, full: false } ]
      refuses jumping case _ of
        JoinOutOfScope _ -> true
        _ -> false

    it "requires its residual row to hold no region, where it owns cells" do
      case outcomeOf (counted (\root -> typeVariable root e) (\scope -> readCell scope cellN)) of
        Failed (ObligationRejected rejected) -> do
          rejected.basis `shouldEqual` Required
          rejected.breach `shouldEqual` LacksUnprovenAtSite RegionKey e
        other -> fail ("expected the requirement to fail: " <> show other)

    it "is closed with one body per clause, each under its own, and one initial value per cell" do
      let
        closedWith bodies initials = do
          root <- rootScope
          c <- var root "c"
          i <- int root
          rho <- emptyRow root
          opened <- openHandle root c (EffectKey counter) (EffectPayload counter []) (Just [ { key: cellN, type: i } ]) i rho [ { op: next, full: false } ]
          bs <- bodies opened
          is <- initials root
          closeHandle root opened.binder opened.returnClause.variable bs is
      refuses (closedWith (\_ -> pure []) (\root -> Array.singleton <$> literal root (LitInt 0))) case _ of
        ClauseCount _ 1 0 -> true
        _ -> false
      refuses (closedWith (\o -> pure (map _.argument o.clauses)) (\_ -> pure [])) case _ of
        InitialValueCount _ 1 0 -> true
        _ -> false
      refuses (closedWith (\o -> pure [ o.returnClause.variable ]) (\root -> Array.singleton <$> literal root (LitInt 0))) case _ of
        ScopeViolation _ -> true
        _ -> false

  describe "a cell" do
    it "is read and written in the operation clauses of the handler owning it, a lambda there included" do
      let
        inClause f = counted emptyRow f
      case outcomeOf (inClause (\scope -> readCell scope cellN)) of
        Done _ -> pure unit
        other -> fail (show other)
      case outcomeOf (inClause \scope -> readCell scope cellN >>= \v -> writeCell scope cellN v >>= resolveExpr >>= \w -> if w.claimed == xUnit then readCell scope cellN else raiseDiagnostic failure) of
        Done _ -> pure unit
        other -> fail (show other)
      let
        underLambda scope = do
          i <- int scope
          lam <- openLambda scope "y" i
          read <- readCell lam.bodyScope cellN
          _ <- emptyRow scope >>= closeLambda scope lam.binder read
          readCell scope cellN
      case outcomeOf (inClause underLambda) of
        Done _ -> pure unit
        other -> fail (show other)

    it "is refused outside a region, in the return clause, and where the layout lacks its key" do
      let
        noRegion = case _ of
          NoRegion _ -> true
          _ -> false
      refuses (rootScope >>= \root -> readCell root cellN) noRegion
      refuses
        ( do
            root <- rootScope
            c <- var root "c"
            i <- int root
            rho <- emptyRow root
            opened <- openHandle root c (EffectKey counter) (EffectPayload counter []) (Just [ { key: cellN, type: i } ]) i rho [ { op: next, full: false } ]
            readCell opened.returnClause.scope cellN
        )
        noRegion
      refuses (counted emptyRow (\scope -> readCell scope (SymbolKey (Symbol "absent")))) case _ of
        CellAbsent _ -> true
        _ -> false

  describe "a goal asked for in a region" do
    it "is attempted in the same region, and its target takes no cell from outside one" do
      let
        asked = counted emptyRow \scope -> int scope >>= \i -> subgoal scope i (Qualified main (Ident "resolve"))

        reading :: Pending -> Elab Unit
        reading _ = void (rootScope >>= \root -> readCell root cellN)
      case runIn session asked of
        Tuple (Done _) s -> case takeReady s.tentative.scheduler of
          Just (Tuple id taken) -> fst (attemptPendingWith session reading id (s { tentative { scheduler = taken } })) `shouldEqual` Committed
          Nothing -> fail ("no job was queued: " <> show (readyIds s.tentative.scheduler))
        Tuple other _ -> fail (show other)
      let
        outside = do
          m <- freshTermMeta context Nothing xInt
          assignTerm site m (EReadCell unit cellN)
      case outcomeOf outside of
        Failed (TermAssignmentFailed _ (TermEscapingCell _ key)) -> key `shouldEqual` cellN
        other -> fail ("expected the assignment to fail: " <> show other)

  describe "a term built in a region" do
    let
      mismatch = case _ of
        RegionMismatch _ -> true
        _ -> false
      -- A handler of `Counter` owning `n`, opened in the scope given over `0`,
      -- its clause's body built by the function given.
      within scope body = do
        zero <- literal scope (LitInt 0)
        i <- int scope
        rho <- emptyRow scope
        opened <- openHandle scope zero (EffectKey counter) (EffectPayload counter []) (Just [ { key: cellN, type: i } ]) i rho [ { op: next, full: false } ]
        case opened.clauses of
          [ clause ] -> do
            b <- body clause.scope
            initial <- literal scope (LitInt 0)
            closeHandle scope opened.binder opened.returnClause.variable [ b ] [ initial ]
          _ -> raiseDiagnostic failure

      -- An outer handler whose clause builds something, and an inner handler in
      -- that clause whose clause's body is what the function makes of it.
      nested :: (Handle -> Elab Handle) -> (Handle -> Handle -> Elab Handle) -> Elab Handle
      nested outer inner = rootScope >>= \root -> within root \outerClause -> do
        built <- outer outerClause
        within outerClause \innerClause -> inner innerClause built

    it "stands in the region it was built in" do
      case outcomeOf (rootScope >>= \root -> within root \clause -> readCell clause cellN >>= openLet clause "v" >>= \l -> closeLet clause l.binder l.variable) of
        Done _ -> pure unit
        other -> fail (show other)

    it "is not captured by an inner region holding a cell of the same key" do
      refuses (nested (\outerClause -> readCell outerClause cellN) (\_ t -> pure t)) mismatch
      refuses (nested (\outerClause -> readCell outerClause cellN) (\innerClause t -> openLet innerClause "v" t >>= \l -> closeLet innerClause l.binder l.variable)) mismatch

    it "is not captured when it waits on a goal asked for in its region" do
      refuses (nested (\outerClause -> int outerClause >>= \i -> subgoal outerClause i (Qualified main (Ident "resolve"))) (\_ t -> pure t)) mismatch

    it "stands anywhere where it depends on no region" do
      case outcomeOf (nested (\outerClause -> literal outerClause (LitInt 1)) (\_ t -> pure t)) of
        Done _ -> pure unit
        other -> fail ("a pure term was refused: " <> show other)
      case outcomeOf (nested (\outerClause -> within outerClause \clause -> readCell clause cellN) (\_ t -> pure t)) of
        Done _ -> pure unit
        other -> fail ("a handler binding its own cells was refused: " <> show other)

    it "stands anywhere where a goal it waits on was asked for in a handler of its own, solved or not" do
      let
        -- A handler whose clause is a goal asked for there, solved to read the
        -- handler's own cell where `solve` says so.
        ownGoal solve outerClause = within outerClause \clause -> do
          i <- int clause
          goal <- subgoal clause i (Qualified main (Ident "resolve"))
          when solve do
            o <- resolveExpr goal
            case o.term of
              ETermMeta _ target -> assignTerm site target (EReadCell unit cellN)
              _ -> raiseDiagnostic failure
          pure goal
      case outcomeOf (nested (ownGoal false) (\_ t -> pure t)) of
        Done _ -> pure unit
        other -> fail ("a handler waiting on its own goal was refused: " <> show other)
      case outcomeOf (nested (ownGoal true) (\_ t -> pure t)) of
        Done _ -> pure unit
        other -> fail ("a handler whose own goal reads its cell was refused: " <> show other)

  describe "the Core type checker" do
    it "accepts a handler owning cells, built by the kernel" do
      let
        literalCounter = do
          root <- rootScope
          zero <- literal root (LitInt 0)
          i <- int root
          rho <- emptyRow root
          opened <- openHandle root zero (EffectKey counter) (EffectPayload counter []) (Just [ { key: cellN, type: i } ]) i rho [ { op: next, full: false } ]
          case opened.clauses of
            [ clause ] -> do
              body <- readCell clause.scope cellN
              initial <- literal root (LitInt 0)
              closeHandle root opened.binder opened.returnClause.variable [ body ] [ initial ] >>= resolveExpr
            _ -> raiseDiagnostic failure
      case outcomeOf literalCounter of
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
          _, _ -> fail "the handler did not cross the boundary"
        other -> fail (show other)
