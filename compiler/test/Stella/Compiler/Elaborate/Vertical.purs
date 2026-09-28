-- | The vertical slice, elaborated: Core⁺ right-hand sides carrying type and term
-- | metavariables, solved through the scheduler and by assignment, zonked, and
-- | handed to the Core type checker.
-- |
-- | Two things are what these cases are for. **What elaboration produces is
-- | checked, not trusted**: the terms that come out of the boundary are the ones
-- | the declaration checker accepts, and a term with a hole left does not come
-- | out at all. And **the order of a module is read off what was committed**: a
-- | reference an assignment supplied is among the references of the term it
-- | landed in, though the right-hand side as written held only a metavariable.
module Test.Stella.Compiler.Elaborate.Vertical (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Outcome(..), SolverState, assignTerm, emptySessionEnv, freshTermMeta, freshTypeMeta, initialState, runElab, raiseDiagnostic, transact)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Mechanism.TermMeta (TermError(..), zonkExpr)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Driver.Loop (RunReport, RunResult(..), Submission(..), Submitted, run, submitEquality)
import Stella.Compiler.Elaborate.Mechanism.Pending (PendingId(..), Site)
import Stella.Compiler.Elaborate.Driver.Attempt as Run
import Stella.Compiler.Elaborate.CorePlus.Term (Residue(..), TermMetaVar, XDecisionTree(..), XExpr(..), toCoreExpr)
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..), fromCore)
import Stella.Compiler.TypedCore (Decl(..), Expr, globalsOf, Ident(..), Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), TyName(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Declare (DeclError, declare)
import Stella.Compiler.TypedCore.Prim (intTy, primSignature, pureFn)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.TypedCore.VerticalSlice (intModule, listDecl)

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

int :: Type
int = TCon intTy []

listInt :: Type
listInt = TApp (TCon (Qualified mainModuleName (TyName "List")) []) int

xInt :: XType
xInt = fromCore int

listOf :: XType -> XType
listOf a = XApp (XCon (Qualified mainModuleName (TyName "List")) []) a

nil :: Qualified Ident
nil = Qualified mainModuleName (Ident "Nil")

cons :: Qualified Ident
cons = Qualified mainModuleName (Ident "Cons")

sumName :: Qualified Ident
sumName = Qualified mainModuleName (Ident "sum")

resultName :: Qualified Ident
resultName = Qualified mainModuleName (Ident "result")

intAdd :: Qualified Ident
intAdd = Qualified (ModuleName "Base.Int") (Ident "add")

xs :: Ident
xs = Ident "xs"

x :: Ident
x = Ident "x"

ys :: Ident
ys = Ident "ys"

here :: Origin
here = InDeclaration sumName

site :: Site
site = { context: emptyXContext, origin: here }

-- | What elaboration left open: the type of `sum`'s parameter, the type `Nil` is
-- | instantiated at, the recursive call in `sum`, and the function `result`
-- | applies.
type Holes =
  { param :: XType
  , nilAt :: XType
  , recursion :: TermMetaVar
  , callee :: TermMetaVar
  }

-- | `λ (xs : ?param). case (xs) of …`, the recursive call left as `?recursion`,
-- | which stands at annotation 42.
sumRhs :: Holes -> XExpr P.Int
sumRhs holes =
  ELam 0 xs (holes.param)
    ( ECase 0 [ EVar 0 xs ]
        ( XSwitchCtor (OccScrutinee 0)
            [ { ctor: nil, tree: XLeaf (ELit 0 (LitInt 0)) }
            , { ctor: cons
              , tree:
                  XBind x (OccField (OccScrutinee 0) cons 0)
                    $ XBind ys (OccField (OccScrutinee 0) cons 1)
                    $ XLeaf
                    $ EApp 0 (EApp 0 (EGlobal 0 intAdd []) (EVar 0 x)) (ETermMeta 42 holes.recursion)
              }
            ]
            Nothing
        )
    )

-- | `?callee ( Cons [Int] 1 ( … ( Nil [?nilAt] ) ) )`, the callee at 43.
resultRhs :: Holes -> XExpr P.Int
resultRhs holes =
  EApp 0 (ETermMeta 43 holes.callee)
    (consAt 1 (consAt 2 (consAt 3 (ETyApp 0 (EGlobal 0 nil []) (holes.nilAt)))))
  where
  consAt n rest = EApp 0 (EApp 0 (ETyApp 0 (EGlobal 0 cons []) xInt) (ELit 0 (LitInt n))) rest

-- | Create the holes. `?recursion` is created where the cons branch stands, so
-- | its scope holds `xs`, `x`, and `ys`; `?callee` where `result`'s right-hand
-- | side stands, which binds nothing.
opened :: Elab Holes
opened = do
  param <- freshTypeMeta emptyXContext XKType
  nilAt <- freshTypeMeta emptyXContext XKType
  let
    branch = bindVar (bindVar (bindVar emptyXContext xs param) x xInt) ys (listOf xInt)
  recursion <- freshTermMeta branch Nothing xInt
  callee <- freshTermMeta emptyXContext Nothing (fromCore (pureFn listInt int))
  pure { param, nilAt, recursion, callee }

-- | Open the holes, submit the two equations that decide the types, and run emptySessionEnv the
-- | scheduler to where it stops.
solvedTypes :: Either P.String (Tuple Holes SolverState)
solvedTypes = case runElab (initialState (SessionId 0) 10) opened of
  Tuple (Done holes) s0 ->
    let
      Tuple first s1 = went (submitEquality emptySessionEnv site { kind: XKType, left: holes.param, right: listOf xInt } s0)
      Tuple second s2 = went (submitEquality emptySessionEnv site { kind: XKType, left: holes.nilAt, right: xInt } s1)
      Tuple result s3 = resultOf (run emptySessionEnv s2)
    in
      if first.attempt /= Run.Committed || second.attempt /= Run.Committed then
        Left "an equation was not solved where it was submitted"
      else if result /= Completed then
        Left ("the scheduler stopped at " <> show result)
      else
        Right (Tuple holes s3)
  Tuple outcome _ -> Left ("the holes were not opened: " <> show outcome)

-- | The recursive call is the local `ys` applied to the global `sum`, and the
-- | callee of `result` is `sum` itself.
filled :: Holes -> Elab Unit
filled holes = do
  assignTerm site holes.recursion (EApp 0 (EGlobal 0 sumName []) (EVar 0 ys))
  assignTerm site holes.callee (EGlobal 0 sumName [])

type Crossed = Either (NonEmptyArray (Residue P.Int)) (Expr P.Int)

-- | The Core right-hand sides the boundary gives back, or what it reported.
boundary :: SolverState -> Holes -> { sum :: Crossed, result :: Crossed }
boundary s holes =
  { sum: toCoreExpr (zonkExpr s.tentative.metas (sumRhs holes))
  , result: toCoreExpr (zonkExpr s.tentative.metas (resultRhs holes))
  }

-- | The module the slice is, with the right-hand sides given.
moduleOf :: Expr P.Int -> Expr P.Int -> Module P.Int
moduleOf sumValue resultValue =
  { annotation: 0
  , name: mainModuleName
  , imports: [ ModuleName "Base.Int" ]
  , exports: []
  , decls:
      [ listDecl
      , DeclRec 2
          [ { name: Ident "sum"
            , scheme: monoScheme (pureFn listInt int)
            , value: sumValue
            , attributes: []
            }
          ]
      , DeclNonRec 3 { name: Ident "result", scheme: monoScheme int, value: resultValue, attributes: [] }
      ]
  }

verdict :: Module P.Int -> Either DeclError Unit
verdict m = case declare primSignature intModule of
  Left failure -> Left failure.error
  Right imported -> case declare imported m of
    Left failure -> Left failure.error
    Right _ -> Right unit

-- | A submission that went on, as the cases read it. One that stopped reads as
-- | a job no table holds, halted, so an assertion expecting it to go on fails.
went :: Tuple Submission SolverState -> Tuple Submitted SolverState
went (Tuple submission s) = case submission of
  Continue submitted -> Tuple submitted s
  Stop _ -> Tuple { id: PendingId (-1), attempt: Run.Halted (PendingAbsent (PendingId (-1))) } s

-- | Where a loop stopped, its warnings set aside.
resultOf :: forall s. Tuple RunReport s -> Tuple RunResult s
resultOf (Tuple report s) = Tuple report.result s

spec :: Spec Unit
spec = describe "Elaborate, the vertical slice" do
  it "is solved, filled, zonked, and accepted by the Core type checker" do
    case solvedTypes of
      Left why -> fail why
      Right (Tuple holes s0) -> case runElab s0 (filled holes) of
        Tuple (Done _) s -> case boundary s holes of
          { sum: Right sumCore, result: Right resultCore } ->
            verdict (moduleOf sumCore resultCore) `shouldEqual` Right unit
          { sum, result } ->
            fail ("the boundary refused: " <> show (map (const unit) sum) <> show (map (const unit) result))
        Tuple outcome _ -> fail ("an assignment was refused: " <> show outcome)

  it "has an ill-typed solution in scope assigned, and rejected by the Core type checker" do
    -- `ys` is in `?recursion`'s scope, so the assignment is admitted; it is a
    -- `List Int` where an `Int` is added, which only the checker decides.
    case solvedTypes of
      Left why -> fail why
      Right (Tuple holes s0) ->
        let
          illTyped = do
            assignTerm site holes.recursion (EVar 0 ys)
            assignTerm site holes.callee (EGlobal 0 sumName [])
        in
          case runElab s0 illTyped of
            Tuple (Done _) s -> case boundary s holes of
              { sum: Right sumCore, result: Right resultCore } ->
                (verdict (moduleOf sumCore resultCore) == Right unit) `shouldEqual` false
              _ -> fail "the boundary refused"
            Tuple outcome _ -> fail ("an assignment was refused: " <> show outcome)

  it "puts each solution where its hole stood, under the hole's annotation" do
    case solvedTypes of
      Left why -> fail why
      Right (Tuple holes s0) -> case runElab s0 (filled holes) of
        Tuple (Done _) s ->
          zonkExpr s.tentative.metas (ETermMeta 42 holes.recursion)
            `shouldEqual` EApp 42 (EGlobal 42 sumName []) (EVar 42 ys)
        Tuple outcome _ -> fail ("an assignment was refused: " <> show outcome)

  it "does not come out of the boundary with a hole left" do
    case solvedTypes of
      Left why -> fail why
      Right (Tuple holes s) ->
        map (const unit) (boundary s holes).sum
          `shouldEqual` Left (NonEmptyArray.singleton (ResidualTermMeta 42 holes.recursion))

  it "carries the references an assignment supplied" do
    case solvedTypes of
      Left why -> fail why
      Right (Tuple holes s0) -> case runElab s0 (filled holes) of
        Tuple (Done _) s -> case boundary s holes of
          { sum: Right sumCore, result: Right resultCore } -> do
            globalsOf sumCore `shouldEqual` Set.fromFoldable [ intAdd, sumName ]
            globalsOf resultCore `shouldEqual` Set.fromFoldable [ sumName, cons, nil ]
            -- Kept to the module's own value declarations, those are the edges
            -- the order is computed over: each of the two refers to `sum`.
            Set.intersection (globalsOf sumCore) locals `shouldEqual` Set.singleton sumName
            Set.intersection (globalsOf resultCore) locals `shouldEqual` Set.singleton sumName
          _ -> fail "the boundary refused"
        Tuple outcome _ -> fail ("an assignment was refused: " <> show outcome)
  it "carries the references of the solution committed, and none of one rolled back" do
    -- A candidate assigns `?callee := result` and is discarded; the one committed
    -- afterwards assigns `sum`. Only the second reaches the term.
    case solvedTypes of
      Left why -> fail why
      Right (Tuple holes s0) ->
        let
          discarded = do
            assignTerm site holes.callee (EGlobal 0 resultName [])
            raiseDiagnostic (TermAssignmentFailed here (TermMetaUnbound holes.callee))

          searched = do
            _ <- transact discarded
            assignTerm site holes.recursion (EApp 0 (EGlobal 0 sumName []) (EVar 0 ys))
            assignTerm site holes.callee (EGlobal 0 sumName [])
        in
          case runElab s0 searched of
            Tuple (Done _) s -> case (boundary s holes).result of
              Right resultCore -> Set.member resultName (globalsOf resultCore) `shouldEqual` false
              Left _ -> fail "the boundary refused"
            Tuple outcome _ -> fail ("an assignment was refused: " <> show outcome)

  where
  locals = Set.fromFoldable [ sumName, resultName ]
