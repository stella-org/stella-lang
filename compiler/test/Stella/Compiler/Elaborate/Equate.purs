-- | `equate`: an equation decided where it can be, and otherwise kept as an
-- | equality job while what stated it goes on.
module Test.Stella.Compiler.Elaborate.Equate (spec) where

import Prelude

import Data.Either (Either(..))
import Data.Map as Map
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Driver.Attempt (runAttempt)
import Stella.Compiler.Elaborate.Driver.Loop (RunResult(..), run)
import Stella.Compiler.Elaborate.Environment.Imported (sessionEnvOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Outcome(..), SessionEnv, SolverState, equate, freshTypeMeta, initialState)
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Mechanism.Unify (substitute)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.TypedCore (Decl(..), Module, declare, primSignature)
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..))
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), Symbol(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (intTy)
import Stella.Compiler.TypedCore.Type (RowKey(..), Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

lib :: ModuleName
lib = ModuleName "Lib"

-- | `data Box a = Box a` and `data Bag a = Bag a`.
libCore :: Module Unit
libCore =
  { annotation: unit
  , name: lib
  , imports: []
  , exports: []
  , decls: map container [ "Box", "Bag" ]
  }
  where
  container n = DeclData unit
    { name: TyName n, kindVars: [], params: [ { name: TyVar "a", kind: KType } ], constructors: [ { name: Ident n, tag: 0, fields: [ TVar (TyVar "a") ] } ], isNewtype: false, attributes: [] }

session :: Either String SessionEnv
session = case declare primSignature libCore of
  Left err -> Left (show err.error)
  Right sig -> Right (sessionEnvOf sig [])

boxOf :: XType -> XType
boxOf = XApp (XCon (Qualified lib (TyName "Box")) [])

bagOf :: XType -> XType
bagOf = XApp (XCon (Qualified lib (TyName "Bag")) [])

int :: XType
int = XCon intTy []

site :: Site
site = { context: emptyXContext, origin: InDeclaration (Qualified (ModuleName "M") (Ident "f")) }

-- | `?v ⊎ ?w ≡ ( a : Int | () )`, which waits: nothing yet says how the row is
-- | split between the two.
stuckOn :: XType -> XType -> { kind :: XKind, left :: XType, right :: XType }
stuckOn v w = { kind: rowType, left: XRowUnion v w, right: fieldA }

rowType :: XKind
rowType = XKRow RowType

-- | `( a : Int | () )`.
fieldA :: XType
fieldA = XRowExtend (XRowTypeEntry (SymbolKey (Symbol "a")) int) XRowEmpty

-- | Run the action as an attempt, then the loop.
attempted :: forall a. (Elab a) -> (Tuple (Outcome a) SolverState -> RunResult -> SolverState -> Aff Unit) -> Aff Unit
attempted action k = case session of
  Left err -> fail err
  Right env -> do
    let
      Tuple outcome s = runAttempt env action (initialState (SessionId 0) 10)
      Tuple report after = run env s
    k (Tuple outcome s) report.result after

isCompleted :: RunResult -> Boolean
isCompleted = case _ of
  Completed -> true
  _ -> false

spec :: Spec Unit
spec = describe "Stella.Compiler.Elaborate.Kernel.equate" do
  it "decides an equation it can at once" do
    attempted
      ( do
          m <- freshTypeMeta emptyXContext XKType
          equate site { kind: XKType, left: m, right: int }
          pure m
      )
      \(Tuple outcome s) _ _ -> case outcome of
        Done m -> substitute s.tentative.metas m `shouldEqual` int
        _ -> fail "not done"

  it "refuses an equation nothing makes true, and installs nothing" do
    attempted (equate site { kind: XKType, left: boxOf int, right: bagOf int })
      \(Tuple outcome _) _ _ -> case outcome of
        Failed (EquationFailed _ _) -> pure unit
        _ -> fail "not refused"

  it "keeps one it cannot decide as a job and goes on, the job solved once an assignment decides it" do
    attempted
      ( do
          v <- freshTypeMeta emptyXContext rowType
          w <- freshTypeMeta emptyXContext rowType
          equate site (stuckOn v w)
          -- what states it goes on, and decides `?v` afterwards
          equate site { kind: rowType, left: v, right: fieldA }
          pure w
      )
      \(Tuple outcome s) result after -> case outcome of
        Done w -> do
          Map.size s.tentative.scheduler.pending `shouldEqual` 1
          isCompleted result `shouldEqual` true
          substitute after.tentative.metas w `shouldEqual` XRowEmpty
          Map.size after.tentative.scheduler.pending `shouldEqual` 0
        _ -> fail "not done"

  it "takes the job back with the attempt that stated it" do
    attempted
      ( do
          v <- freshTypeMeta emptyXContext rowType
          w <- freshTypeMeta emptyXContext rowType
          equate site (stuckOn v w)
          equate site { kind: XKType, left: boxOf int, right: bagOf int }
      )
      \(Tuple outcome s) _ _ -> case outcome of
        Failed _ -> Map.size s.tentative.scheduler.pending `shouldEqual` 0
        _ -> fail "not failed"
