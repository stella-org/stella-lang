-- | Closing a row nothing needs anything of to `()`, once the fits are resolved
-- | by direction.
module Test.Stella.Compiler.Elaborate.Close (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Row (xnf)
import Stella.Compiler.Elaborate.CorePlus.Term (XExpr(..))
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Driver.Attempt (attemptPending, runAttempt)
import Stella.Compiler.Elaborate.Driver.Close (Closing(..), Undoing(..), closeRows)
import Stella.Compiler.Elaborate.Driver.Loop (run)
import Stella.Compiler.Elaborate.Driver.Resolve (resolveByDirection)
import Stella.Compiler.Elaborate.Environment.Imported (sessionEnvOf)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, Outcome(..), SessionEnv, SolverState, closeBoundary, freshTypeMeta, initialState, openBoundary, placeFit, require)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitUse(..))
import Stella.Compiler.Elaborate.Mechanism.Pending (Job(..), Site)
import Stella.Compiler.Elaborate.Mechanism.Scheduler (create, lookupPending, reblock)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (substitute)
import Stella.Compiler.Elaborate.Vocabulary.Handle (SessionId(..))
import Stella.Compiler.Elaborate.Surface.Type (xFunction)
import Stella.Compiler.TypedCore (Literal(..), primSignature)
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Prim (unitTy)
import Stella.Compiler.TypedCore.Type (RowKey(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

session :: SessionEnv
session = sessionEnvOf primSignature []

declaration :: Qualified Ident
declaration = Qualified (ModuleName "M") (Ident "f")

site :: Site
site = { context: emptyXContext, origin: InDeclaration declaration }

ownerOf :: Origin -> Qualified Ident
ownerOf = case _ of
  InDeclaration name -> name
  AtSource o -> o.declaration

effect :: String -> XRowEntry
effect n = XRowEffectEntry (Qualified (ModuleName "M") (EffName n)) []

console :: XRowEntry
console = effect "Console"

clock :: XRowEntry
clock = effect "Clock"

row :: Array XRowEntry -> XType -> XType
row entries tail = foldr XRowExtend tail entries

rowEffect :: XKind
rowEffect = XKRow RowEffect

literal :: XExpr Unit
literal = ELit unit (LitInt 1)

unit' :: XType
unit' = XCon unitTy []

-- | Run the action as an attempt, the loop to quiescence, and the resolution of
-- | the fits; then close the rows of `f`, its term the one the action gives.
closing :: forall a. Elab { term :: XExpr Unit, keep :: a } -> (a -> Closing -> SolverState -> Aff Unit) -> Aff Unit
closing action k = case runAttempt session action (initialState (SessionId 0) 100) of
  Tuple (Done r) s -> do
    let
      Tuple _ quiet = run session s
      Tuple _ resolved = resolveByDirection session (attemptPending session) ownerOf quiet
    case closeRows session (attemptPending session) ownerOf declaration site r.term resolved of
      Tuple (Right c) after -> k r.keep c after
      Tuple (Left d) _ -> fail (show d)
  Tuple _ _ -> fail "the attempt did not commit"

-- | That the two rows are one, as their normal forms say once what is solved
-- | is substituted.
sameRow :: SolverState -> XType -> XType -> Aff Unit
sameRow s a b = xnf (substitute s.tentative.metas a) `shouldEqual` xnf (substitute s.tentative.metas b)

metaOf :: XType -> Maybe MetaVar
metaOf = case _ of
  XMeta m -> Just m
  _ -> Nothing

spec :: Spec Unit
spec = describe "Stella.Compiler.Elaborate.Driver.Close" do
  it "closes the row of a pure local λ to `()`, which nothing else decides" do
    closing
      ( do
          -- `(\_ -> 1) ()` at a top-level value's right-hand side
          sigma <- openBoundary emptyXContext
          lambda <- freshTypeMeta emptyXContext rowEffect
          f <- placeFit site Wrapping lambda (XMeta sigma)
          closeBoundary site sigma XRowEmpty
          pure { term: EFit unit f literal, keep: { sigma, lambda } }
      )
      \r closed after -> do
        closed `shouldEqual` Closed (Set.fromFoldable (metaOf r.lambda))
        sameRow after r.lambda XRowEmpty
        sameRow after (XMeta r.sigma) XRowEmpty

  it "leaves a checking boundary's ambient row to the boundary, which decides it once the rows inside are closed" do
    closing
      ( do
          sigma <- openBoundary emptyXContext
          a <- freshTypeMeta emptyXContext rowEffect
          f <- placeFit site Wrapping a (XMeta sigma)
          closeBoundary site sigma (row [ console ] XRowEmpty)
          pure { term: EFit unit f literal, keep: { sigma, a } }
      )
      \r closed after -> do
        closed `shouldEqual` Closed (Set.fromFoldable (metaOf r.a))
        sameRow after (XMeta r.sigma) (row [ console ] XRowEmpty)

  it "does not close a row a fit needs to hold what its source performs, and closes the sources' tails" do
    closing
      ( do
          e <- freshTypeMeta emptyXContext rowEffect
          a <- freshTypeMeta emptyXContext rowEffect
          b <- freshTypeMeta emptyXContext rowEffect
          f <- placeFit site Wrapping (row [ console ] a) e
          _ <- placeFit site Wrapping (row [ clock ] b) e
          pure { term: EFit unit f literal, keep: { e, a, b } }
      )
      \r closed after -> do
        closed `shouldEqual` Closed (Set.fromFoldable (Array.mapMaybe metaOf [ r.a, r.b ]))
        sameRow after r.e (row [ console, clock ] XRowEmpty)

  it "counts where a row stands in the types the term writes, and not the fits naming it" do
    -- named by two fits and standing once in a type: closed
    closing
      ( do
          e <- freshTypeMeta emptyXContext rowEffect
          f <- placeFit site Wrapping e (row [ console ] XRowEmpty)
          _ <- placeFit site Wrapping e (row [ clock ] XRowEmpty)
          pure { term: ELam unit (Ident "x") (xFunction unit' e unit') (EFit unit f literal), keep: e }
      )
      \e closed _ -> closed `shouldEqual` Closed (Set.fromFoldable (metaOf e))
    -- standing twice: left
    closing
      ( do
          e <- freshTypeMeta emptyXContext rowEffect
          f <- placeFit site Wrapping e (row [ console ] XRowEmpty)
          pure { term: ELam unit (Ident "x") (xFunction unit' e unit') (ELam unit (Ident "y") (xFunction unit' e unit') (EFit unit f literal)), keep: unit }
      )
      \_ closed _ -> closed `shouldEqual` NothingClosed

  it "closes a row a `Lacks` names, `()` meeting it, and leaves one a `Disjoint` names" do
    closing
      ( do
          e <- freshTypeMeta emptyXContext rowEffect
          require site (XLacks (EffectKey (Qualified (ModuleName "M") (EffName "Console"))) e)
          f <- placeFit site Wrapping e (row [ console ] XRowEmpty)
          pure { term: EFit unit f literal, keep: e }
      )
      \e closed _ -> closed `shouldEqual` Closed (Set.fromFoldable (metaOf e))
    closing
      ( do
          e <- freshTypeMeta emptyXContext rowEffect
          require site (XDisjoint e (row [ clock ] XRowEmpty))
          f <- placeFit site Wrapping e (row [ console ] XRowEmpty)
          pure { term: EFit unit f literal, keep: unit }
      )
      \_ closed _ -> closed `shouldEqual` NothingClosed

  it "undone where what it decides is refused, the refusal kept as what the owner is reported by" do
    closing
      ( do
          -- the union of the boundary's sources is formed only once their
          -- tails are closed, and then holds what `()` cannot
          sigma <- openBoundary emptyXContext
          a <- freshTypeMeta emptyXContext rowEffect
          b <- freshTypeMeta emptyXContext rowEffect
          f <- placeFit site Wrapping (row [ console ] a) (XMeta sigma)
          _ <- placeFit site Wrapping (row [ clock ] b) (XMeta sigma)
          closeBoundary site sigma XRowEmpty
          pure { term: EFit unit f literal, keep: a }
      )
      \a closed after -> do
        case closed of
          Undone { cause: UndoneBy (BoundaryNotContained _ _) } -> pure unit
          other -> fail ("not undone by the boundary: " <> show other)
        substitute after.tentative.metas a `shouldEqual` a

  it "leaves a row a waiting equation awaits, whether or not either side shows it" do
    case runAttempt session placed (initialState (SessionId 0) 100) of
      Tuple (Done r) s -> do
        let
          -- an equation of `f` waiting on `?e`, which neither of its sides names
          Tuple id created = create site (JobUnify { kind: rowEffect, left: XRowUnion r.x r.y, right: row [ console ] XRowEmpty }) s.tentative.scheduler
          waiting = s { tentative { scheduler = reblock' id created (Set.fromFoldable (Array.mapMaybe metaOf [ r.e ])) } }
        case closeRows session (attemptPending session) ownerOf declaration site r.term waiting of
          Tuple (Right c) _ -> c `shouldEqual` NothingClosed
          Tuple (Left d) _ -> fail (show d)
      Tuple _ _ -> fail "the attempt did not commit"
  where
  placed = do
    e <- freshTypeMeta emptyXContext rowEffect
    x <- freshTypeMeta emptyXContext rowEffect
    y <- freshTypeMeta emptyXContext rowEffect
    f <- placeFit site Wrapping e (row [ console ] XRowEmpty)
    pure { term: EFit unit f literal, e, x, y }

  reblock' id scheduler ms = case lookupPending scheduler id of
    Just p -> reblock p ms scheduler
    Nothing -> scheduler
