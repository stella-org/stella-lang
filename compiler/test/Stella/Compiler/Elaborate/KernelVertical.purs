-- | A term the kernel's requests build, carried from a synthesis job's target to
-- | the Core type checker.
-- |
-- | ```text
-- | kernel requests → Expr → the target's solution, committed → zonkTerm
-- |   → toCoreExpr → globalsOf → the Core type checker
-- | ```
-- |
-- | Three things are what these cases are for. **Only what commits reaches the
-- | boundary**: a candidate a `transact` discarded leaves no term, no name, and
-- | no reference behind. **What does not resolve is reported**, the target of a
-- | goal not yet run among it. And **a claim is not a proof**: a term in scope,
-- | claimed at the goal's type but not bearing the claim out, is built and
-- | committed here, and the Core type checker refuses it.
module Test.Stella.Compiler.Elaborate.KernelVertical (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Build (emptyRow, rootScope, typeConstructor)
import Stella.Compiler.Elaborate.BuildTerm (closeLambda, globalRef, literal, openLambda, termApply)
import Stella.Compiler.Elaborate.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Effects (effectsOf)
import Stella.Compiler.Elaborate.Elab (Elab, Outcome(..), SessionEnv, SolverState, assignTerm, createSynthesis, initialState, resolveExpr, runElabIn, throw, transact)
import Stella.Compiler.Elaborate.Handle (Handle, SessionId(..))
import Stella.Compiler.Elaborate.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Pending (Job(..), Pending, Site, goalOf)
import Stella.Compiler.Elaborate.Run (Attempt(..), attemptPendingWith)
import Stella.Compiler.Elaborate.Scheduler (takeReady)
import Stella.Compiler.Elaborate.Term (Residue(..), TermMetaVar, XExpr(..), toCoreExpr)
import Stella.Compiler.Elaborate.TermMeta (zonkExpr)
import Stella.Compiler.Elaborate.Type (XType(..))
import Stella.Compiler.Elaborate.Unify (UnifyError(..))
import Stella.Compiler.TypedCore (Decl(..), Expr(..), Ident(..), Literal(..), Module, ModuleName(..), Qualified(..), Type(..), globalsOf, monoScheme)
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (intTy, primSignature)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), either, isRight)
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

main :: ModuleName
main = ModuleName "Main"

qualified :: P.String -> Qualified Ident
qualified name = Qualified main (Ident name)

xInt :: XType
xInt = XCon intTy []

coreInt :: Type
coreInt = TCon intTy []

-- | `one = 1` and `two = 2`, the globals a term may refer to.
valuesModule :: Module P.Int
valuesModule =
  { annotation: 0
  , name: main
  , imports: []
  , exports: []
  , decls:
      [ DeclNonRec 1 { name: Ident "one", scheme: monoScheme coreInt, value: Lit 1 (LitInt 1), attributes: [] }
      , DeclNonRec 2 { name: Ident "two", scheme: monoScheme coreInt, value: Lit 2 (LitInt 2), attributes: [] }
      ]
  }

signature :: Signature
signature = either (const primSignature) identity (declare primSignature valuesModule)

session :: SessionEnv
session =
  { catalog: catalogOf (map entry [ "one", "two" ])
  , kinding: kindingOf signature
  , constructors: constructorsOf signature
  , effects: effectsOf signature
  }
  where
  entry name = { name: qualified name, sort: ValueEntry, scheme: { kindVars: [], body: xInt }, attributes: [] }

site :: Site
site = { context: emptyXContext, origin: InDeclaration (Qualified (ModuleName "User") (Ident "answer")) }

failure :: Diagnostic
failure = EquationFailed site.origin (TypeNotEqual xInt xInt)

-- | A goal at `Int`, created and queued, and the state holding it.
asked :: Either P.String (Tuple TermMetaVar SolverState)
asked = case runElabIn session (initialState (SessionId 0) 10) (createSynthesis site xInt (qualified "resolve") Nothing) of
  Tuple (Done (Tuple _ target)) s -> Right (Tuple target s)
  Tuple other _ -> Left (show other)

-- | The goal attempted by a runner that assigns its target the term the action
-- | given builds from the root and the target, and the declaration's right-hand
-- | side, `?m`, zonked after.
answered :: (Handle -> TermMetaVar -> Elab Handle) -> Either P.String (Tuple Attempt (XExpr Unit))
answered build = case asked of
  Left err -> Left err
  Right (Tuple target s0) -> case takeReady s0.tentative.scheduler of
    Nothing -> Left "no job was queued"
    Just (Tuple id taken) ->
      let
        runner :: Pending -> Elab Unit
        runner p = case p.job of
          JobSynthesis goal -> do
            root <- rootScope
            let
              goalTarget = (goalOf goal).target
            term <- build root goalTarget >>= resolveExpr
            assignTerm p.site goalTarget term.term
          JobUnify _ -> throw failure
        Tuple result s1 = attemptPendingWith session runner id (s0 { tentative { scheduler = taken } })
      in
        Right (Tuple result (zonkExpr s1.tentative.metas (ETermMeta unit target)))

-- | `(λ(x : Int). x) Main.one`.
identityOfOne :: Handle -> TermMetaVar -> Elab Handle
identityOfOne root _ = do
  i <- typeConstructor root intTy []
  lam <- openLambda root "x" i
  f <- emptyRow root >>= closeLambda root lam.binder lam.variable
  globalRef root (qualified "one") [] >>= termApply root f

-- | A module declaring `answer : Int` with the right-hand side given.
verdict :: Expr Unit -> Either P.String Unit
verdict value = case declare signature m of
  Left e -> Left (show e.error)
  Right _ -> Right unit
  where
  m =
    { annotation: unit
    , name: ModuleName "User"
    , imports: [ main ]
    , exports: []
    , decls: [ DeclNonRec unit { name: Ident "answer", scheme: monoScheme coreInt, value, attributes: [] } ]
    }

spec :: Spec Unit
spec = describe "Elaborate, a kernel-built term through the Core boundary" do
  it "reports the target of a goal not yet run as a residue" do
    case asked of
      Right (Tuple target s) -> case toCoreExpr (zonkExpr s.tentative.metas (ETermMeta unit target)) of
        Left residues -> NonEmptyArray.toArray residues `shouldEqual` [ ResidualTermMeta unit target ]
        Right _ -> fail "an unsolved target crossed the boundary"
      Left err -> fail err

  it "carries the committed term, and its references, to a Core type checker that accepts it" do
    case answered identityOfOne of
      Right (Tuple Committed rhs) -> case toCoreExpr rhs of
        Right core -> do
          globalsOf core `shouldEqual` Set.singleton (qualified "one")
          isRight (verdict core) `shouldEqual` true
        Left _ -> fail "the committed term did not cross the boundary"
      other -> fail (show other)

  it "leaves no term, name, or reference of a candidate a transact discarded" do
    let
      -- A candidate that opens a lambda, and assigns the target a reference to
      -- `two`, before it fails.
      tried root target = do
        _ <- transact do
          i <- typeConstructor root intTy []
          discarded <- openLambda root "x" i
          _ <- emptyRow root >>= closeLambda root discarded.binder discarded.variable
          two <- globalRef root (qualified "two") [] >>= resolveExpr
          assignTerm site target two.term
          throw failure
        identityOfOne root target
    case answered tried, answered identityOfOne of
      Right (Tuple Committed rhs), Right (Tuple Committed clean) -> do
        rhs `shouldEqual` clean
        map globalsOf (toCoreExpr rhs) `shouldEqual` Right (Set.singleton (qualified "one"))
      a, b -> fail (show a <> ", " <> show b)

  it "commits a term whose claim it does not bear out, which the Core type checker refuses" do
    let
      -- `(λ(x : Int). x) true`, claimed at `Int` as the goal is.
      misapplied root _ = do
        i <- typeConstructor root intTy []
        lam <- openLambda root "x" i
        f <- emptyRow root >>= closeLambda root lam.binder lam.variable
        literal root (LitBoolean true) >>= termApply root f
    case answered misapplied of
      Right (Tuple Committed rhs) -> case toCoreExpr rhs of
        Right core -> isRight (verdict core) `shouldEqual` false
        Left _ -> fail "the committed term did not cross the boundary"
      other -> fail (show other)
