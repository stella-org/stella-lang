-- | The kernel's join points.
-- |
-- | Three things are what these cases are for. **A join point is in scope where
-- | its `letjoin` puts it**: its definition and its continuation, and what they
-- | open without an abstraction between. **No term carries a jump under an
-- | abstraction**, whichever builder it reaches litOne by. And **the definition and
-- | the continuation are two scopes**, the parameters bound in the first alone.
module Test.Stella.Compiler.Elaborate.Joins (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Build (openForall, rootScope, typeConstructor)
import Stella.Compiler.Elaborate.BuildTerm (closeJoin, closeLambda, closeLet, jump, literal, openConstraintAbs, openJoin, openLambda, openLet, openTypeAbs, termApply)
import Stella.Compiler.Elaborate.Build as Build
import Stella.Compiler.Elaborate.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Effects (effectsOf)
import Stella.Compiler.Elaborate.Catalog (catalogOf)
import Stella.Compiler.Elaborate.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Elab (Elab, Frame, Outcome(..), SessionEnv, SolverState, initialState, resolveExpr, runElabIn, throw, transact, withFrame)
import Stella.Compiler.Elaborate.Unify (UnifyError(..))
import Stella.Compiler.Elaborate.Handle (Handle, ScopeId(..), SessionId(..))
import Stella.Compiler.Elaborate.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Run (runAttempt)
import Stella.Compiler.Elaborate.Term (XExpr(..), toCoreExpr)
import Stella.Compiler.Elaborate.Type (XType(..))
import Stella.Compiler.Elaborate.View (ConstraintView(..), KindView(..))
import Stella.Compiler.TypedCore (Decl(..), Ident(..), JoinName(..), Literal(..), Module, ModuleName(..), Qualified(..), RowKey(..), Symbol(..), monoScheme)
import Stella.Compiler.TypedCore as Core
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (intTy, primSignature)
import Data.Either (Either(..), isRight)
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (fst)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

xInt :: XType
xInt = XCon intTy []

session :: SessionEnv
session = { catalog: catalogOf [], kinding: kindingOf primSignature, constructors: constructorsOf primSignature, effects: effectsOf primSignature }

site :: Site
site = { context: emptyXContext, origin: InDeclaration (Qualified (ModuleName "Main") (Ident "decl")) }

frame :: Frame
frame = { site, goal: Nothing }

start :: SolverState
start = initialState (SessionId 0) 10

outcomeOf :: forall a. Elab a -> Outcome a
outcomeOf action = fst (runElabIn session start (withFrame frame action))

-- | The term a handle holds, what it is claimed at, and where it was built.
termOf :: Handle -> Elab { term :: XExpr Unit, claimed :: XType, builtIn :: Maybe ScopeId }
termOf handle = resolveExpr handle <#> \o -> { term: o.term, claimed: o.claimed, builtIn: o.builtIn }

refuses :: forall a. Show a => Elab a -> (BuildError -> Aff Unit) -> Aff Unit
refuses action check = case outcomeOf action of
  Broke (BuildRejected err) -> check err
  other -> fail ("the builder did not refuse: " <> show other)

outOfScope :: BuildError -> Aff Unit
outOfScope = case _ of
  JoinOutOfScope _ -> pure unit
  other -> fail ("not JoinOutOfScope: " <> show other)

scopeViolation :: BuildError -> Aff Unit
scopeViolation = case _ of
  ScopeViolation _ -> pure unit
  other -> fail ("not a scope violation: " <> show other)

int :: Handle -> Elab Handle
int scope = typeConstructor scope intTy []

litOne :: Handle -> Elab Handle
litOne scope = literal scope (LitInt 1)

-- | `letjoin j (x : Int) : Int`, opened in the root.
opened
  :: Elab
       { root :: Handle
       , binder :: Handle
       , join :: Handle
       , param :: Handle
       , definitionScope :: Handle
       , bodyScope :: Handle
       }
opened = do
  root <- rootScope
  i <- int root
  o <- openJoin root "j" [ { hint: "x", type: i } ] i
  case o.params of
    [ param ] -> pure { root, binder: o.binder, join: o.join, param, definitionScope: o.definitionScope, bodyScope: o.bodyScope }
    _ -> throw failure

-- | `letjoin j (x : Int) : Int = x in jump j (1)`.
letjoin :: Elab Handle
letjoin = do
  j <- opened
  body <- litOne j.bodyScope >>= \n -> jump j.bodyScope j.join [ n ]
  closeJoin j.root j.binder j.param body

j0 :: JoinName
j0 = JoinName "j#0"

x0 :: Ident
x0 = Ident "x#0"

keyN :: RowKey
keyN = SymbolKey (Symbol "n")

failure :: Diagnostic
failure = EquationFailed site.origin (TypeNotEqual xInt xInt)

spec :: Spec Unit
spec = describe "Elaborate.BuildTerm, join points" do
  describe "a letjoin" do
    it "binds the parameters in the definition and the join point in both, claimed at its result" do
      case outcomeOf (letjoin >>= termOf) of
        Done o -> do
          o.term `shouldEqual`
            ELetJoin unit j0 [ { name: x0, ty: xInt } ] xInt (EVar unit x0) (EJump unit j0 [ ELit unit (LitInt 1) ])
          o.claimed `shouldEqual` xInt
          o.builtIn `shouldEqual` Just (ScopeId 0)
        other -> fail (show other)

    it "lets the definition jump to its own join point" do
      let
        recursive = do
          j <- opened
          again <- jump j.definitionScope j.join [ j.param ]
          body <- litOne j.bodyScope >>= \n -> jump j.bodyScope j.join [ n ]
          closeJoin j.root j.binder again body >>= termOf
      case outcomeOf recursive of
        Done o -> o.term `shouldEqual`
          ELetJoin unit j0 [ { name: x0, ty: xInt } ] xInt (EJump unit j0 [ EVar unit x0 ]) (EJump unit j0 [ ELit unit (LitInt 1) ])
        other -> fail (show other)

    it "keeps the definition and the continuation apart" do
      let
        paramInBody = do
          j <- opened
          closeJoin j.root j.binder j.param j.param
        swapped = do
          j <- opened
          body <- litOne j.bodyScope >>= \n -> jump j.bodyScope j.join [ n ]
          closeJoin j.root j.binder body j.param
      refuses paramInBody scopeViolation
      refuses swapped scopeViolation

    it "names each join point afresh, apart from values" do
      let
        names = do
          j <- opened
          i <- int j.bodyScope
          inner <- openJoin j.bodyScope "j" [] i
          body <- jump inner.bodyScope inner.join []
          definition <- litOne inner.definitionScope
          closeJoin j.bodyScope inner.binder definition body >>= termOf
      case outcomeOf names of
        Done o -> o.term `shouldEqual` ELetJoin unit (JoinName "j#1") [] xInt (ELit unit (LitInt 1)) (EJump unit (JoinName "j#1") [])
        other -> fail (show other)

    it "draws a join point's name again after a rollback" do
      let
        again = do
          root <- rootScope
          i <- int root
          _ <- transact (openJoin root "j" [] i *> throw failure)
          j <- openJoin root "j" [] i
          body <- jump j.bodyScope j.join []
          definition <- litOne j.definitionScope
          closeJoin root j.binder definition body >>= termOf
      case outcomeOf again of
        Done o -> o.term `shouldEqual` ELetJoin unit j0 [] xInt (ELit unit (LitInt 1)) (EJump unit j0 [])
        other -> fail (show other)

  describe "a jump" do
    it "refuses a join point outside its letjoin, and another number of arguments" do
      refuses (opened >>= \j -> litOne j.root >>= \n -> jump j.root j.join [ n ]) outOfScope
      refuses (opened >>= \j -> jump j.bodyScope j.join []) case _ of
        JumpArity _ 1 0 -> pure unit
        other -> fail ("not JumpArity: " <> show other)

    it "refuses a join point across each of the three abstractions, and not across a let or a type's binder" do
      let
        underLambda = do
          j <- opened
          lam <- int j.bodyScope >>= openLambda j.bodyScope "y"
          litOne lam.bodyScope >>= \n -> jump lam.bodyScope j.join [ n ]
        -- `Λ(t : Type)` binds what `forall (t : Type)` does, and empties `Δ`
        -- where the type's binder does not.
        underTypeAbs = do
          j <- opened
          abs <- openTypeAbs j.bodyScope "t" KindType
          litOne abs.bodyScope >>= \n -> jump abs.bodyScope j.join [ n ]
        underConstraintAbs = do
          j <- opened
          e <- Build.emptyRow j.bodyScope
          abs <- openConstraintAbs j.bodyScope (LacksView keyN e)
          litOne abs.bodyScope >>= \n -> jump abs.bodyScope j.join [ n ]
        underForall = do
          j <- opened
          quantified <- openForall j.bodyScope "t" KindType
          litOne quantified.bodyScope >>= \n -> jump quantified.bodyScope j.join [ n ]
        underLet = do
          j <- opened
          bound <- litOne j.bodyScope >>= openLet j.bodyScope "v"
          litOne bound.bodyScope >>= \n -> jump bound.bodyScope j.join [ n ]
      refuses underLambda outOfScope
      refuses underTypeAbs outOfScope
      refuses underConstraintAbs outOfScope
      case outcomeOf underForall, outcomeOf underLet of
        Done _, Done _ -> pure unit
        a, b -> fail ("expected both jumps: " <> show a <> ", " <> show b)

  describe "a term that jumps" do
    it "is not carried under an abstraction, by any builder that takes it" do
      let
        jumped j = litOne j.bodyScope >>= \n -> jump j.bodyScope j.join [ n ]
        asLambdaBody = do
          j <- opened
          t <- jumped j
          lam <- int j.bodyScope >>= openLambda j.bodyScope "y"
          Build.emptyRow j.bodyScope >>= closeLambda j.bodyScope lam.binder t
        asArgument = do
          j <- opened
          t <- jumped j
          lam <- int j.bodyScope >>= openLambda j.bodyScope "y"
          termApply lam.bodyScope lam.variable t
        asLetBody = do
          j <- opened
          t <- jumped j
          bound <- litOne j.bodyScope >>= openLet j.bodyScope "v"
          closeLet j.bodyScope bound.binder t
      refuses asLambdaBody outOfScope
      refuses asArgument outOfScope
      case outcomeOf asLetBody of
        Done _ -> pure unit
        other -> fail ("expected the let: " <> show other)

  describe "a join binder" do
    it "refuses being closed by the operation for another sort, and being left open" do
      refuses (opened >>= \j -> Build.emptyRow j.root >>= closeLambda j.root j.binder j.param) case _ of
        BinderMisuse _ -> pure unit
        other -> fail ("not a binder misuse: " <> show other)
      case fst (runAttempt session (withFrame frame opened) start) of
        Broke (BindersLeftOpen open) -> open `shouldEqual` Set.singleton (ScopeId 1)
        other -> fail ("expected the attempt to halt: " <> show other)

  describe "the Core type checker" do
    it "accepts a letjoin the kernel built" do
      case outcomeOf (letjoin >>= termOf) of
        Done o -> case toCoreExpr o.term of
          Right core -> isRight (verdict (moduleOf core)) `shouldEqual` true
          Left _ -> fail "the letjoin did not cross the boundary"
        other -> fail (show other)

moduleOf :: Core.Expr Unit -> Module Unit
moduleOf value =
  { annotation: unit
  , name: ModuleName "Main"
  , imports: []
  , exports: []
  , decls: [ DeclNonRec unit { name: Ident "joined", scheme: monoScheme (Core.TCon intTy []), value, attributes: [] } ]
  }

verdict :: Module Unit -> Either P.String Unit
verdict m = case declare primSignature m of
  Left e -> Left (show e.error)
  Right _ -> Right unit
