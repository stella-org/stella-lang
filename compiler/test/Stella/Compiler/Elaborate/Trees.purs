-- | The kernel's `case` and decision tree builders.
-- |
-- | Four things are what these cases are for. **An occurrence stands where its
-- | branch put it**: in the tree of its own `case`, under the branch that
-- | established it. **What it stands at is the host's**, read off the data
-- | type's declaration or the row, and waited on only where a solution could
-- | still give it the shape it needs. **A tree reaches the type of its first
-- | leaf**, or a `case` is given its result type. And **what is built passes the
-- | Core type checker**.
module Test.Stella.Compiler.Elaborate.Trees (spec) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Build (emptyRow, rootScope, typeConstructor)
import Stella.Compiler.Elaborate.Build as Build
import Stella.Compiler.Elaborate.BuildTerm (closeLambda, literal, localVariable, openLambda)
import Stella.Compiler.Elaborate.BuildTree (closeBind, closeCase, closeSwitch, guard, leaf, openBind, openCase, openSwitchCtor, openSwitchKey, openSwitchLit, recordField)
import Stella.Compiler.Elaborate.Catalog (EntrySort(..), catalogOf)
import Stella.Compiler.Elaborate.Constructors (constructorsOf)
import Stella.Compiler.Elaborate.Effects (effectsOf)
import Stella.Compiler.Elaborate.Context (Origin(..), XContext, bindTyVar, bindVar, emptyXContext)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..), Diagnostic(..))
import Stella.Compiler.Elaborate.Elab (Cause(..), Elab, Frame, Outcome(..), SessionEnv, SolverState, initialState, issue, resolveExpr, resolveOccurrence, resolveTree, runElabIn, throw, withFrame)
import Stella.Compiler.Elaborate.Handle (Handle, HandleObject(..), ScopeId(..), SessionId(..))
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (kindingOf)
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Run (runAttempt)
import Stella.Compiler.Elaborate.Term (XDecisionTree(..), XExpr(..), toCoreExpr)
import Stella.Compiler.Elaborate.Type (MetaVar, XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Unify (UnifyError(..), emptyContext, freshMeta)
import Stella.Compiler.TypedCore (Decl(..), Ident(..), Literal(..), Module, ModuleName(..), Occurrence(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), TyName(..), TyVar(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore as Core
import Stella.Compiler.TypedCore.Declare (declare)
import Stella.Compiler.TypedCore.Prim (intTy, primSignature, pureFn, recordTy, variantTy)
import Stella.Compiler.TypedCore.Signature (Signature)
import Data.Either (Either(..), either, isRight)
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.TypedCore.VerticalSlice (listDecl)

main :: ModuleName
main = ModuleName "Main"

qualified :: P.String -> Qualified Ident
qualified name = Qualified main (Ident name)

listTy :: Qualified TyName
listTy = Qualified main (TyName "List")

nil :: Qualified Ident
nil = qualified "Nil"

cons :: Qualified Ident
cons = qualified "Cons"

box :: Qualified Ident
box = qualified "Box"

xInt :: XType
xInt = XCon intTy []

xList :: XType -> XType
xList a = XApp (XCon listTy []) a

-- | `data Box a = Box a`, a second data type.
boxDecl :: Decl P.Int
boxDecl = DeclData 2
  { name: TyName "Box"
  , kindVars: []
  , params: [ { name: TyVar "a", kind: Core.KType } ]
  , constructors: [ { name: Ident "Box", tag: 0, fields: [ TVar (TyVar "a") ] } ]
  , isNewtype: false
  , attributes: []
  }

-- | `data Wrap a b = Wrap (forall b. a)`: a field binding a name its data type
-- | also binds.
wrapDecl :: Decl P.Int
wrapDecl = DeclData 3
  { name: TyName "Wrap"
  , kindVars: []
  , params: [ { name: TyVar "a", kind: Core.KType }, { name: TyVar "b", kind: Core.KType } ]
  , constructors: [ { name: Ident "Wrap", tag: 0, fields: [ TForall (TyVar "b") Core.KType (TVar (TyVar "a")) ] } ]
  , isNewtype: false
  , attributes: []
  }

-- | `data Same (a : k) (b : k) = Same`: two parameters at one kind variable.
sameDecl :: Decl P.Int
sameDecl = DeclData 4
  { name: TyName "Same"
  , kindVars: [ Core.KindVar "k" ]
  , params: [ { name: TyVar "a", kind: Core.KVar (Core.KindVar "k") }, { name: TyVar "b", kind: Core.KVar (Core.KindVar "k") } ]
  , constructors: [ { name: Ident "Same", tag: 0, fields: [] } ]
  , isNewtype: false
  , attributes: []
  }

dataModule :: Module P.Int
dataModule = { annotation: 0, name: main, imports: [], exports: [], decls: [ listDecl, boxDecl, wrapDecl, sameDecl ] }

declared :: Either P.String Signature
declared = either (Left <<< show <<< _.error) Right (declare primSignature dataModule)

signature :: Signature
signature = either (const primSignature) identity declared

-- | The signature's constructors, and a name the catalog calls a constructor
-- | that the table does not hold.
session :: SessionEnv
session =
  { catalog: catalogOf
      [ { name: qualified "Ghost", sort: ConstructorEntry, scheme: { kindVars: [], body: xInt }, attributes: [] } ]
  , kinding: kindingOf signature
  , constructors: constructorsOf signature
  , effects: effectsOf signature
  }

keyN :: RowKey
keyN = SymbolKey (Symbol "n")

keyM :: RowKey
keyM = SymbolKey (Symbol "m")

keyK :: RowKey
keyK = SymbolKey (Symbol "k")

r :: TyVar
r = TyVar "r"

-- | `( n : Int, m : Int | tail )`.
nm :: XType -> XType
nm tail = XRowExtend (XRowTypeEntry keyN xInt) (XRowExtend (XRowTypeEntry keyM xInt) tail)

-- | A site binding `r : Row Type` and `b : Type` and, as scrutinees, a list, a
-- | record, a closed variant, a variant with a rigid tail, and `w : Wrap b Int`.
context :: XContext
context =
  bindVar
    ( bindVar
        (bindVar (bindVar (bindTyVar emptyXContext r (XKRow RowType)) (Ident "xs") (xList xInt)) (Ident "rec") (XApp (XCon recordTy []) (nm XRowEmpty)))
        (Ident "var")
        (XApp (XCon variantTy []) (nm XRowEmpty))
    )
    (Ident "rigid")
    (XApp (XCon variantTy []) (nm (XVar r)))
    # \ctx -> bindVar (bindTyVar ctx (TyVar "b") XKType) (Ident "w") (XApp (XApp (XCon (Qualified main (TyName "Wrap")) []) (XVar (TyVar "b"))) xInt)

site :: Site
site = { context, origin: InDeclaration (qualified "decl") }

frame :: Frame
frame = { site, goal: Nothing }

-- | Unsolved metavariables a scrutinee's claim may be headed by or end in:
-- | `?f : Type -> Type`, `?g : Row Type -> Type`, and a row tail `?t`.
withMetas :: { state :: SolverState, f :: MetaVar, g :: MetaVar, t :: MetaVar, same :: MetaVar, differ :: MetaVar }
withMetas =
  let
    fresh kind = freshMeta { kind, scope: { types: Set.empty, kinds: Set.empty } }
    Tuple f m1 = fresh (XKFun XKType XKType) emptyContext
    Tuple g m2 = fresh (XKFun (XKRow RowType) XKType) m1
    Tuple t m3 = fresh (XKRow RowType) m2
    Tuple same m4 = fresh (XKFun XKType (XKFun XKType XKType)) m3
    Tuple differ m5 = fresh (XKFun XKType (XKFun (XKRow RowType) XKType)) m4
  in
    { state: start { tentative = start.tentative { metas = m5 } }, f, g, t, same, differ }

start :: SolverState
start = initialState (SessionId 0) 10

outcomeIn :: forall a. SolverState -> Elab a -> Outcome a
outcomeIn s action = fst (runElabIn session s (withFrame frame action))

outcomeOf :: forall a. Elab a -> Outcome a
outcomeOf = outcomeIn start

refusesIn :: forall a. Show a => SolverState -> Elab a -> (BuildError -> Aff Unit) -> Aff Unit
refusesIn s action check = case outcomeIn s action of
  Broke (BuildRejected err) -> check err
  other -> fail ("the builder did not refuse: " <> show other)

refuses :: forall a. Show a => Elab a -> (BuildError -> Aff Unit) -> Aff Unit
refuses = refusesIn start

is :: P.String -> (BuildError -> P.Boolean) -> BuildError -> Aff Unit
is name test err = if test err then pure unit else fail ("not " <> name <> ": " <> show err)

failure :: Diagnostic
failure = EquationFailed site.origin (TypeNotEqual xInt xInt)

litZero :: Handle -> Elab Handle
litZero scope = literal scope (LitInt 0)

-- | `case (v) of` over the site's variable named, opened in the root.
caseOn :: P.String -> Elab { root :: Handle, binder :: Handle, occurrence :: Handle, treeScope :: Handle }
caseOn name = do
  root <- rootScope
  v <- localVariable root (Ident name)
  opened <- openCase root [ v ]
  case opened.scrutinees of
    [ occurrence ] -> pure { root, binder: opened.binder, occurrence, treeScope: opened.treeScope }
    _ -> throw failure

-- | `case (e) of` over a term claimed at the type given.
caseClaimed :: XType -> Elab { root :: Handle, binder :: Handle, occurrence :: Handle, treeScope :: Handle }
caseClaimed ty = do
  root <- rootScope
  e <- issue (ExprObject { term: EVar unit (Ident "e"), claimed: ty, scope: { kindVars: Set.empty, tyVars: context.tyVars }, builtIn: Just (ScopeId 0), region: Nothing })
  opened <- openCase root [ e ]
  case opened.scrutinees of
    [ occurrence ] -> pure { root, binder: opened.binder, occurrence, treeScope: opened.treeScope }
    _ -> throw failure

occurrenceType :: Handle -> Elab XType
occurrenceType h = resolveOccurrence h <#> _.type

-- | `case (xs) of Nil -> 0; Cons -> bind x = xs!Cons.0 in x`.
lengthish :: Elab { root :: Handle, term :: Handle }
lengthish = do
  c <- caseOn "xs"
  s <- openSwitchCtor c.treeScope c.occurrence [ nil, cons ] false
  case s.branches of
    [ nilBranch, consBranch ] -> case consBranch.fields of
      [ head, _ ] -> do
        nilTree <- litZero nilBranch.scope >>= leaf nilBranch.scope
        bound <- openBind consBranch.scope head "x"
        inner <- leaf bound.bodyScope bound.variable
        consTree <- closeBind consBranch.scope bound.binder inner
        tree <- closeSwitch c.treeScope s.binder [ nilTree, consTree ] Nothing
        term <- closeCase c.root c.binder Nothing tree
        pure { root: c.root, term }
      _ -> throw failure
    _ -> throw failure

spec :: Spec Unit
spec = describe "Elaborate.BuildTree" do
  it "is given a signature declaring List and Box" do
    isRight declared `shouldEqual` true

  describe "a switch on constructors" do
    it "gives each branch its constructor's fields, instantiated at the occurrence's type" do
      let
        fields = do
          c <- caseOn "xs"
          s <- openSwitchCtor c.treeScope c.occurrence [ nil, cons ] false
          traverse (\b -> traverse occurrenceType b.fields) s.branches
      case outcomeOf fields of
        Done types -> types `shouldEqual` [ [], [ xInt, xList xInt ] ]
        other -> fail (show other)

    it "refuses a constructor the table lacks, and one of another data type" do
      refuses (caseOn "xs" >>= \c -> openSwitchCtor c.treeScope c.occurrence [ qualified "Absent" ] false)
        (_ `shouldEqual` UnknownConstructor (qualified "Absent"))
      refuses (caseOn "xs" >>= \c -> openSwitchCtor c.treeScope c.occurrence [ nil, box ] false)
        (_ `shouldEqual` NotAConstructorOf listTy box)
      refuses (caseOn "xs" >>= \c -> openSwitchCtor c.treeScope c.occurrence [ nil, nil ] false)
        ( is "DuplicateBranch" case _ of
            DuplicateBranch _ -> true
            _ -> false
        )

    it "halts where the catalog calls a name a constructor the table lacks" do
      case outcomeOf (caseOn "xs" >>= \c -> openSwitchCtor c.treeScope c.occurrence [ qualified "Ghost" ] false) of
        Broke (ConstructorTableMismatch name) -> name `shouldEqual` qualified "Ghost"
        other -> fail ("expected a host defect: " <> show other)

    it "waits on a head that can become the data type, and refuses one that cannot" do
      case outcomeIn withMetas.state (caseClaimed (XApp (XMeta withMetas.f) xInt) >>= \c -> openSwitchCtor c.treeScope c.occurrence [ nil ] false) of
        Postponed (ExplicitPostponement ms) -> ms `shouldEqual` Set.singleton withMetas.f
        other -> fail ("expected a postponement: " <> show other)
      refusesIn withMetas.state (caseClaimed (XApp (XMeta withMetas.g) XRowEmpty) >>= \c -> openSwitchCtor c.treeScope c.occurrence [ nil ] false)
        ( is "NotOfDataType" case _ of
            NotOfDataType _ -> true
            _ -> false
        )
      refuses (caseClaimed xInt >>= \c -> openSwitchCtor c.treeScope c.occurrence [ nil ] false)
        ( is "NotOfDataType" case _ of
            NotOfDataType _ -> true
            _ -> false
        )

  describe "a case" do
    it "is claimed at its first leaf, and the Core type checker accepts it" do
      case outcomeOf (lengthish >>= \l -> resolveExpr l.term) of
        Done o -> do
          o.claimed `shouldEqual` xInt
          o.term `shouldEqual`
            ECase unit [ EVar unit (Ident "xs") ]
              ( XSwitchCtor (OccScrutinee 0)
                  [ { ctor: nil, tree: XLeaf (ELit unit (LitInt 0)) }
                  , { ctor: cons, tree: XBind (Ident "x#0") (OccField (OccScrutinee 0) cons 0) (XLeaf (EVar unit (Ident "x#0"))) }
                  ]
                  Nothing
              )
        other -> fail (show other)
      let
        underLambda = do
          root <- rootScope
          listInt <- typeConstructor root listTy [] >>= \l -> typeConstructor root intTy [] >>= \i -> Build.applyType root l i
          lam <- openLambda root "xs" listInt
          c <- openCase lam.bodyScope [ lam.variable ]
          case c.scrutinees of
            [ occurrence ] -> do
              s <- openSwitchCtor c.treeScope occurrence [ nil, cons ] false
              case s.branches of
                [ nilBranch, consBranch ] -> case consBranch.fields of
                  [ head, _ ] -> do
                    nilTree <- litZero nilBranch.scope >>= leaf nilBranch.scope
                    bound <- openBind consBranch.scope head "x"
                    consTree <- leaf bound.bodyScope bound.variable >>= closeBind consBranch.scope bound.binder
                    tree <- closeSwitch c.treeScope s.binder [ nilTree, consTree ] Nothing
                    body <- closeCase lam.bodyScope c.binder Nothing tree
                    emptyRow root >>= closeLambda root lam.binder body >>= resolveExpr
                  _ -> throw failure
                _ -> throw failure
            _ -> throw failure
      case outcomeOf underLambda of
        Done o -> case toCoreExpr o.term of
          Right core -> isRight (verdict core) `shouldEqual` true
          Left _ -> fail "the case did not cross the boundary"
        other -> fail (show other)

    it "reaches the type of the first leaf a branch reaches, a branch reaching none passed over" do
      let
        firstLeaf = do
          c <- caseOn "xs"
          s <- openSwitchCtor c.treeScope c.occurrence [ nil, cons ] false
          case s.branches of
            [ nilBranch, consBranch ] -> case consBranch.fields of
              [ _, tail ] -> do
                -- The Nil branch switches on nothing and reaches no leaf.
                empty <- openSwitchCtor nilBranch.scope c.occurrence [] false
                nilTree <- closeSwitch nilBranch.scope empty.binder [] Nothing
                consTree <- openBind consBranch.scope tail "t" >>= \b -> leaf b.bodyScope b.variable >>= closeBind consBranch.scope b.binder
                tree <- closeSwitch c.treeScope s.binder [ nilTree, consTree ] Nothing
                resolveTree tree <#> _.inferred
              _ -> throw failure
            _ -> throw failure
      case outcomeOf firstLeaf of
        Done inferred -> inferred `shouldEqual` Just (xList xInt)
        other -> fail (show other)

    it "needs a result type over a tree that reaches no leaf" do
      let
        empty result = do
          c <- caseOn "xs"
          s <- openSwitchCtor c.treeScope c.occurrence [] false
          tree <- closeSwitch c.treeScope s.binder [] Nothing
          given <- result c.root
          closeCase c.root c.binder given tree >>= resolveExpr
      refuses (empty \_ -> pure Nothing)
        ( is "NoLeaf" case _ of
            NoLeaf _ -> true
            _ -> false
        )
      case outcomeOf (empty \root -> Just <$> typeConstructor root intTy []) of
        Done o -> o.claimed `shouldEqual` xInt
        other -> fail (show other)

    it "reaches through a guard the first of its two trees that reaches a leaf" do
      let
        guarded = do
          c <- caseOn "xs"
          condition <- literal c.treeScope (LitBoolean true)
          empty <- openSwitchCtor c.treeScope c.occurrence [] false
          nothing <- closeSwitch c.treeScope empty.binder [] Nothing
          something <- litZero c.treeScope >>= leaf c.treeScope
          guard c.treeScope condition nothing something >>= resolveTree <#> _.inferred
      case outcomeOf guarded of
        Done inferred -> inferred `shouldEqual` Just xInt
        other -> fail (show other)

  describe "an occurrence" do
    it "is read only under the branch that established it, and only in its own case's tree" do
      let
        inSibling = do
          c <- caseOn "xs"
          s <- openSwitchCtor c.treeScope c.occurrence [ nil, cons ] false
          case s.branches of
            [ nilBranch, consBranch ] -> case consBranch.fields of
              [ head, _ ] -> openBind nilBranch.scope head "x"
              _ -> throw failure
            _ -> throw failure
        inInnerCase = do
          c <- caseOn "xs"
          v <- localVariable c.treeScope (Ident "xs")
          inner <- openCase c.treeScope [ v ]
          openBind inner.treeScope c.occurrence "x"
      refuses inSibling
        ( is "ScopeViolation" case _ of
            ScopeViolation _ -> true
            _ -> false
        )
      refuses inInnerCase
        ( is "OccurrenceOfAnotherCase" case _ of
            OccurrenceOfAnotherCase _ -> true
            _ -> false
        )

    it "is taken apart only in a scope standing in a tree" do
      refuses (rootScope >>= \root -> litZero root >>= leaf root)
        ( is "NotATreeScope" case _ of
            NotATreeScope _ -> true
            _ -> false
        )

  describe "recordField" do
    it "reads a record's field at the payload its row carries" do
      case outcomeOf (caseOn "rec" >>= \c -> recordField c.treeScope c.occurrence keyN >>= occurrenceType) of
        Done ty -> ty `shouldEqual` xInt
        other -> fail (show other)

    it "refuses a key the row does not carry, and what is not a record" do
      refuses (caseOn "rec" >>= \c -> recordField c.treeScope c.occurrence keyK)
        ( is "FieldAbsent" case _ of
            FieldAbsent _ _ -> true
            _ -> false
        )
      refuses (caseOn "xs" >>= \c -> recordField c.treeScope c.occurrence keyN)
        ( is "NotARecord" case _ of
            NotARecord _ -> true
            _ -> false
        )

  describe "a switch on keys" do
    it "gives each branch its key's payload, and the default the residual variant" do
      let
        opened = do
          c <- caseOn "var"
          s <- openSwitchKey c.treeScope c.occurrence [ keyN ] true
          payloads <- traverse (\b -> occurrenceType b.payload) s.branches
          residual <- traverse (\f -> occurrenceType f.residual) s.fallback
          pure (Tuple payloads residual)
      case outcomeOf opened of
        Done (Tuple payloads residual) -> do
          payloads `shouldEqual` [ xInt ]
          residual `shouldEqual` Just (XApp (XCon variantTy []) (XRowExtend (XRowTypeEntry keyM xInt) XRowEmpty))
        other -> fail (show other)

    it "refuses an ill-formed key over a flexible tail rather than waiting on it" do
      let
        negative = PositionKey (-1)
        illKinded = is "IllKinded" case _ of
          IllKinded _ -> true
          _ -> false
        overTail wrap = caseClaimed (XApp (XCon wrap []) (nm (XMeta withMetas.t)))
      refusesIn withMetas.state (overTail recordTy >>= \c -> recordField c.treeScope c.occurrence negative) illKinded
      refusesIn withMetas.state (overTail variantTy >>= \c -> openSwitchKey c.treeScope c.occurrence [ negative ] true) illKinded

    it "waits on a flexible tail for a key it lacks, and refuses one a closed or rigid row lacks" do
      case outcomeIn withMetas.state (caseClaimed (XApp (XCon variantTy []) (nm (XMeta withMetas.t))) >>= \c -> openSwitchKey c.treeScope c.occurrence [ keyK ] true) of
        Postponed (ExplicitPostponement ms) -> ms `shouldEqual` Set.singleton withMetas.t
        other -> fail ("expected a postponement: " <> show other)
      let
        fieldAbsent = is "FieldAbsent" case _ of
          FieldAbsent _ _ -> true
          _ -> false
      refuses (caseOn "var" >>= \c -> openSwitchKey c.treeScope c.occurrence [ keyK ] true) fieldAbsent
      refuses (caseOn "rigid" >>= \c -> openSwitchKey c.treeScope c.occurrence [ keyK ] true) fieldAbsent

  describe "closing a switch" do
    let
      onLiterals = do
        c <- caseOn "xs"
        s <- openSwitchLit c.treeScope c.occurrence [ LitInt 1, LitInt 2 ]
        pure { c, s }

    it "needs a tree for each branch, and the default a switch on literals always has" do
      let
        closedWith trees fallback = do
          o <- onLiterals
          ts <- traverse (\scope -> litZero scope >>= leaf scope) (trees o.s)
          f <- traverse (\scope -> litZero scope >>= leaf scope) (fallback o.s)
          closeSwitch o.c.treeScope o.s.binder ts f
      refuses (closedWith (\s -> Array.take 1 s.branches) (\s -> Just s.fallback))
        ( is "BranchCount" case _ of
            BranchCount _ 2 1 -> true
            _ -> false
        )
      refuses (closedWith _.branches (\_ -> Nothing))
        ( is "DefaultMismatch" case _ of
            DefaultMismatch _ -> true
            _ -> false
        )
      case outcomeOf (closedWith _.branches (\s -> Just s.fallback)) of
        Done _ -> pure unit
        other -> fail (show other)

    it "refuses a branch's tree built in another branch" do
      let
        crossed = do
          o <- onLiterals
          case o.s.branches of
            [ first, _ ] -> do
              t1 <- litZero first >>= leaf first
              f <- litZero o.s.fallback >>= leaf o.s.fallback
              closeSwitch o.c.treeScope o.s.binder [ t1, t1 ] (Just f)
            _ -> throw failure
      refuses crossed
        ( is "ScopeViolation" case _ of
            ScopeViolation _ -> true
            _ -> false
        )

  describe "an instantiation, a tree, and a head" do
    it "instantiates a field's binder named like a parameter without capturing another argument" do
      let
        fields = do
          c <- caseOn "w"
          s <- openSwitchCtor c.treeScope c.occurrence [ qualified "Wrap" ] false
          traverse (\b -> traverse occurrenceType b.fields) s.branches
      case outcomeOf fields of
        Done types -> types `shouldEqual` [ [ XForall (TyVar "b#0") XKType (XVar (TyVar "b")) ] ]
        other -> fail (show other)

    it "refuses a tree of an enclosing case as an inner case's" do
      let
        inner close = do
          c <- caseOn "xs"
          outerTree <- litZero c.treeScope >>= leaf c.treeScope
          v <- localVariable c.treeScope (Ident "xs")
          opened <- openCase c.treeScope [ v ]
          close c.treeScope opened outerTree
        treeOfAnotherCase = is "TreeOfAnotherCase" case _ of
          TreeOfAnotherCase _ -> true
          _ -> false
      refuses (inner \scope opened t -> closeCase scope opened.binder Nothing t) treeOfAnotherCase
      refuses
        ( inner \_ opened t -> do
            condition <- literal opened.treeScope (LitBoolean true)
            guard opened.treeScope condition t t
        )
        treeOfAnotherCase

    it "holds a kind variable of the data type to one kind wherever it occurs" do
      let
        headedBy m = caseClaimed (XApp (XApp (XMeta m) xInt) xInt) >>= \c -> openSwitchCtor c.treeScope c.occurrence [ qualified "Same" ] false
      case outcomeIn withMetas.state (headedBy withMetas.same) of
        Postponed (ExplicitPostponement ms) -> ms `shouldEqual` Set.singleton withMetas.same
        other -> fail ("expected a postponement: " <> show other)
      refusesIn withMetas.state (headedBy withMetas.differ)
        ( is "NotOfDataType" case _ of
            NotOfDataType _ -> true
            _ -> false
        )

  describe "the binders of a tree" do
    it "refuse being closed by the operation for another sort, and being left open" do
      refuses (caseOn "xs" >>= \c -> openSwitchLit c.treeScope c.occurrence [] >>= \s -> litZero s.fallback >>= leaf s.fallback >>= closeBind c.treeScope s.binder)
        ( is "BinderMisuse" case _ of
            BinderMisuse _ -> true
            _ -> false
        )
      case fst (runAttempt session (withFrame frame (caseOn "xs")) start) of
        Broke (BindersLeftOpen open) -> open `shouldEqual` Set.singleton (ScopeId 1)
        other -> fail ("expected the attempt to halt: " <> show other)

-- | A module importing `List` and declaring a function taking a list apart.
verdict :: Core.Expr Unit -> Either P.String Unit
verdict value = case declare signature m of
  Left e -> Left (show e.error)
  Right _ -> Right unit
  where
  m =
    { annotation: unit
    , name: ModuleName "User"
    , imports: [ main ]
    , exports: []
    , decls:
        [ DeclNonRec unit
            { name: Ident "first"
            , scheme: monoScheme (pureFn (TApp (TCon listTy []) (TCon intTy [])) (TCon intTy []))
            , value
            , attributes: []
            }
        ]
    }
