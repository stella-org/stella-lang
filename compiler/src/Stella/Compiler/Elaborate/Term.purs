-- | Terms of Core⁺, that is, Core's terms with unresolved holes added.
-- |
-- | Core has no metavariables (D12), so these are a separate type rather than a
-- | widening of `Stella.Compiler.TypedCore.Term`: every position Core writes a
-- | type or a kind in holds an `XType` or an `XKind` here, and two forms exist
-- | that Core has none of — a term metavariable `?m`, and a typed hole.
-- |
-- | A synthesis goal `⟨ τ by f ⟩` is not among them. It is what elaboration is
-- | handed, and it is taken apart where it is met into a term metavariable in
-- | the term and a `Synth ?m τ f` job beside it, so the term holds the `?m`
-- | alone.
-- |
-- | Nothing here reaches the Core type checker except through `toCore`, which
-- | refuses while anything unresolved remains.
module Stella.Compiler.Elaborate.Term
  ( TermMetaVar(..)
  , XExpr(..)
  , XParam
  , XBinding
  , XTyBinder
  , XHandler
  , XLayout
  , XCell
  , XReturnClause
  , XOpClause(..)
  , XDecisionTree(..)
  , XCtorBranch
  , XLitBranch
  , XKeyBranch
  , Residue(..)
  , FreeVars
  , MetasOfTerm
  , xExprAnnotation
  , fromCoreExpr
  , toCoreExpr
  , freeVarsOf
  , metasOfTerm
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Kind (KindMetaVar, XKind(..), fromCoreKind, kindMetasOf, kindVarsOf)
import Stella.Compiler.Elaborate.Type (MetaVar, XConstraint(..), XRowEntry(..), XType(..), fromCore, fromCoreConstraint, fromCoreEntry, freeKindVars, freeRigids, kindMetasOfType, metasOf)
import Stella.Compiler.TypedCore (Constraint(..), DecisionTree(..), Expr(..), Ident, JoinName, Kind(..), KindVar, Literal, OpClause(..), OpName, Occurrence, Qualified, RowEntry(..), RowKey, TyVar, Type(..))
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Foldable (foldMap)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)

-- | A term metavariable of `Ψ`. What it stands at and what it may mention live
-- | in the metavariable context, not here.
newtype TermMetaVar = TermMetaVar P.Int

-- | A Core⁺ term. Each constructor but the last two mirrors the Core form of the
-- | same name ([Term](../TypedCore/Term.purs)).
data XExpr a
  = EVar a Ident
  | EGlobal a (Qualified Ident) (P.Array XKind)
  | ELit a Literal
  | ELam a Ident XType (XExpr a)
  | EApp a (XExpr a) (XExpr a)
  | ETyLam a TyVar XKind (XExpr a)
  | ETyApp a (XExpr a) XType
  | EConstraintLam a XConstraint (XExpr a)
  | EConstraintApp a (XExpr a)
  | ELet a Ident XType (XExpr a) (XExpr a)
  | ELetRec a (P.Array (XBinding a)) (XExpr a)
  | ECase a (P.Array (XExpr a)) (XDecisionTree a)
  | ELetJoin a JoinName (P.Array XParam) XType (XExpr a) (XExpr a)
  | EJump a JoinName (P.Array (XExpr a))
  | ERecordEmpty a
  | ERecordExtend a RowKey (XExpr a) (XExpr a)
  | ERecordSelect a RowKey (XExpr a)
  | ERecordRestrict a RowKey (XExpr a)
  | ERecordUpdate a RowKey (XExpr a) (XExpr a)
  | ERecordMerge a (XExpr a) (XExpr a)
  | EVariantInject a RowKey (XExpr a)
  | EVariantWeaken a RowKey XType (XExpr a)
  | EVariantAbsurd a XType (XExpr a)
  | EPerform a RowKey OpName (P.Array XType) (XExpr a)
  | EHandle a (XExpr a) (XHandler a) (P.Array (XExpr a))
  | EReadCell a RowKey
  | EWriteCell a RowKey (XExpr a)
  | EOpenEff a XType (XExpr a)
  -- | `?m`, a term to be supplied later.
  | ETermMeta a TermMetaVar
  -- | `hole τ`, a place the author left open. It is reported, never filled.
  | EHole a XType

type XParam =
  { name :: Ident
  , ty :: XType
  }

type XBinding a =
  { name :: Ident
  , ty :: XType
  , value :: XExpr a
  }

type XTyBinder =
  { name :: TyVar
  , kind :: XKind
  }

type XHandler a =
  { element :: XRowEntry
  , cells :: Maybe XLayout
  , returnClause :: XReturnClause a
  , opClauses :: P.Array (XOpClause a)
  }

type XLayout =
  { var :: TyVar
  , cells :: P.Array XCell
  }

type XCell =
  { key :: RowKey
  , ty :: XType
  }

type XReturnClause a =
  { binder :: Ident
  , ty :: XType
  , body :: XExpr a
  }

data XOpClause a
  = XFullClause
      { op :: OpName
      , tyBinders :: P.Array XTyBinder
      , argBinder :: XParam
      , contBinder :: XParam
      , body :: XExpr a
      }
  | XFastClause
      { op :: OpName
      , tyBinders :: P.Array XTyBinder
      , argBinder :: XParam
      , body :: XExpr a
      }

data XDecisionTree a
  = XLeaf (XExpr a)
  | XBind Ident Occurrence (XDecisionTree a)
  | XSwitchCtor Occurrence (P.Array (XCtorBranch a)) (Maybe (XDecisionTree a))
  | XSwitchLit Occurrence (P.Array (XLitBranch a)) (XDecisionTree a)
  | XSwitchKey Occurrence (P.Array (XKeyBranch a)) (Maybe (XDecisionTree a))
  | XGuard (XExpr a) (XDecisionTree a) (XDecisionTree a)

type XCtorBranch a =
  { ctor :: Qualified Ident
  , tree :: XDecisionTree a
  }

type XLitBranch a =
  { lit :: Literal
  , tree :: XDecisionTree a
  }

type XKeyBranch a =
  { key :: RowKey
  , tree :: XDecisionTree a
  }

-- | Something unresolved that keeps a term from being Core.
-- |
-- | Each carries the annotation of the nearest node that has one: a type, a
-- | kind, a decision tree, and a handler carry none, so what stands in one is
-- | reported at the term enclosing it.
data Residue a
  = ResidualTypeMeta a MetaVar
  | ResidualKindMeta a KindMetaVar
  | ResidualTermMeta a TermMetaVar
  | ResidualHole a XType

-- | The variables a term mentions free, one set per class.
-- |
-- | `joins` are the join points a `jump` names that no `letjoin` inside the term
-- | binds. Kind variables have no binder in a term (D3), so every one is free.
type FreeVars =
  { values :: Set Ident
  , types :: Set TyVar
  , kinds :: Set KindVar
  , joins :: Set JoinName
  }

-- | The metavariables a term mentions, one set per class.
type MetasOfTerm =
  { terms :: Set TermMetaVar
  , types :: Set MetaVar
  , kinds :: Set KindMetaVar
  }

xExprAnnotation :: forall a. XExpr a -> a
xExprAnnotation = case _ of
  EVar a _ -> a
  EGlobal a _ _ -> a
  ELit a _ -> a
  ELam a _ _ _ -> a
  EApp a _ _ -> a
  ETyLam a _ _ _ -> a
  ETyApp a _ _ -> a
  EConstraintLam a _ _ -> a
  EConstraintApp a _ -> a
  ELet a _ _ _ _ -> a
  ELetRec a _ _ -> a
  ECase a _ _ -> a
  ELetJoin a _ _ _ _ _ -> a
  EJump a _ _ -> a
  ERecordEmpty a -> a
  ERecordExtend a _ _ _ -> a
  ERecordSelect a _ _ -> a
  ERecordRestrict a _ _ -> a
  ERecordUpdate a _ _ _ -> a
  ERecordMerge a _ _ -> a
  EVariantInject a _ _ -> a
  EVariantWeaken a _ _ _ -> a
  EVariantAbsurd a _ _ -> a
  EPerform a _ _ _ _ -> a
  EHandle a _ _ _ -> a
  EReadCell a _ -> a
  EWriteCell a _ _ -> a
  EOpenEff a _ _ -> a
  ETermMeta a _ -> a
  EHole a _ -> a

-- | A Core term as a Core⁺ one, which holds nothing unresolved.
fromCoreExpr :: forall a. Expr a -> XExpr a
fromCoreExpr = case _ of
  Var a x -> EVar a x
  Global a name kinds -> EGlobal a name (map fromCoreKind kinds)
  Lit a literal -> ELit a literal
  Lam a x ty body -> ELam a x (fromCore ty) (fromCoreExpr body)
  App a f x -> EApp a (fromCoreExpr f) (fromCoreExpr x)
  TyLam a name kind body -> ETyLam a name (fromCoreKind kind) (fromCoreExpr body)
  TyApp a e ty -> ETyApp a (fromCoreExpr e) (fromCore ty)
  ConstraintLam a c body -> EConstraintLam a (fromCoreConstraint c) (fromCoreExpr body)
  ConstraintApp a e -> EConstraintApp a (fromCoreExpr e)
  Let a x ty value body -> ELet a x (fromCore ty) (fromCoreExpr value) (fromCoreExpr body)
  LetRec a bindings body -> ELetRec a (map binding bindings) (fromCoreExpr body)
  Case a scrutinees dt -> ECase a (map fromCoreExpr scrutinees) (fromCoreTree dt)
  LetJoin a j params result value body ->
    ELetJoin a j (map param params) (fromCore result) (fromCoreExpr value) (fromCoreExpr body)
  Jump a j args -> EJump a j (map fromCoreExpr args)
  RecordEmpty a -> ERecordEmpty a
  RecordExtend a key value rest -> ERecordExtend a key (fromCoreExpr value) (fromCoreExpr rest)
  RecordSelect a key e -> ERecordSelect a key (fromCoreExpr e)
  RecordRestrict a key e -> ERecordRestrict a key (fromCoreExpr e)
  RecordUpdate a key rec value -> ERecordUpdate a key (fromCoreExpr rec) (fromCoreExpr value)
  RecordMerge a left right -> ERecordMerge a (fromCoreExpr left) (fromCoreExpr right)
  VariantInject a key value -> EVariantInject a key (fromCoreExpr value)
  VariantWeaken a key ty e -> EVariantWeaken a key (fromCore ty) (fromCoreExpr e)
  VariantAbsurd a ty e -> EVariantAbsurd a (fromCore ty) (fromCoreExpr e)
  Perform a key op tyArgs arg -> EPerform a key op (map fromCore tyArgs) (fromCoreExpr arg)
  Handle a body handler initial ->
    EHandle a (fromCoreExpr body) (fromCoreHandler handler) (map fromCoreExpr initial)
  ReadCell a key -> EReadCell a key
  WriteCell a key value -> EWriteCell a key (fromCoreExpr value)
  OpenEff a row e -> EOpenEff a (fromCore row) (fromCoreExpr e)
  where
  param p = { name: p.name, ty: fromCore p.ty }
  binding b = { name: b.name, ty: fromCore b.ty, value: fromCoreExpr b.value }

  fromCoreHandler h =
    { element: fromCoreEntry h.element
    , cells: map (\l -> { var: l.var, cells: map (\c -> { key: c.key, ty: fromCore c.ty }) l.cells }) h.cells
    , returnClause: { binder: h.returnClause.binder, ty: fromCore h.returnClause.ty, body: fromCoreExpr h.returnClause.body }
    , opClauses: map clause h.opClauses
    }

  clause = case _ of
    FullClause c -> XFullClause
      { op: c.op
      , tyBinders: map tyBinder c.tyBinders
      , argBinder: param c.argBinder
      , contBinder: param c.contBinder
      , body: fromCoreExpr c.body
      }
    FastClause c -> XFastClause
      { op: c.op
      , tyBinders: map tyBinder c.tyBinders
      , argBinder: param c.argBinder
      , body: fromCoreExpr c.body
      }

  tyBinder b = { name: b.name, kind: fromCoreKind b.kind }

  fromCoreTree = case _ of
    Leaf e -> XLeaf (fromCoreExpr e)
    Bind x o dt -> XBind x o (fromCoreTree dt)
    SwitchCtor o branches d ->
      XSwitchCtor o (map (\b -> { ctor: b.ctor, tree: fromCoreTree b.tree }) branches) (map fromCoreTree d)
    SwitchLit o branches d ->
      XSwitchLit o (map (\b -> { lit: b.lit, tree: fromCoreTree b.tree }) branches) (fromCoreTree d)
    SwitchKey o branches d ->
      XSwitchKey o (map (\b -> { key: b.key, tree: fromCoreTree b.tree }) branches) (map fromCoreTree d)
    Guard e yes no -> XGuard (fromCoreExpr e) (fromCoreTree yes) (fromCoreTree no)

-- | The elaboration boundary: a term with nothing unresolved, as Core.
-- |
-- | **Every residue is reported, not only the first**, in the order a
-- | depth-first walk meets them: a node's own types and kinds before its
-- | subterms, and subterms in the order the constructor writes them. The caller
-- | zonks first, so a metavariable that is solved but not substituted is a
-- | residue like any other.
toCoreExpr :: forall a. XExpr a -> Either (NonEmptyArray (Residue a)) (Expr a)
toCoreExpr e = case convExpr e of
  Conv result -> result

-- | A conversion that keeps every residue it meets, as an applicative: where
-- | both sides met some, the residues are concatenated left to right, and a
-- | value exists only where neither side met one.
newtype Conv r b = Conv (Either (NonEmptyArray r) b)

instance Functor (Conv r) where
  map f (Conv v) = Conv (map f v)

instance Apply (Conv r) where
  apply (Conv f) (Conv v) = Conv case f, v of
    Left r1, Left r2 -> Left (r1 <> r2)
    Left r1, Right _ -> Left r1
    Right _, Left r2 -> Left r2
    Right g, Right x -> Right (g x)

instance Applicative (Conv r) where
  pure b = Conv (Right b)

residue :: forall r b. r -> Conv r b
residue r = Conv (Left (NonEmptyArray.singleton r))

convExpr :: forall a. XExpr a -> Conv (Residue a) (Expr a)
convExpr = case _ of
  EVar a x -> pure (Var a x)
  EGlobal a name kinds -> Global a name <$> traverse (convKind a) kinds
  ELit a literal -> pure (Lit a literal)
  ELam a x ty body -> Lam a x <$> convType a ty <*> convExpr body
  EApp a f x -> App a <$> convExpr f <*> convExpr x
  ETyLam a name kind body -> TyLam a name <$> convKind a kind <*> convExpr body
  ETyApp a e ty -> (\t e' -> TyApp a e' t) <$> convType a ty <*> convExpr e
  EConstraintLam a c body -> ConstraintLam a <$> convConstraint a c <*> convExpr body
  EConstraintApp a e -> ConstraintApp a <$> convExpr e
  ELet a x ty value body -> Let a x <$> convType a ty <*> convExpr value <*> convExpr body
  ELetRec a bindings body -> LetRec a <$> traverse (convBinding a) bindings <*> convExpr body
  ECase a scrutinees dt -> Case a <$> traverse convExpr scrutinees <*> convTree a dt
  ELetJoin a j params result value body ->
    LetJoin a j <$> traverse (convParam a) params <*> convType a result <*> convExpr value <*> convExpr body
  EJump a j args -> Jump a j <$> traverse convExpr args
  ERecordEmpty a -> pure (RecordEmpty a)
  ERecordExtend a key value rest -> RecordExtend a key <$> convExpr value <*> convExpr rest
  ERecordSelect a key e -> RecordSelect a key <$> convExpr e
  ERecordRestrict a key e -> RecordRestrict a key <$> convExpr e
  ERecordUpdate a key rec value -> RecordUpdate a key <$> convExpr rec <*> convExpr value
  ERecordMerge a left right -> RecordMerge a <$> convExpr left <*> convExpr right
  EVariantInject a key value -> VariantInject a key <$> convExpr value
  EVariantWeaken a key ty e -> VariantWeaken a key <$> convType a ty <*> convExpr e
  EVariantAbsurd a ty e -> VariantAbsurd a <$> convType a ty <*> convExpr e
  EPerform a key op tyArgs arg -> Perform a key op <$> traverse (convType a) tyArgs <*> convExpr arg
  EHandle a body handler initial -> convHandle a body handler initial
  EReadCell a key -> pure (ReadCell a key)
  EWriteCell a key value -> WriteCell a key <$> convExpr value
  EOpenEff a row e -> OpenEff a <$> convType a row <*> convExpr e
  ETermMeta a m -> residue (ResidualTermMeta a m)
  EHole a ty -> convType a ty *> residue (ResidualHole a ty)

convParam :: forall a. a -> XParam -> Conv (Residue a) { name :: Ident, ty :: Type }
convParam at p = { name: p.name, ty: _ } <$> convType at p.ty

convBinding :: forall a. a -> XBinding a -> Conv (Residue a) { name :: Ident, ty :: Type, value :: Expr a }
convBinding at b = { name: b.name, ty: _, value: _ } <$> convType at b.ty <*> convExpr b.value

-- | The element and the layout are the node's own types, so they come before the
-- | handled computation; the clauses are subterms of the handler and come after
-- | it, and the initial values last, as the constructor writes them.
convHandle :: forall a. a -> XExpr a -> XHandler a -> P.Array (XExpr a) -> Conv (Residue a) (Expr a)
convHandle at handled h initial =
  ( \element cells computation ret opClauses initialValues ->
      Handle at computation { element, cells, returnClause: ret, opClauses } initialValues
  )
    <$> convEntry at h.element
    <*> traverse layout h.cells
    <*> convExpr handled
    <*> returnClause h.returnClause
    <*> traverse clause h.opClauses
    <*> traverse convExpr initial
  where
  layout l = { var: l.var, cells: _ } <$> traverse (\c -> { key: c.key, ty: _ } <$> convType at c.ty) l.cells

  returnClause r = { binder: r.binder, ty: _, body: _ } <$> convType at r.ty <*> convExpr r.body

  clause = case _ of
    XFullClause c ->
      (\tyBinders argBinder contBinder body -> FullClause { op: c.op, tyBinders, argBinder, contBinder, body })
        <$> traverse tyBinder c.tyBinders
        <*> convParam at c.argBinder
        <*> convParam at c.contBinder
        <*> convExpr c.body
    XFastClause c ->
      (\tyBinders argBinder body -> FastClause { op: c.op, tyBinders, argBinder, body })
        <$> traverse tyBinder c.tyBinders
        <*> convParam at c.argBinder
        <*> convExpr c.body

  tyBinder b = { name: b.name, kind: _ } <$> convKind at b.kind

convTree :: forall a. a -> XDecisionTree a -> Conv (Residue a) (DecisionTree a)
convTree at = case _ of
  XLeaf e -> Leaf <$> convExpr e
  XBind x o dt -> Bind x o <$> convTree at dt
  XSwitchCtor o branches d ->
    SwitchCtor o <$> traverse (\b -> { ctor: b.ctor, tree: _ } <$> convTree at b.tree) branches <*> traverse (convTree at) d
  XSwitchLit o branches d ->
    SwitchLit o <$> traverse (\b -> { lit: b.lit, tree: _ } <$> convTree at b.tree) branches <*> convTree at d
  XSwitchKey o branches d ->
    SwitchKey o <$> traverse (\b -> { key: b.key, tree: _ } <$> convTree at b.tree) branches <*> traverse (convTree at) d
  XGuard e yes no -> Guard <$> convExpr e <*> convTree at yes <*> convTree at no

convType :: forall a. a -> XType -> Conv (Residue a) Type
convType at = case _ of
  XVar a -> pure (TVar a)
  XMeta m -> residue (ResidualTypeMeta at m)
  XCon n kinds -> TCon n <$> traverse (convKind at) kinds
  XApp f x -> TApp <$> convType at f <*> convType at x
  XForall a k body -> TForall a <$> convKind at k <*> convType at body
  XConstrained c body -> TConstrained <$> convConstraint at c <*> convType at body
  XRowEmpty -> pure TRowEmpty
  XRowExtend entry rest -> TRowExtend <$> convEntry at entry <*> convType at rest
  XRowUnion l r -> TRowUnion <$> convType at l <*> convType at r

convEntry :: forall a. a -> XRowEntry -> Conv (Residue a) RowEntry
convEntry at = case _ of
  XRowTypeEntry k ty -> RowTypeEntry k <$> convType at ty
  XRowEffectEntry e args -> RowEffectEntry e <$> traverse (convType at) args
  XRowLabelledEffectEntry s e args -> RowLabelledEffectEntry s e <$> traverse (convType at) args
  XRowRegionEntry var cells -> RowRegionEntry <$> convType at var <*> convType at cells

convConstraint :: forall a. a -> XConstraint -> Conv (Residue a) Constraint
convConstraint at = case _ of
  XLacks key row -> Lacks key <$> convType at row
  XDisjoint l r -> Disjoint <$> convType at l <*> convType at r

convKind :: forall a. a -> XKind -> Conv (Residue a) Kind
convKind at = case _ of
  XKVar k -> pure (KVar k)
  XKMeta m -> residue (ResidualKindMeta at m)
  XKType -> pure KType
  XKEffect -> pure KEffect
  XKRow e -> pure (KRow e)
  XKFun a b -> KFun <$> convKind at a <*> convKind at b

-- | The variables a term mentions free, with every binder of every class taken
-- | into account.
-- |
-- | Value binders are `λ`, `let` (over its body), `letrec` (over every
-- | right-hand side and the body), a decision tree's `bind` (over the tree
-- | beneath it), and a handler clause's argument and continuation, and its
-- | return binder. Type binders are `Λ`, a `forall` inside a type, a handler's
-- | region variable (over its operation clauses, annotations included), and a
-- | clause's own type parameters. A `letjoin` binds its join point over both its
-- | definition and its body, and its parameters over the definition alone.
freeVarsOf :: forall a. XExpr a -> FreeVars
freeVarsOf = case _ of
  EVar _ x -> valueVar x
  EGlobal _ _ kinds -> foldMap kindsOf kinds
  ELit _ _ -> none
  ELam _ x ty body -> typeVars ty <> withoutValue x (freeVarsOf body)
  EApp _ f x -> freeVarsOf f <> freeVarsOf x
  ETyLam _ name kind body -> kindsOf kind <> withoutType name (freeVarsOf body)
  ETyApp _ e ty -> freeVarsOf e <> typeVars ty
  EConstraintLam _ c body -> constraintVars c <> freeVarsOf body
  EConstraintApp _ e -> freeVarsOf e
  ELet _ x ty v body -> typeVars ty <> freeVarsOf v <> withoutValue x (freeVarsOf body)
  ELetRec _ bindings body ->
    withoutValues (map _.name bindings)
      (foldMap (\b -> typeVars b.ty <> freeVarsOf b.value) bindings <> freeVarsOf body)
  ECase _ scrutinees dt -> foldMap freeVarsOf scrutinees <> treeVars dt
  ELetJoin _ j params result v body ->
    withoutJoin j
      ( foldMap (typeVars <<< _.ty) params
          <> typeVars result
          <> withoutValues (map _.name params) (freeVarsOf v)
          <> freeVarsOf body
      )
  EJump _ j args -> joinVar j <> foldMap freeVarsOf args
  ERecordEmpty _ -> none
  ERecordExtend _ _ v rest -> freeVarsOf v <> freeVarsOf rest
  ERecordSelect _ _ e -> freeVarsOf e
  ERecordRestrict _ _ e -> freeVarsOf e
  ERecordUpdate _ _ rec v -> freeVarsOf rec <> freeVarsOf v
  ERecordMerge _ l r -> freeVarsOf l <> freeVarsOf r
  EVariantInject _ _ v -> freeVarsOf v
  EVariantWeaken _ _ ty e -> typeVars ty <> freeVarsOf e
  EVariantAbsurd _ ty e -> typeVars ty <> freeVarsOf e
  EPerform _ _ _ tyArgs arg -> foldMap typeVars tyArgs <> freeVarsOf arg
  EHandle _ body h initial -> freeVarsOf body <> handlerVars h <> foldMap freeVarsOf initial
  EReadCell _ _ -> none
  EWriteCell _ _ v -> freeVarsOf v
  EOpenEff _ row e -> typeVars row <> freeVarsOf e
  ETermMeta _ _ -> none
  EHole _ ty -> typeVars ty
  where
  treeVars = case _ of
    XLeaf e -> freeVarsOf e
    XBind x _ dt -> withoutValue x (treeVars dt)
    XSwitchCtor _ branches d -> foldMap (treeVars <<< _.tree) branches <> foldMap treeVars d
    XSwitchLit _ branches d -> foldMap (treeVars <<< _.tree) branches <> treeVars d
    XSwitchKey _ branches d -> foldMap (treeVars <<< _.tree) branches <> foldMap treeVars d
    XGuard e yes no -> freeVarsOf e <> treeVars yes <> treeVars no

  handlerVars h =
    entryVars h.element
      <> foldMap (\l -> foldMap (typeVars <<< _.ty) l.cells) h.cells
      <> typeVars h.returnClause.ty
      <> withoutValue h.returnClause.binder (freeVarsOf h.returnClause.body)
      <> regionScoped (foldMap clauseVars h.opClauses)
    where
    regionScoped = case h.cells of
      Just l -> withoutType l.var
      Nothing -> identity

  clauseVars = case _ of
    XFullClause c ->
      foldMap (kindsOf <<< _.kind) c.tyBinders
        <> withoutTypes (map _.name c.tyBinders)
          ( typeVars c.argBinder.ty
              <> typeVars c.contBinder.ty
              <> withoutValues [ c.argBinder.name, c.contBinder.name ] (freeVarsOf c.body)
          )
    XFastClause c ->
      foldMap (kindsOf <<< _.kind) c.tyBinders
        <> withoutTypes (map _.name c.tyBinders)
          (typeVars c.argBinder.ty <> withoutValue c.argBinder.name (freeVarsOf c.body))

  entryVars entry = typeVars (XRowExtend entry XRowEmpty)
  constraintVars c = typeVars (XConstrained c XRowEmpty)

none :: FreeVars
none = { values: Set.empty, types: Set.empty, kinds: Set.empty, joins: Set.empty }

valueVar :: Ident -> FreeVars
valueVar x = none { values = Set.singleton x }

joinVar :: JoinName -> FreeVars
joinVar j = none { joins = Set.singleton j }

kindsOf :: XKind -> FreeVars
kindsOf k = none { kinds = kindVarsOf k }

typeVars :: XType -> FreeVars
typeVars ty = none { types = freeRigids ty, kinds = freeKindVars ty }

withoutValue :: Ident -> FreeVars -> FreeVars
withoutValue x fv = fv { values = Set.delete x fv.values }

withoutValues :: P.Array Ident -> FreeVars -> FreeVars
withoutValues xs fv = fv { values = Set.difference fv.values (Set.fromFoldable xs) }

withoutType :: TyVar -> FreeVars -> FreeVars
withoutType a fv = fv { types = Set.delete a fv.types }

withoutTypes :: P.Array TyVar -> FreeVars -> FreeVars
withoutTypes as fv = fv { types = Set.difference fv.types (Set.fromFoldable as) }

withoutJoin :: JoinName -> FreeVars -> FreeVars
withoutJoin j fv = fv { joins = Set.delete j fv.joins }

-- | Every metavariable a term mentions, in any position.
metasOfTerm :: forall a. XExpr a -> MetasOfTerm
metasOfTerm = case _ of
  EVar _ _ -> noMetas
  EGlobal _ _ kinds -> foldMap kindMetas kinds
  ELit _ _ -> noMetas
  ELam _ _ ty body -> typeMetas ty <> metasOfTerm body
  EApp _ f x -> metasOfTerm f <> metasOfTerm x
  ETyLam _ _ kind body -> kindMetas kind <> metasOfTerm body
  ETyApp _ e ty -> metasOfTerm e <> typeMetas ty
  EConstraintLam _ c body -> typeMetas (XConstrained c XRowEmpty) <> metasOfTerm body
  EConstraintApp _ e -> metasOfTerm e
  ELet _ _ ty v body -> typeMetas ty <> metasOfTerm v <> metasOfTerm body
  ELetRec _ bindings body -> foldMap (\b -> typeMetas b.ty <> metasOfTerm b.value) bindings <> metasOfTerm body
  ECase _ scrutinees dt -> foldMap metasOfTerm scrutinees <> treeMetas dt
  ELetJoin _ _ params result v body ->
    foldMap (typeMetas <<< _.ty) params <> typeMetas result <> metasOfTerm v <> metasOfTerm body
  EJump _ _ args -> foldMap metasOfTerm args
  ERecordEmpty _ -> noMetas
  ERecordExtend _ _ v rest -> metasOfTerm v <> metasOfTerm rest
  ERecordSelect _ _ e -> metasOfTerm e
  ERecordRestrict _ _ e -> metasOfTerm e
  ERecordUpdate _ _ rec v -> metasOfTerm rec <> metasOfTerm v
  ERecordMerge _ l r -> metasOfTerm l <> metasOfTerm r
  EVariantInject _ _ v -> metasOfTerm v
  EVariantWeaken _ _ ty e -> typeMetas ty <> metasOfTerm e
  EVariantAbsurd _ ty e -> typeMetas ty <> metasOfTerm e
  EPerform _ _ _ tyArgs arg -> foldMap typeMetas tyArgs <> metasOfTerm arg
  EHandle _ body h initial -> metasOfTerm body <> handlerMetas h <> foldMap metasOfTerm initial
  EReadCell _ _ -> noMetas
  EWriteCell _ _ v -> metasOfTerm v
  EOpenEff _ row e -> typeMetas row <> metasOfTerm e
  ETermMeta _ m -> noMetas { terms = Set.singleton m }
  EHole _ ty -> typeMetas ty
  where
  treeMetas = case _ of
    XLeaf e -> metasOfTerm e
    XBind _ _ dt -> treeMetas dt
    XSwitchCtor _ branches d -> foldMap (treeMetas <<< _.tree) branches <> foldMap treeMetas d
    XSwitchLit _ branches d -> foldMap (treeMetas <<< _.tree) branches <> treeMetas d
    XSwitchKey _ branches d -> foldMap (treeMetas <<< _.tree) branches <> foldMap treeMetas d
    XGuard e yes no -> metasOfTerm e <> treeMetas yes <> treeMetas no

  handlerMetas h =
    typeMetas (XRowExtend h.element XRowEmpty)
      <> foldMap (\l -> foldMap (typeMetas <<< _.ty) l.cells) h.cells
      <> typeMetas h.returnClause.ty
      <> metasOfTerm h.returnClause.body
      <> foldMap clauseMetas h.opClauses

  clauseMetas = case _ of
    XFullClause c ->
      foldMap (kindMetas <<< _.kind) c.tyBinders
        <> typeMetas c.argBinder.ty
        <> typeMetas c.contBinder.ty
        <> metasOfTerm c.body
    XFastClause c ->
      foldMap (kindMetas <<< _.kind) c.tyBinders <> typeMetas c.argBinder.ty <> metasOfTerm c.body

noMetas :: MetasOfTerm
noMetas = { terms: Set.empty, types: Set.empty, kinds: Set.empty }

typeMetas :: XType -> MetasOfTerm
typeMetas ty = noMetas { types = metasOf ty, kinds = kindMetasOfType ty }

kindMetas :: XKind -> MetasOfTerm
kindMetas k = noMetas { kinds = kindMetasOf k }

derive instance Eq TermMetaVar
derive instance Ord TermMetaVar
derive newtype instance Show TermMetaVar

derive instance Eq a => Eq (XExpr a)
derive instance Functor XExpr
derive instance Generic (XExpr a) _

instance Show a => Show (XExpr a) where
  show x = genericShow x

derive instance Eq a => Eq (XOpClause a)
derive instance Functor XOpClause
derive instance Generic (XOpClause a) _

instance Show a => Show (XOpClause a) where
  show x = genericShow x

derive instance Eq a => Eq (XDecisionTree a)
derive instance Functor XDecisionTree
derive instance Generic (XDecisionTree a) _

instance Show a => Show (XDecisionTree a) where
  show x = genericShow x

derive instance Eq a => Eq (Residue a)
derive instance Generic (Residue a) _

instance Show a => Show (Residue a) where
  show x = genericShow x
