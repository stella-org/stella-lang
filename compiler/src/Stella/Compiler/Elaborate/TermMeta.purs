-- | Term metavariables of `Ψ`: creating one, assigning it, and zonking a Core⁺
-- | term against what `Ψ` has solved.
-- |
-- | **A solution is not type checked here.** An elaborator may construct an
-- | ill-typed Core⁺ term, and what rejects it is the Core type checker once the
-- | term has been zonked. What is checked is scope: a solution stands where its
-- | `?m` stood, so it may mention only what was in scope there.
module Stella.Compiler.Elaborate.TermMeta
  ( TermError(..)
  , termScopeOf
  , freshTermMeta
  , assignTermMeta
  , zonkExpr
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Context (XContext)
import Stella.Compiler.Elaborate.Term (TermMetaVar(..), XDecisionTree(..), XExpr(..), XHandler, XOpClause(..), freeVarsOf, metasOfTerm)
import Stella.Compiler.Elaborate.Type (XConstraint, XType(..), freeKindVars, freeRigids, kindMetasOfType, metasOf)
import Stella.Compiler.Elaborate.Unify (MetaContext, TermBinding(..), TermMetaInfo, TermScope, UnifyError, narrowMetas, substitute, substituteKind)
import Stella.Compiler.TypedCore (Ident, JoinName, KindVar, TyVar)
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

data TermError
  -- | A term metavariable `Ψ` does not hold, and one it holds solved. Both are
  -- | errors of whoever assigns, not of the program.
  = TermMetaUnbound TermMetaVar
  | TermMetaAlreadyAssigned TermMetaVar
  -- | Assigning would make the metavariable part of its own solution.
  | TermOccursCheck TermMetaVar
  -- | A solution mentioning a variable of the class named that was not in scope
  -- | where the metavariable was created.
  | TermEscapingValue TermMetaVar Ident
  | TermEscapingType TermMetaVar TyVar
  | TermEscapingKind TermMetaVar KindVar
  -- | A solution jumping to a join point it does not bind. A join point does not
  -- | cross into a term supplied from elsewhere.
  | TermCapturesJoin TermMetaVar JoinName
  -- | A metavariable the solution holds, whose own type or kind mentions a
  -- | variable the scope it is narrowed to excludes.
  | TermNarrowing UnifyError

-- | The scope a context gives: the values, types, and kinds it binds.
termScopeOf :: XContext -> TermScope
termScopeOf context =
  { values: Map.keys context.vars
  , types: Map.keys context.tyVars
  , kinds: context.kindVars
  }

freshTermMeta :: TermMetaInfo -> MetaContext -> Tuple TermMetaVar MetaContext
freshTermMeta info ctx =
  Tuple m ctx
    { termBindings = Map.insert m (TermUnsolved info) ctx.termBindings
    , nextTerm = ctx.nextTerm + 1
    }
  where
  m = TermMetaVar ctx.nextTerm

-- | `?m := e`.
-- |
-- | The solution is zonked first, so what is checked is what it stands on
-- | rather than what it was written with. Then:
-- |
-- | ```text
-- | ?m does not occur in it
-- | every value, type, and kind variable it mentions free is in ?m's scope
-- | it jumps to no join point it does not bind
-- | every term metavariable in it is narrowed to its own scope ∩ ?m's
-- | every type and kind metavariable in it is narrowed to ?m's
-- | ```
-- |
-- | **Narrowing is what stops an escape through a chain.** A metavariable
-- | standing in a solution mentions nothing until it is solved, so without it
-- | `?outer := ?inner` followed by `?inner := x` would admit an `x` that is out
-- | of scope where `?outer` stood. A term metavariable narrowed has its own type
-- | checked against the narrower scope, and the metavariables of that type
-- | narrowed with it.
-- |
-- | The solution is stored without annotations.
assignTermMeta :: forall a. MetaContext -> TermMetaVar -> XExpr a -> Either TermError MetaContext
assignTermMeta ctx m given = case Map.lookup m ctx.termBindings of
  Nothing -> Left (TermMetaUnbound m)
  Just (TermAssigned _) -> Left (TermMetaAlreadyAssigned m)
  Just (TermUnsolved info) -> do
    let
      solution = zonkExpr ctx given
      free = freeVarsOf solution
      metas = metasOfTerm solution
    when (Set.member m metas.terms) (Left (TermOccursCheck m))
    escaping (TermEscapingValue m) (Set.difference free.values info.scope.values)
    escaping (TermEscapingType m) (Set.difference free.types info.scope.types)
    escaping (TermEscapingKind m) (Set.difference free.kinds info.scope.kinds)
    escaping (TermCapturesJoin m) free.joins
    narrowedTerms <- foldM (narrowTerm info.scope) ctx (Set.toUnfoldable metas.terms :: P.Array TermMetaVar)
    narrowed <- lmap TermNarrowing
      (narrowMetas narrowedTerms (typeScope info.scope) metas.types metas.kinds)
    pure narrowed
      { termBindings = Map.insert m (TermAssigned (map (const unit) solution)) narrowed.termBindings }
  where
  escaping :: forall v. (v -> TermError) -> Set v -> Either TermError Unit
  escaping err vs = case Set.findMin vs of
    Just v -> Left (err v)
    Nothing -> Right unit

-- | Narrow one term metavariable standing in a solution to the scope given.
narrowTerm :: TermScope -> MetaContext -> TermMetaVar -> Either TermError MetaContext
narrowTerm scope ctx t = case Map.lookup t ctx.termBindings of
  Just (TermUnsolved tInfo) -> do
    let
      within =
        { values: Set.intersection tInfo.scope.values scope.values
        , types: Set.intersection tInfo.scope.types scope.types
        , kinds: Set.intersection tInfo.scope.kinds scope.kinds
        }
      ty = substitute ctx tInfo.ty
    case Set.findMin (Set.difference (freeRigids ty) within.types) of
      Just a -> Left (TermEscapingType t a)
      Nothing -> Right unit
    case Set.findMin (Set.difference (freeKindVars ty) within.kinds) of
      Just k -> Left (TermEscapingKind t k)
      Nothing -> Right unit
    ctx' <- lmap TermNarrowing (narrowMetas ctx (typeScope within) (metasOf ty) (kindMetasOfType ty))
    pure ctx'
      { termBindings = Map.insert t (TermUnsolved { ty, scope: within }) ctx'.termBindings }

  -- A zonked solution holds no metavariable that is solved.
  Just (TermAssigned _) -> Left (TermMetaAlreadyAssigned t)
  Nothing -> Left (TermMetaUnbound t)

typeScope :: TermScope -> { types :: Set TyVar, kinds :: Set KindVar }
typeScope scope = { types: scope.types, kinds: scope.kinds }

lmap :: forall e f b. (e -> f) -> Either e b -> Either f b
lmap f = case _ of
  Left e -> Left (f e)
  Right b -> Right b

-- | Apply everything `Ψ` has solved, at every level.
-- |
-- | A solved `?m` is replaced by its solution zonked in turn, every node of it
-- | taking the annotation of the `?m` it replaces. The occurs check at assignment
-- | is what makes this terminate.
zonkExpr :: forall a. MetaContext -> XExpr a -> XExpr a
zonkExpr ctx = go
  where
  ty = substitute ctx
  kind = substituteKind ctx

  go :: XExpr a -> XExpr a
  go = case _ of
    EVar a x -> EVar a x
    EGlobal a name kinds -> EGlobal a name (map kind kinds)
    ELit a literal -> ELit a literal
    ELam a x t body -> ELam a x (ty t) (go body)
    EApp a f x -> EApp a (go f) (go x)
    ETyLam a name k body -> ETyLam a name (kind k) (go body)
    ETyApp a e t -> ETyApp a (go e) (ty t)
    EConstraintLam a c body -> EConstraintLam a (constraint c) (go body)
    EConstraintApp a e -> EConstraintApp a (go e)
    ELet a x t v body -> ELet a x (ty t) (go v) (go body)
    ELetRec a bindings body ->
      ELetRec a (map (\b -> { name: b.name, ty: ty b.ty, value: go b.value }) bindings) (go body)
    ECase a scrutinees dt -> ECase a (map go scrutinees) (tree dt)
    ELetJoin a j params result v body ->
      ELetJoin a j (map param params) (ty result) (go v) (go body)
    EJump a j args -> EJump a j (map go args)
    ERecordEmpty a -> ERecordEmpty a
    ERecordExtend a key v rest -> ERecordExtend a key (go v) (go rest)
    ERecordSelect a key e -> ERecordSelect a key (go e)
    ERecordRestrict a key e -> ERecordRestrict a key (go e)
    ERecordUpdate a key rec v -> ERecordUpdate a key (go rec) (go v)
    ERecordMerge a l r -> ERecordMerge a (go l) (go r)
    EVariantInject a key v -> EVariantInject a key (go v)
    EVariantWeaken a key t e -> EVariantWeaken a key (ty t) (go e)
    EVariantAbsurd a t e -> EVariantAbsurd a (ty t) (go e)
    EPerform a key op tyArgs arg -> EPerform a key op (map ty tyArgs) (go arg)
    EHandle a body h initial -> EHandle a (go body) (handler h) (map go initial)
    EReadCell a key -> EReadCell a key
    EWriteCell a key v -> EWriteCell a key (go v)
    EOpenEff a row e -> EOpenEff a (ty row) (go e)
    ETermMeta a m -> case Map.lookup m ctx.termBindings of
      Just (TermAssigned solution) -> go (map (const a) solution)
      _ -> ETermMeta a m
    EHole a t -> EHole a (ty t)

  param p = { name: p.name, ty: ty p.ty }

  constraint :: XConstraint -> XConstraint
  constraint c = case ty (XConstrained c XRowEmpty) of
    XConstrained c' _ -> c'
    _ -> c

  tree :: XDecisionTree a -> XDecisionTree a
  tree = case _ of
    XLeaf e -> XLeaf (go e)
    XBind x o dt -> XBind x o (tree dt)
    XSwitchCtor o branches d -> XSwitchCtor o (map (\b -> b { tree = tree b.tree }) branches) (map tree d)
    XSwitchLit o branches d -> XSwitchLit o (map (\b -> b { tree = tree b.tree }) branches) (tree d)
    XSwitchKey o branches d -> XSwitchKey o (map (\b -> b { tree = tree b.tree }) branches) (map tree d)
    XGuard e yes no -> XGuard (go e) (tree yes) (tree no)

  handler :: XHandler a -> XHandler a
  handler h =
    { element: entry h.element
    , cells: map (\l -> l { cells = map (\c -> c { ty = ty c.ty }) l.cells }) h.cells
    , returnClause: h.returnClause { ty = ty h.returnClause.ty, body = go h.returnClause.body }
    , opClauses: map clause h.opClauses
    }

  entry e = case ty (XRowExtend e XRowEmpty) of
    XRowExtend e' _ -> e'
    _ -> e

  clause = case _ of
    XFullClause c -> XFullClause c
      { tyBinders = map (\b -> b { kind = kind b.kind }) c.tyBinders
      , argBinder = param c.argBinder
      , contBinder = param c.contBinder
      , body = go c.body
      }
    XFastClause c -> XFastClause c
      { tyBinders = map (\b -> b { kind = kind b.kind }) c.tyBinders
      , argBinder = param c.argBinder
      , body = go c.body
      }

derive instance Eq TermError
derive instance Generic TermError _

instance Show TermError where
  show x = genericShow x
