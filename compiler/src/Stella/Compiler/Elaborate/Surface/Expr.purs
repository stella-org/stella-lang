-- | A value declaration's body elaborated into Core⁺, checked against its
-- | signature ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **Checking is directed by the signature.** A declaration's scheme is opened
-- | by type abstractions, its parameters are bound by λs at the argument types
-- | its arrows give, and its body is checked against what is left. An
-- | application infers its function, checks its argument, and fits the row
-- | the function performs into the row ambient there; a global is instantiated
-- | at a fresh metavariable for each of its kind variables and each `forall`
-- | of its scheme, a row quantifier's an instantiation row; a λ is checked
-- | against an arrow, or inferred under a fresh row where nothing gives its
-- | type; and a form whose type is only inferred is subsumed by what is
-- | expected. Every equation is stated where the node it is about stands, and
-- | one that cannot be decided yet is left to the loop.
-- |
-- | **What a signature or an annotation writes is a checking boundary**: the
-- | right-hand side of a declaration at `()`, and a λ at each arrow written,
-- | its body built under an ambient row of its own that only the boundary
-- | decides. An arrow instantiation or inference gives is no boundary, its row
-- | being ambient as it is.
-- |
-- | **A scheme's constraints are assumed where its declaration's body opens
-- | it**, under a constraint abstraction, **and required where a global is
-- | instantiated**, under a constraint application.
-- |
-- | **This version elaborates a subset**: variables, globals and constructors,
-- | literals, application, λ over variables, and type annotations. A
-- | synthesized argument of the declaration's own is a parameter like any
-- | other; a reference to a value taking one is outside the subset, a goal
-- | being what supplies the argument. Anything else is reported where it
-- | stands, and the declaration holding it is not elaborated further.
module Stella.Compiler.Elaborate.Surface.Expr
  ( Surf
  , runSurf
  , elaborateValue
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), XContext, bindKindVars, bindTyVar, bindVar, emptyXContext, lookupVar)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.CorePlus.Term (XExpr(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..), fromCore)
import Stella.Compiler.Elaborate.Surface.Internal (Internal)
import Stella.Compiler.Elaborate.Environment.Catalog (lookupEntry)
import Stella.Compiler.Elaborate.Environment.Surface (SurfaceEnv)
import Stella.Compiler.Elaborate.Kernel.Builder.Common (substituteKindVars, substituteTyVars)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, askEnv, assume, closeBoundary, currentMetas, equate, freshInstantiationRow, freshKindMeta, freshTypeMeta, openBoundary, placeFit, require)
import Stella.Compiler.Elaborate.Mechanism.Fit (FitUse(..))
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindRequirement(..), substitute)
import Stella.Compiler.Elaborate.Surface.Type (Unsupported(..), elaborateType, xFunction)
import Stella.Compiler.Surface.Expr (Binder(..), Expr(..), exprOrigin)
import Stella.Compiler.Surface.Name (LocalVar(..))
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore.Name (Ident, Qualified)
import Stella.Compiler.TypedCore.Prim (functionTy, litType)
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Type (TypeScheme)

-- | Elaboration that stops at the first form this version does not read.
newtype Surf a = Surf (Elab (Either Unsupported a))

runSurf :: forall a. Surf a -> Elab (Either Unsupported a)
runSurf (Surf e) = e

instance Functor Surf where
  map f (Surf e) = Surf (map (map f) e)

instance Apply Surf where
  apply = ap

instance Applicative Surf where
  pure = Surf <<< pure <<< Right

instance Bind Surf where
  bind (Surf e) k = Surf
    ( e >>= case _ of
        Left problem -> pure (Left problem)
        Right a -> runSurf (k a)
    )

instance Monad Surf

lift :: forall a. Elab a -> Surf a
lift = Surf <<< map Right

outside :: forall a. Unsupported -> Surf a
outside = Surf <<< pure <<< Left

-- | What an expression is elaborated under: the declaration it belongs to, the
-- | context its node stands in, the row its evaluation may perform, the entries
-- | the compiler's desugarings refer to that no catalog holds, and what the
-- | surface elaborator reads of the imports and of the module: the synonyms its
-- | annotations are read through, and the values taking a synthesized argument.
type Scope = { declaration :: Qualified Ident, context :: XContext, ambient :: XType, internal :: Internal, surface :: SurfaceEnv }

-- | Where a type an expression is checked against comes from. **An arrow a
-- | signature or an annotation writes is a checking boundary**, and so is every
-- | arrow reached by opening its quantifiers, constraints, and parameters; one
-- | instantiation or inference gives is not, its row being ambient as it is.
data Expected
  = Written
  | Derived

siteAt :: Scope -> Surface.Origin -> Site
siteAt scope origin = { context: scope.context, origin: AtSource { declaration: scope.declaration, origin } }

-- | A value declaration's definition, at its scheme: `Λ`s for its quantifiers,
-- | `λ`s for its parameters, and its body checked against what is left, the
-- | whole of it a checking boundary at `()`, the row every top-level value is
-- | defined at.
elaborateValue
  :: Internal
  -> SurfaceEnv
  -> Qualified Ident
  -> Surface.Origin
  -> TypeScheme
  -> Array Binder
  -> Expr
  -> Surf (XExpr Surface.Origin)
elaborateValue internal surface declaration origin scheme params body =
  boundary scope0 origin XRowEmpty \scope -> abstractions origin true Written scope params body (fromCore scheme.body)
  where
  scope0 = { declaration, context: bindKindVars emptyXContext scheme.kindVars, ambient: XRowEmpty, internal, surface }

-- | What the action given builds under a checking boundary's ambient row, the
-- | boundary closed against the row expected once it is built.
boundary :: forall a. Scope -> Surface.Origin -> XType -> (Scope -> Surf a) -> Surf a
boundary scope origin expected inside = do
  sigma <- lift (openBoundary scope.context)
  built <- inside (scope { ambient = XMeta sigma })
  lift (closeBoundary (siteAt scope origin) sigma expected)
  pure built

-- | The expected type opened along its spine: a `Λ` for each quantifier and a
-- | constraint abstraction for each constraint, the constraint assumed in what
-- | it encloses, and a `λ` for each variable given at the argument its arrow
-- | gives, its body under the arrow's row; then the body at what is left.
-- | Quantifiers and constraints are opened in front of the first variable and
-- | wherever variables remain, so a `forall` following a parameter, a
-- | synthesized argument's among them, is opened where it stands; one left
-- | once every variable is bound is the body's to meet. A `λ` at an arrow that
-- | is written is a checking boundary at the arrow's row.
abstractions :: Surface.Origin -> Boolean -> Expected -> Scope -> Array Binder -> Expr -> XType -> Surf (XExpr Surface.Origin)
abstractions origin front expected scope binders body ty = case ty, Array.uncons binders of
  XForall a k rest, _ | opening -> ETyLam origin a k <$> abstractions origin front expected (scope { context = bindTyVar scope.context a k }) binders body rest
  XConstrained c rest, _ | opening -> do
    context <- lift (assume (siteAt scope origin) c)
    EConstraintLam origin c <$> abstractions origin front expected (scope { context = context }) binders body rest
  _, Nothing -> check scope body expected ty
  _, Just { head, tail } -> do
    parts <- arrow scope (binderOrigin head) ty
    case head of
      BinderVar o (LocalVar v) -> do
        let
          inner = scope { context = bindVar scope.context v.name parts.argument }
          rest s = abstractions origin false expected s tail body parts.result
        ELam o v.name parts.argument <$> case expected of
          Written -> boundary inner o parts.row rest
          Derived -> rest (inner { ambient = parts.row })
      BinderInvalid o -> outside (ReportedAlready o)
      other -> outside (OutsideSubset (binderOrigin other) "a pattern that is no variable")
  where
  opening = front || not (Array.null binders)

-- | The argument, the row, and the result of the arrow the type must be: its
-- | own where it is one, and otherwise an arrow of fresh metavariables it is
-- | equated with, its row an inference row.
arrow :: Scope -> Surface.Origin -> XType -> Surf { argument :: XType, row :: XType, result :: XType }
arrow scope origin ty = do
  metas <- lift currentMetas
  case substitute metas ty of
    XApp (XApp (XApp (XCon name []) argument) row) result | name == functionTy -> pure { argument, row, result }
    _ -> do
      argument <- lift (freshTypeMeta scope.context XKType)
      row <- lift (freshTypeMeta scope.context (XKRow RowEffect))
      result <- lift (freshTypeMeta scope.context XKType)
      lift (equate (siteAt scope origin) { kind: XKType, left: ty, right: xFunction argument row result })
      pure { argument, row, result }

check :: Scope -> Expr -> Expected -> XType -> Surf (XExpr Surface.Origin)
check scope expr expected ty = case expr of
  ExprLambda o binders body -> abstractions o false expected scope binders body ty
  ExprInvalid o -> outside (ReportedAlready o)
  _ -> do
    inferred <- infer scope expr
    subsume scope (exprOrigin expr) inferred ty

-- | An expression inferred at one type where another is expected. **Where both
-- | are arrows, the outermost row alone is contained**, a wrapping fit around
-- | the expression, and the arguments and the results are equal; anything else
-- | is an equation of the two types.
subsume :: Scope -> Surface.Origin -> { expr :: XExpr Surface.Origin, type :: XType } -> XType -> Surf (XExpr Surface.Origin)
subsume scope origin inferred expected = do
  metas <- lift currentMetas
  case asArrow (substitute metas inferred.type), asArrow (substitute metas expected) of
    Just given, Just wanted -> do
      lift (equate site { kind: XKType, left: given.argument, right: wanted.argument })
      lift (equate site { kind: XKType, left: given.result, right: wanted.result })
      fit <- lift (placeFit site Wrapping given.row wanted.row)
      pure (EFit origin fit inferred.expr)
    _, _ -> do
      lift (equate site { kind: XKType, left: inferred.type, right: expected })
      pure inferred.expr
  where
  site = siteAt scope origin
  asArrow = case _ of
    XApp (XApp (XApp (XCon name []) argument) row) result | name == functionTy -> Just { argument, row, result }
    _ -> Nothing

infer :: Scope -> Expr -> Surf { expr :: XExpr Surface.Origin, type :: XType }
infer scope expr = case expr of
  ExprLocal o (LocalVar v) -> case lookupVar scope.context v.name of
    Just ty -> pure { expr: EVar o v.name, type: ty }
    Nothing -> outside (OutsideSubset o "a variable bound outside what this version elaborates")
  ExprValue o name -> global o name
  ExprConstructor o name -> global o name
  ExprLiteral o literal -> pure { expr: ELit o literal, type: fromCore (litType literal) }
  -- the function is fitted into the row ambient where it is applied
  ExprApp _ f x -> do
    f' <- infer scope f
    parts <- arrow scope (exprOrigin f) f'.type
    x' <- check scope x Derived parts.argument
    fit <- lift (placeFit (siteAt scope (exprOrigin f)) Wrapping parts.row scope.ambient)
    pure { expr: EApp (exprOrigin expr) (EFit (exprOrigin f) fit f'.expr) x', type: parts.result }
  ExprTyped _ inner t -> do
    annotation <- lift (elaborateType scope.surface.synonyms scope.declaration scope.context t)
    case Array.head annotation.unsupported of
      Just problem -> outside problem
      Nothing -> do
        inner' <- check scope inner Written annotation.type
        pure { expr: inner', type: annotation.type }
  -- a λ whose type is not known: each parameter at a fresh type, its body
  -- under a fresh inference row
  ExprLambda _ binders body -> lambda binders body
  ExprInvalid o -> outside (ReportedAlready o)
  _ -> outside (OutsideSubset (exprOrigin expr) "this form")
  where
  lambda binders body = case Array.uncons binders of
    Nothing -> infer scope body
    Just { head: BinderVar o (LocalVar v), tail } -> do
      argument <- lift (freshTypeMeta scope.context XKType)
      row <- lift (freshTypeMeta scope.context (XKRow RowEffect))
      inner <- infer' (scope { context = bindVar scope.context v.name argument, ambient = row }) tail body
      pure { expr: ELam o v.name argument inner.expr, type: xFunction argument row inner.type }
    Just { head: BinderInvalid o } -> outside (ReportedAlready o)
    Just { head } -> outside (OutsideSubset (binderOrigin head) "a pattern that is no variable")

  infer' s binders body = case binders of
    [] -> infer s body
    _ -> infer s (ExprLambda (exprOrigin body) binders body)

  -- a global at a fresh metavariable for each kind variable and each
  -- quantifier of its scheme, outermost first, a row quantifier's an
  -- instantiation row: one the catalog holds, or one a desugaring of the
  -- compiler's refers to
  global o name = do
    env <- lift askEnv
    case lookupScheme env.session.catalog name of
      Nothing -> outside (OutsideSubset o "a global the catalog does not hold")
      -- a synthesized argument is supplied by a goal, which this version does
      -- not create
      Just _ | Set.member name scope.surface.synthesizing -> outside (OutsideSubset o "a reference to a value taking a synthesized argument")
      Just scheme -> do
        kinds <- lift (traverse (\_ -> freshKindMeta scope.context.kindVars (Set.singleton Quantifiable)) scheme.kindVars)
        let ty = substituteKindVars (Map.fromFoldable (Array.zip scheme.kindVars kinds)) scheme.body
        instantiated o (EGlobal o name kinds) ty

  lookupScheme catalog name = case lookupEntry catalog name of
    Just entry -> Just entry.scheme
    Nothing -> Map.lookup name scope.internal

  instantiated o e = case _ of
    XForall a k rest -> do
      m <- lift case k of
        XKRow RowEffect -> freshInstantiationRow scope.context
        _ -> freshTypeMeta scope.context k
      instantiated o (ETyApp o e m) (substituteTyVars (Map.singleton a m) Map.empty rest)
    XConstrained c rest -> do
      lift (require (siteAt scope o) c)
      instantiated o (EConstraintApp o e) rest
    ty -> pure { expr: e, type: ty }

binderOrigin :: Binder -> Surface.Origin
binderOrigin = case _ of
  BinderWildcard o -> o
  BinderVar o _ -> o
  BinderAs o _ _ -> o
  BinderConstructor o _ _ -> o
  BinderTag o _ _ -> o
  BinderLiteral o _ -> o
  BinderTuple o _ -> o
  BinderRecord o _ _ -> o
  BinderOr o _ -> o
  BinderTyped o _ _ -> o
  BinderInvalid o -> o
