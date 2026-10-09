-- | A value declaration's body elaborated into Core⁺, checked against its
-- | signature ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **Checking is directed by the signature.** A declaration's scheme is opened
-- | by type abstractions, its parameters are bound by λs at the argument types
-- | its arrows give, and its body is checked against what is left. An
-- | application infers its function and checks its argument; a global is
-- | instantiated at a fresh metavariable for each of its kind variables and
-- | each `forall` of its scheme; a λ is checked against an arrow, and a form
-- | whose type is only inferred is checked by equating what it is inferred at
-- | with what is expected. Every equation is stated where the node it is about
-- | stands, and one that cannot be decided yet is left to the loop.
-- |
-- | **A scheme's constraints are assumed where its declaration's body opens
-- | it**, under a constraint abstraction, **and required where a global is
-- | instantiated**, under a constraint application.
-- |
-- | **This version elaborates a subset**: variables, globals and constructors,
-- | literals, application, λ over variables where its type is known, and type
-- | annotations, over pure arrows. Anything else is reported where it stands,
-- | and the declaration holding it is not elaborated further.
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
import Stella.Compiler.Elaborate.Environment.Synonyms (SynonymEnv)
import Stella.Compiler.Elaborate.Kernel.Builder.Common (substituteKindVars, substituteTyVars)
import Stella.Compiler.Elaborate.CorePlus.Row (xnf)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, askEnv, assume, currentMetas, equate, freshKindMeta, freshTypeMeta, require)
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindRequirement(..), substitute)
import Stella.Compiler.Elaborate.Surface.Type (Unsupported(..), elaborateType, xFunction)
import Stella.Compiler.Surface.Expr (Binder(..), Expr(..), exprOrigin)
import Stella.Compiler.Surface.Name (LocalVar(..))
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.TypedCore.Name (Ident, Qualified)
import Stella.Compiler.TypedCore.Prim (functionTy, litType)
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
-- | context its node stands in, the entries the compiler's desugarings refer to
-- | that no catalog holds, and the type synonyms its annotations are read
-- | through.
type Scope = { declaration :: Qualified Ident, context :: XContext, internal :: Internal, synonyms :: SynonymEnv }

siteAt :: Scope -> Surface.Origin -> Site
siteAt scope origin = { context: scope.context, origin: AtSource { declaration: scope.declaration, origin } }

-- | A value declaration's definition, at its scheme: `Λ`s for its quantifiers,
-- | `λ`s for its parameters, and its body checked against what is left.
elaborateValue
  :: Internal
  -> SynonymEnv
  -> Qualified Ident
  -> Surface.Origin
  -> TypeScheme
  -> Array Binder
  -> Expr
  -> Surf (XExpr Surface.Origin)
elaborateValue internal synonyms declaration origin scheme params body = opened scope0 (fromCore scheme.body)
  where
  scope0 = { declaration, context: bindKindVars emptyXContext scheme.kindVars, internal, synonyms }

  opened scope = case _ of
    XForall a k rest -> ETyLam origin a k <$> opened (scope { context = bindTyVar scope.context a k }) rest
    XConstrained c rest -> do
      context <- lift (assume (siteAt scope origin) c)
      EConstraintLam origin c <$> opened (scope { context = context }) rest
    ty -> lambdas scope params body ty

-- | `λ`s binding the variables given at the argument types the expected type's
-- | arrows give, then the body at what is left.
lambdas :: Scope -> Array Binder -> Expr -> XType -> Surf (XExpr Surface.Origin)
lambdas scope binders body expected = case Array.uncons binders of
  Nothing -> check scope body expected
  Just { head, tail } -> do
    parts <- arrow "a λ at an arrow that performs effects" scope (binderOrigin head) expected
    case head of
      BinderVar o (LocalVar v) ->
        ELam o v.name parts.argument <$> lambdas (scope { context = bindVar scope.context v.name parts.argument }) tail body parts.result
      BinderInvalid o -> outside (ReportedAlready o)
      other -> outside (OutsideSubset (binderOrigin other) "a pattern that is no variable")

-- | The argument and the result of a pure arrow the type must be. An arrow
-- | whose row, zonked and normalized, holds an element or a row variable — one
-- | that need not be empty among them — is outside what this version
-- | elaborates, what the arrow is for said by the text given; a row of unsolved
-- | metavariables alone is equated with the empty one.
arrow :: String -> Scope -> Surface.Origin -> XType -> Surf { argument :: XType, result :: XType }
arrow what scope origin ty = do
  metas <- lift currentMetas
  case substitute metas ty of
    XApp (XApp (XApp (XCon name []) argument) row) result | name == functionTy -> case xnf row of
      Right n
        | not (Map.isEmpty n.known) || not (Set.isEmpty n.rigid) -> outside (OutsideSubset origin what)
        | Set.isEmpty n.flexible -> pure { argument, result }
      _ -> equatedWithPure
    _ -> equatedWithPure
  where
  equatedWithPure = do
    argument <- lift (freshTypeMeta scope.context XKType)
    result <- lift (freshTypeMeta scope.context XKType)
    lift (equate (siteAt scope origin) { kind: XKType, left: ty, right: xFunction argument XRowEmpty result })
    pure { argument, result }

check :: Scope -> Expr -> XType -> Surf (XExpr Surface.Origin)
check scope expr expected = case expr of
  ExprLambda _ binders body -> lambdas scope binders body expected
  ExprInvalid o -> outside (ReportedAlready o)
  _ -> do
    inferred <- infer scope expr
    lift (equate (siteAt scope (exprOrigin expr)) { kind: XKType, left: inferred.type, right: expected })
    pure inferred.expr

infer :: Scope -> Expr -> Surf { expr :: XExpr Surface.Origin, type :: XType }
infer scope expr = case expr of
  ExprLocal o (LocalVar v) -> case lookupVar scope.context v.name of
    Just ty -> pure { expr: EVar o v.name, type: ty }
    Nothing -> outside (OutsideSubset o "a variable bound outside what this version elaborates")
  ExprValue o name -> global o name
  ExprConstructor o name -> global o name
  ExprLiteral o literal -> pure { expr: ELit o literal, type: fromCore (litType literal) }
  ExprApp _ f x -> do
    f' <- infer scope f
    parts <- arrow "applying a function that performs effects" scope (exprOrigin f) f'.type
    x' <- check scope x parts.argument
    pure { expr: EApp (exprOrigin expr) f'.expr x', type: parts.result }
  ExprTyped _ inner t -> do
    annotation <- lift (elaborateType scope.synonyms scope.declaration scope.context t)
    case Array.head annotation.unsupported of
      Just problem -> outside problem
      Nothing -> do
        inner' <- check scope inner annotation.type
        pure { expr: inner', type: annotation.type }
  ExprLambda o _ _ -> outside (OutsideSubset o "a λ whose type is not known where it stands")
  ExprInvalid o -> outside (ReportedAlready o)
  _ -> outside (OutsideSubset (exprOrigin expr) "this form")
  where
  -- a global at a fresh metavariable for each kind variable and each
  -- quantifier of its scheme, outermost first: one the catalog holds, or one a
  -- desugaring of the compiler's refers to
  global o name = do
    env <- lift askEnv
    case lookupScheme env.session.catalog name of
      Nothing -> outside (OutsideSubset o "a global the catalog does not hold")
      Just scheme -> do
        kinds <- lift (traverse (\_ -> freshKindMeta scope.context.kindVars (Set.singleton Quantifiable)) scheme.kindVars)
        let ty = substituteKindVars (Map.fromFoldable (Array.zip scheme.kindVars kinds)) scheme.body
        instantiated o (EGlobal o name kinds) ty

  lookupScheme catalog name = case lookupEntry catalog name of
    Just entry -> Just entry.scheme
    Nothing -> Map.lookup name scope.internal

  instantiated o e = case _ of
    XForall a k rest -> do
      m <- lift (freshTypeMeta scope.context k)
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
