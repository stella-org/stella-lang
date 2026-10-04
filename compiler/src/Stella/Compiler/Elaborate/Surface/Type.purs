-- | A type of the Surface AST elaborated into Core⁺, its kinds inferred
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **A kind left unwritten is a kind metavariable**, and every kind a type is
-- | at is constrained by an equation as it is read: a constructor at an
-- | instance of its kind scheme, an application at the arrow its head must be,
-- | an arrow's sides and a `forall`'s body at `Type`. The equations are decided
-- | as they are met, kinds never waiting; whether every kind ended up solved is
-- | asked once the elaboration they belong to is done, of each binder that left
-- | one unwritten.
-- |
-- | **This version reads a subset of types**: variables, constructors,
-- | applications, pure arrows, `forall`, and kind annotations. Anything else is
-- | reported as outside it, and stands meanwhile as a fresh metavariable, so
-- | what surrounds it is still read.
module Stella.Compiler.Elaborate.Surface.Type
  ( Unsupported(..)
  , Elaborated
  , elaborateSignature
  , settledScheme
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Foldable (foldr)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Either (Either(..))
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..), kindMetasOf)
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..), toCore)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, askEnv, equateKinds, freshKindMeta, freshTypeMeta, raiseDiagnostic)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (instantiate)
import Stella.Compiler.Elaborate.Mechanism.Kinding (quantifiable) as Kinding
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindRequirement(..), MetaContext, UnifyError(..), substitute, substituteKind)
import Stella.Compiler.Surface.Name (TypeVar(..))
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.Surface.Type (Kind(..), Signature, Type(..), TypeVarBinder, typeOrigin)
import Stella.Compiler.TypedCore.Name (Ident, KindVar, Qualified, TyVar)
import Stella.Compiler.TypedCore.Prim (functionTy)
import Stella.Compiler.TypedCore.Type (TypeScheme)

-- | A form this version does not read, where it stands: what it is, or that
-- | resolution reported it already.
data Unsupported
  = OutsideSubset Surface.Origin String
  | ReportedAlready Surface.Origin

-- | A signature elaborated: the kind variables its kinds mention, which its
-- | scheme binds; its type; each binder whose kind was left unwritten, with
-- | the metavariable standing for it; and what was outside the subset.
type Elaborated =
  { kindVars :: Array KindVar
  , type :: XType
  , unwritten :: Array { origin :: Surface.Origin, kind :: XKind }
  , unsupported :: Array Unsupported
  }

-- | What a type is read under: the declaration it belongs to, the kind
-- | variables in scope, and the kind of each type variable bound.
type Scope = { declaration :: Qualified Ident, kindVars :: Set KindVar, tyVars :: Map TypeVar XKind }

-- | What reading one type gave.
type Read = { type :: XType, kind :: XKind, unwritten :: Array { origin :: Surface.Origin, kind :: XKind }, unsupported :: Array Unsupported }

-- | `forall ā. τ`, where `ā` are the variables the signature quantifies
-- | implicitly, at `Type`.
elaborateSignature :: Qualified Ident -> Signature Type -> Elab Elaborated
elaborateSignature declaration signature = do
  let kindVars = foldr Set.insert Set.empty (typeKindVars signature.body)
  implicit <- traverse (\v -> { var: v, kind: _ } <$> freshKindMeta kindVars quantifiable) signature.implicit
  let
    scope =
      { declaration
      , kindVars
      , tyVars: Map.fromFoldable (map (\i -> Tuple i.var i.kind) implicit)
      }
  body <- checkAt scope XKType signature.body
  pure
    { kindVars: Array.fromFoldable kindVars
    , type: foldr (\i t -> XForall (nameOf i.var) i.kind t) body.type implicit
    -- an implicit variable is written first where it is first mentioned
    , unwritten: map (\i -> { origin: fromMaybe (typeOrigin signature.body) (firstMention i.var signature.body), kind: i.kind }) implicit <> body.unwritten
    , unsupported: body.unsupported
    }

-- | A type at the kind given.
checkAt :: Scope -> XKind -> Type -> Elab Read
checkAt scope expected t = do
  r <- readType scope t
  equateKinds (siteOf scope (typeOrigin t)) r.kind expected
  pure r

readType :: Scope -> Type -> Elab Read
readType scope t = case t of
  TypeVariable o v -> case Map.lookup v scope.tyVars of
    Just kind -> pure (plain (XVar (nameOf v)) kind)
    Nothing -> unsupported (OutsideSubset o "a type variable bound outside the signature")
  TypeConstructor o name -> do
    env <- askEnv
    case Map.lookup name env.session.kinding.types of
      Just scheme -> do
        args <- traverse (\_ -> freshKindMeta scope.kindVars quantifiable) scheme.kindVars
        pure (plain (XCon name args) (instantiate scheme args))
      Nothing -> unsupported (OutsideSubset o "a type constructor the signature does not hold")
  TypeApp o f x -> do
    f' <- readType scope f
    x' <- readType scope x
    result <- freshKindMeta scope.kindVars Set.empty
    equateKinds (siteOf scope o) f'.kind (XKFun x'.kind result)
    pure (joined [ f', x' ] (XApp f'.type x'.type) result)
  TypeFunction _ a b Nothing -> do
    a' <- checkAt scope XKType a
    b' <- checkAt scope XKType b
    pure (joined [ a', b' ] (XApp (XApp (XApp (XCon functionTy []) a'.type) XRowEmpty) b'.type) XKType)
  TypeFunction o _ _ (Just _) -> unsupported (OutsideSubset o "an effect row")
  TypeForall _ binders body -> do
    bound <- traverse (binder scope) binders
    let inner = scope { tyVars = foldr (\b m -> Map.insert b.var b.kind m) scope.tyVars bound }
    body' <- checkAt inner XKType body
    pure
      { type: foldr (\b ty -> XForall (nameOf b.var) b.kind ty) body'.type bound
      , kind: XKType
      , unwritten: Array.concatMap _.unwritten bound <> body'.unwritten
      , unsupported: Array.concatMap _.unsupported bound <> body'.unsupported
      }
  TypeKinded _ inner k -> do
    kind <- readKind k
    case kind of
      Right written -> checkAt scope written inner
      Left problem -> unsupported problem
  TypeInvalid o -> unsupported (ReportedAlready o)
  TypeSynonym o _ -> unsupported (OutsideSubset o "a type synonym")
  TypeConstrained o _ _ -> unsupported (OutsideSubset o "a constraint")
  TypeSynthesized o _ _ _ -> unsupported (OutsideSubset o "a synthesized argument")
  TypeWildcard o -> unsupported (OutsideSubset o "a wildcard")
  TypeHole o _ -> unsupported (OutsideSubset o "a typed hole")
  TypeOperator o _ _ _ -> unsupported (OutsideSubset o "a type operator")
  TypeTuple o _ -> unsupported (OutsideSubset o "a tuple type")
  TypeRecord o _ -> unsupported (OutsideSubset o "a record type")
  TypeVariant o _ -> unsupported (OutsideSubset o "a variant type")
  TypeEffectRow o _ -> unsupported (OutsideSubset o "an effect row")
  where
  plain ty kind = { type: ty, kind, unwritten: [], unsupported: [] }

  joined parts ty kind =
    { type: ty, kind, unwritten: Array.concatMap _.unwritten parts, unsupported: Array.concatMap _.unsupported parts }

  -- a form not read stands as a metavariable of a kind of its own
  unsupported problem = do
    kind <- freshKindMeta scope.kindVars Set.empty
    meta <- freshTypeMeta (emptyXContext { kindVars = scope.kindVars }) kind
    pure { type: meta, kind, unwritten: [], unsupported: [ problem ] }

-- | A binder of a `forall`, at the kind written or at a metavariable.
binder :: Scope -> TypeVarBinder -> Elab { var :: TypeVar, kind :: XKind, unwritten :: Array { origin :: Surface.Origin, kind :: XKind }, unsupported :: Array Unsupported }
binder scope b = case b.kind of
  Just k -> readKind k >>= case _ of
    Right kind -> case Kinding.quantifiable kind of
      Right _ -> pure { var: b.var, kind, unwritten: [], unsupported: [] }
      -- a type variable stands at a kind it may be introduced at, `Effect` and
      -- what produces it being none
      Left _ -> raiseDiagnostic (EquationFailed (AtSource { declaration: scope.declaration, origin: b.origin }) (KindNotQuantifiable kind))
    Left problem -> pure { var: b.var, kind: XKType, unwritten: [], unsupported: [ problem ] }
  Nothing -> do
    kind <- freshKindMeta scope.kindVars quantifiable
    pure { var: b.var, kind, unwritten: [ { origin: b.origin, kind } ], unsupported: [] }

readKind :: Kind -> Elab (Either Unsupported XKind)
readKind k = pure (go k)
  where
  go = case _ of
    KindType _ -> Right XKType
    KindEffect _ -> Right XKEffect
    KindRow _ e -> Right (XKRow e)
    KindArrow _ a b -> XKFun <$> go a <*> go b
    KindVariable _ v -> Right (XKVar v)
    KindInvalid o -> Left (ReportedAlready o)

-- | What a kind a type variable is introduced at must be.
quantifiable :: Set KindRequirement
quantifiable = Set.singleton Quantifiable

-- | The site a node of the type is read at, under the kind variables in scope.
siteOf :: Scope -> Surface.Origin -> Site
siteOf scope origin =
  { context: emptyXContext { kindVars = scope.kindVars }
  , origin: AtSource { declaration: scope.declaration, origin }
  }

nameOf :: TypeVar -> TyVar
nameOf (TypeVar v) = v.name

-- | Where a type variable is first mentioned in a type, reading left to right.
firstMention :: TypeVar -> Type -> Maybe Surface.Origin
firstMention x = case _ of
  TypeVariable o y | x == y -> Just o
  TypeApp _ f y -> either (firstMention x f) (firstMention x y)
  TypeFunction _ a b _ -> either (firstMention x a) (firstMention x b)
  TypeForall _ _ body -> firstMention x body
  TypeKinded _ inner _ -> firstMention x inner
  _ -> Nothing
  where
  either first second = case first of
    Just o -> Just o
    Nothing -> second

-- | The kind variables the kinds written in a type mention.
typeKindVars :: Type -> Array KindVar
typeKindVars = case _ of
  TypeApp _ f x -> typeKindVars f <> typeKindVars x
  TypeFunction _ a b _ -> typeKindVars a <> typeKindVars b
  TypeForall _ binders body -> Array.concatMap (\b -> maybe [] kindVars b.kind) binders <> typeKindVars body
  TypeKinded _ inner k -> typeKindVars inner <> kindVars k
  _ -> []
  where
  maybe d f = case _ of
    Just x -> f x
    Nothing -> d
  kindVars = case _ of
    KindArrow _ a b -> kindVars a <> kindVars b
    KindVariable _ v -> [ v ]
    _ -> []

-- | The Core scheme of a signature once its kinds are decided: every
-- | metavariable solved, or the origin of each binder whose kind was left
-- | undetermined.
settledScheme :: MetaContext -> Elaborated -> Either (Array Surface.Origin) TypeScheme
settledScheme metas e =
  case Array.filter (\u -> not (Set.isEmpty (kindMetasOf (substituteKind metas u.kind)))) e.unwritten of
    [] -> case toCore (substitute metas e.type) of
      Just body -> Right { kindVars: e.kindVars, body }
      Nothing -> Left []
    undetermined -> Left (map _.origin undetermined)

derive instance Eq Unsupported

instance Show Unsupported where
  show = case _ of
    OutsideSubset o what -> "OutsideSubset (" <> show o <> ") " <> show what
    ReportedAlready o -> "ReportedAlready (" <> show o <> ")"
