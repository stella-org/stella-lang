-- | A type of the Surface AST elaborated into Core⁺, its kinds inferred
-- | ([Elaboration](../../../../../docs/technical-references/02-Surface-Language/01-Elaboration.md)).
-- |
-- | **A kind left unwritten is a kind metavariable**, and every kind a type is
-- | at is constrained by an equation as it is read: a constructor at an
-- | instance of its kind scheme, an application at the arrow its head must be,
-- | an arrow's sides and a `forall`'s body at `Type`. The equations are decided
-- | as they are met, kinds never waiting; whether every kind ended up solved is
-- | asked once the elaboration they belong to is done, of each place that left
-- | one unwritten: a binder, or a constructor instantiated at fresh kinds.
-- |
-- | **A type constructor the module declares is read at the kind its
-- | declaration is being given** while the module's data declarations are
-- | elaborated together: a kind variable written in the declaration is
-- | instantiated afresh where the constructor is used, and a metavariable
-- | standing for a kind left unwritten is the one kind every use shares.
-- |
-- | **A row is read in the bracket it is written in**: a record's and a
-- | variant's at `Row Type`, under `Prim.Record` and `Prim.Variant`, a tuple's
-- | as a record keyed by position, and an effect row at `Row Effect`, each
-- | effect applied at the kinds its parameters are declared at. An arrow
-- | carries the effect row `/` writes on it, and is pure otherwise.
-- |
-- | **This version reads a subset of types**: variables, constructors,
-- | applications, arrows, `forall`, kind annotations, tuples, rows written
-- | without a spread, and type operators naming a type constructor. Anything
-- | else is reported as outside it, and stands meanwhile as a fresh
-- | metavariable, so what surrounds it is still read.
module Stella.Compiler.Elaborate.Surface.Type
  ( Unsupported(..)
  , Elaborated
  , Read
  , Scope
  , LocalHead
  , ReadBinder
  , elaborateSignature
  , elaborateType
  , readTypeAt
  , readBinder
  , readKind
  , siteOf
  , typeKindVars
  , xFunction
  , settledScheme
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Foldable (foldM, foldr)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Either (Either(..))
import Stella.Compiler.Elaborate.CorePlus.Context (Origin(..), XContext, emptyXContext)
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..), fromCoreKind, kindMetasOf)
import Stella.Compiler.Elaborate.CorePlus.Type (XRowEntry(..), XType(..), toCore)
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, askEnv, equateKinds, freshKindMeta, freshTypeMeta, raiseDiagnostic)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (Diagnostic(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (instantiate)
import Stella.Compiler.Elaborate.Mechanism.Kinding (quantifiable) as Kinding
import Stella.Compiler.Elaborate.Mechanism.Pending (Site)
import Stella.Compiler.Elaborate.Mechanism.Unify (KindRequirement(..), MetaContext, UnifyError(..), substitute, substituteKind)
import Stella.Compiler.Surface.Name (TypeVar(..))
import Stella.Compiler.Surface.Origin as Surface
import Stella.Compiler.Surface.Type (EffectApplication, EffectRowItem(..), Kind(..), RecordRowItem(..), Signature, Type(..), TypeOperatorTarget(..), TypeVarBinder, VariantRowItem(..), typeOrigin)
import Stella.Compiler.TypedCore.Kind (RowElemKind(..))
import Stella.Compiler.TypedCore.Name (EffName, Ident, KindVar, Qualified, TyName, TyVar)
import Stella.Compiler.TypedCore.Prim (functionTy, recordTy, variantTy)
import Stella.Compiler.TypedCore.Type (RowKey(..), TypeScheme)

-- | A part of a type that is not read, where it stands: a form this version
-- | does not read, one resolution reported already, or an effect standing
-- | where a type does.
data Unsupported
  = OutsideSubset Surface.Origin String
  | ReportedAlready Surface.Origin
  -- | A type operator naming an effect, applied where no effect row's element
  -- | stands: an effect is no type.
  | EffectAsType Surface.Origin (Qualified EffName)

-- | A signature elaborated: where its type stands; the kind variables its
-- | kinds mention, which its scheme binds; its type; each place a kind was
-- | left unwritten, with the kind standing for it; and what was outside the
-- | subset.
type Elaborated =
  { origin :: Surface.Origin
  , kindVars :: Array KindVar
  , type :: XType
  , unwritten :: Array { origin :: Surface.Origin, kind :: XKind }
  , unsupported :: Array Unsupported
  }

-- | What a type is read under: the declaration it belongs to, the kind
-- | variables in scope, the kind of each type variable bound, and the type
-- | constructors the module declares whose kinds are being decided.
type Scope =
  { declaration :: Qualified Ident
  , kindVars :: Set KindVar
  , tyVars :: Map TyVar XKind
  , localTypes :: Map (Qualified TyName) LocalHead
  }

-- | The kind a type constructor of the module is read at while its declaration
-- | is elaborated: over the kind variables its declaration writes, and holding
-- | a metavariable for each kind it leaves unwritten.
type LocalHead = { kindVars :: Array KindVar, body :: XKind }

-- | A binder read: its variable, its kind, where its kind was left unwritten,
-- | and what was outside the subset.
type ReadBinder = { var :: TypeVar, kind :: XKind, unwritten :: Array { origin :: Surface.Origin, kind :: XKind }, unsupported :: Array Unsupported }

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
      , tyVars: Map.fromFoldable (map (\i -> Tuple (nameOf i.var) i.kind) implicit)
      , localTypes: Map.empty
      }
  body <- checkAt scope XKType signature.body
  pure
    { origin: typeOrigin signature.body
    , kindVars: Array.fromFoldable kindVars
    , type: foldr (\i t -> XForall (nameOf i.var) i.kind t) body.type implicit
    -- an implicit variable is written first where it is first mentioned
    , unwritten: map (\i -> { origin: fromMaybe (typeOrigin signature.body) (firstMention i.var signature.body), kind: i.kind }) implicit <> body.unwritten
    , unsupported: body.unsupported
    }

-- | A type written inside a declaration, at `Type`, under the kind variables and
-- | the type variables the context binds: an annotation, whose variables are
-- | those of the signature around it.
elaborateType :: Qualified Ident -> XContext -> Type -> Elab Read
elaborateType declaration context = checkAt { declaration, kindVars: context.kindVars, tyVars: context.tyVars, localTypes: Map.empty } XKType

-- | A type at the kind given, under the scope given.
readTypeAt :: Scope -> XKind -> Type -> Elab Read
readTypeAt = checkAt

-- | A binder, at the kind written or at a metavariable.
readBinder :: Scope -> TypeVarBinder -> Elab ReadBinder
readBinder = binder

-- | `τ1 -{ρ}-> τ2`.
xFunction :: XType -> XType -> XType -> XType
xFunction argument row result = XApp (XApp (XApp (XCon functionTy []) argument) row) result

-- | A type at the kind given.
checkAt :: Scope -> XKind -> Type -> Elab Read
checkAt scope expected t = do
  r <- readType scope t
  equateKinds (siteOf scope (typeOrigin t)) r.kind expected
  pure r

readType :: Scope -> Type -> Elab Read
readType scope t = case t of
  TypeVariable o v -> case Map.lookup (nameOf v) scope.tyVars of
    Just kind -> pure (plain (XVar (nameOf v)) kind)
    Nothing -> unsupported (OutsideSubset o "a type variable bound outside the signature")
  TypeConstructor o name | Just head <- Map.lookup name scope.localTypes -> do
    args <- traverse (\_ -> freshKindMeta scope.kindVars quantifiable) head.kindVars
    let instantiated = Map.fromFoldable (Array.zip head.kindVars args)
    pure
      { type: XCon name args
      , kind: instantiateKindVars instantiated head.body
      , unwritten: map (\kind -> { origin: o, kind }) args
      , unsupported: []
      }
  TypeConstructor o name -> do
    env <- askEnv
    case Map.lookup name env.session.kinding.types of
      Just scheme -> do
        args <- traverse (\_ -> freshKindMeta scope.kindVars quantifiable) scheme.kindVars
        pure
          { type: XCon name args
          , kind: instantiate scheme args
          , unwritten: map (\kind -> { origin: o, kind }) args
          , unsupported: []
          }
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
    pure (joined [ a', b' ] (xFunction a'.type XRowEmpty b'.type) XKType)
  TypeFunction _ a b (Just row) -> do
    a' <- checkAt scope XKType a
    b' <- checkAt scope XKType b
    row' <- checkAt scope (XKRow RowEffect) row
    pure (joined [ a', b', row' ] (xFunction a'.type row'.type b'.type) XKType)
  TypeTuple _ components -> do
    read <- traverse (checkAt scope XKType) components
    let row = foldr (\(Tuple n c) rest -> XRowExtend (XRowTypeEntry (PositionKey n) c.type) rest) XRowEmpty (Array.mapWithIndex Tuple read)
    pure (joined read (XApp (XCon recordTy []) row) XKType)
  TypeRecord _ items -> do
    row <- rowOf scope RowType (map recordItem items)
    pure row { type = XApp (XCon recordTy []) row.type, kind = XKType }
  TypeVariant _ items -> do
    row <- rowOf scope RowType (map variantItem items)
    pure row { type = XApp (XCon variantTy []) row.type, kind = XKType }
  TypeEffectRow _ items -> rowOf scope RowEffect (map effectItem items)
  TypeOperator o op l r -> case op.target of
    TargetTypeConstructor name -> readType scope (TypeApp o (TypeApp o (TypeConstructor op.origin name) l) r)
    TargetTypeSynonym _ -> unsupported (OutsideSubset op.origin "a type synonym")
    TargetEffect effect -> unsupported (EffectAsType op.origin effect)
  TypeForall _ binders body -> do
    bound <- traverse (binder scope) binders
    let inner = scope { tyVars = foldr (\b m -> Map.insert (nameOf b.var) b.kind m) scope.tyVars bound }
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
  where
  plain ty kind = { type: ty, kind, unwritten: [], unsupported: [] }

  -- a form not read stands as a metavariable of a kind of its own
  unsupported problem = do
    kind <- freshKindMeta scope.kindVars Set.empty
    meta <- freshTypeMeta (emptyXContext { kindVars = scope.kindVars }) kind
    pure { type: meta, kind, unwritten: [], unsupported: [ problem ] }

joined :: Array Read -> XType -> XKind -> Read
joined parts ty kind =
  { type: ty, kind, unwritten: Array.concatMap _.unwritten parts, unsupported: Array.concatMap _.unsupported parts }

-- | An item of a row as written: an element, read by the action given, or a
-- | spread.
data RowItem
  = Element (Scope -> Elab { entry :: XRowEntry, read :: Read })
  | Spread Surface.Origin

recordItem :: RecordRowItem -> RowItem
recordItem = case _ of
  RecordField _ label t -> Element (typeEntry (SymbolKey label) t)
  RecordSpread o _ -> Spread o

variantItem :: VariantRowItem -> RowItem
variantItem = case _ of
  VariantTag _ tag t -> Element (typeEntry (TagKey tag) t)
  VariantLabel _ label t -> Element (typeEntry (SymbolKey label) t)
  VariantSpread o _ -> Spread o

effectItem :: EffectRowItem -> RowItem
effectItem = case _ of
  EffectElement application -> Element \scope -> do
    e <- effectApplication scope application
    pure { entry: XRowEffectEntry application.effect e.arguments, read: e.read }
  EffectInstance _ label application -> Element \scope -> do
    e <- effectApplication scope application
    pure { entry: XRowLabelledEffectEntry label application.effect e.arguments, read: e.read }
  EffectSpread o _ -> Spread o

-- | An element of a `Row Type`: its payload at `Type`, under its key.
typeEntry :: RowKey -> Type -> Scope -> Elab { entry :: XRowEntry, read :: Read }
typeEntry key t scope = do
  payload <- checkAt scope XKType t
  pure { entry: XRowTypeEntry key payload.type, read: payload }

-- | A row of the element kind given, its elements in the order written and
-- | nothing beyond them. A spread is outside what this version reads, and the
-- | row holding one is read with a metavariable for its tail.
rowOf :: Scope -> RowElemKind -> Array RowItem -> Elab Read
rowOf scope elementKind items = do
  elements <- traverse
    ( case _ of
        Element element -> Just <$> element scope
        Spread _ -> pure Nothing
    )
    items
  let spreads = Array.mapMaybe spreadOrigin items
  tail <-
    if Array.null spreads then pure XRowEmpty
    else freshTypeMeta (emptyXContext { kindVars = scope.kindVars }) (XKRow elementKind)
  let
    present = Array.catMaybes elements
    read = joined (map _.read present) (foldr (\e rest -> XRowExtend e.entry rest) tail present) (XKRow elementKind)
  pure read { unsupported = read.unsupported <> map (\o -> OutsideSubset o "a spread") spreads }
  where
  spreadOrigin = case _ of
    Spread o -> Just o
    Element _ -> Nothing

-- | An effect applied to its arguments, read as an application of something at
-- | the arrow of its parameters' kinds into `Effect`: each argument is read at
-- | the kind its parameter is declared at, and an effect applied to more or to
-- | fewer arguments than it has parameters is a kind that does not meet.
effectApplication :: Scope -> EffectApplication -> Elab { arguments :: Array XType, read :: Read }
effectApplication scope application = do
  env <- askEnv
  case Map.lookup application.effect env.session.kinding.effects of
    Nothing -> do
      r <- unreadEffect
      pure { arguments: [], read: r }
    Just params -> do
      read <- traverse (readType scope) application.arguments
      result <- foldM
        ( \kind argument -> do
            rest <- freshKindMeta scope.kindVars Set.empty
            equateKinds (siteOf scope (typeOrigin argument.written)) kind (XKFun argument.kind rest)
            pure rest
        )
        (foldr XKFun XKEffect (map fromCoreKind params))
        (Array.zipWith (\written r -> { written, kind: r.kind }) application.arguments read)
      equateKinds (siteOf scope application.origin) result XKEffect
      pure { arguments: map _.type read, read: joined read XRowEmpty XKEffect }
  where
  unreadEffect = pure
    { type: XRowEmpty
    , kind: XKEffect
    , unwritten: []
    , unsupported: [ OutsideSubset application.origin "an effect the signature does not hold" ]
    }

-- | A kind with the kind variables given replaced.
instantiateKindVars :: Map KindVar XKind -> XKind -> XKind
instantiateKindVars by = case _ of
  XKVar k | Just kind <- Map.lookup k by -> kind
  XKFun a b -> XKFun (instantiateKindVars by a) (instantiateKindVars by b)
  other -> other

-- | A binder of a `forall`, at the kind written or at a metavariable.
binder :: Scope -> TypeVarBinder -> Elab ReadBinder
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
  t -> Array.findMap (firstMention x) (typeParts t)

-- | The kind variables the kinds written in a type mention.
typeKindVars :: Type -> Array KindVar
typeKindVars t = written <> Array.concatMap typeKindVars (typeParts t)
  where
  written = case t of
    TypeForall _ binders _ -> Array.concatMap (\b -> maybe [] kindVars b.kind) binders
    TypeKinded _ _ k -> kindVars k
    _ -> []
  kindVars = case _ of
    KindArrow _ a b -> kindVars a <> kindVars b
    KindVariable _ v -> [ v ]
    _ -> []

-- | The types a type is written with, in the order written.
typeParts :: Type -> Array Type
typeParts = case _ of
  TypeApp _ f x -> [ f, x ]
  TypeOperator _ _ l r -> [ l, r ]
  TypeFunction _ a b row -> [ a, b ] <> Array.fromFoldable row
  TypeForall _ _ body -> [ body ]
  TypeConstrained _ c body -> [ c, body ]
  TypeKinded _ inner _ -> [ inner ]
  TypeTuple _ components -> components
  TypeRecord _ items -> Array.concatMap
    ( case _ of
        RecordField _ _ t -> [ t ]
        RecordSpread _ t -> Array.fromFoldable t
    )
    items
  TypeVariant _ items -> Array.concatMap
    ( case _ of
        VariantTag _ _ t -> [ t ]
        VariantLabel _ _ t -> [ t ]
        VariantSpread _ t -> Array.fromFoldable t
    )
    items
  TypeEffectRow _ items -> Array.concatMap
    ( case _ of
        EffectElement application -> application.arguments
        EffectInstance _ _ application -> application.arguments
        EffectSpread _ t -> Array.fromFoldable t
    )
    items
  TypeSynthesized _ _ t _ -> [ t ]
  _ -> []

-- | The Core scheme of a signature once its kinds are decided: every
-- | metavariable solved, or each place whose kind was left undetermined, once
-- | however many kinds stand there. A metavariable left where no such place
-- | accounts for it is reported where the signature's type stands.
settledScheme :: MetaContext -> Elaborated -> Either (NonEmptyArray Surface.Origin) TypeScheme
settledScheme metas e =
  case NonEmptyArray.fromArray (Array.nubEq (map _.origin (Array.filter undetermined e.unwritten))) of
    Just places -> Left places
    Nothing -> case toCore (substitute metas e.type) of
      Just body -> Right { kindVars: e.kindVars, body }
      Nothing -> Left (NonEmptyArray.singleton e.origin)
  where
  undetermined u = not (Set.isEmpty (kindMetasOf (substituteKind metas u.kind)))

derive instance Eq Unsupported

instance Show Unsupported where
  show = case _ of
    OutsideSubset o what -> "OutsideSubset (" <> show o <> ") " <> show what
    ReportedAlready o -> "ReportedAlready (" <> show o <> ")"
    EffectAsType o e -> "EffectAsType (" <> show o <> ") (" <> show e <> ")"
