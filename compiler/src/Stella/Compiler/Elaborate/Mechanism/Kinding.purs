-- | The kinding judgement over Core⁺, read-only: `Σκ ; Γ ; Ψ ⊢ τ⁺ ⇒ k`.
-- |
-- | It changes nothing and creates nothing. It checks as well as synthesizes:
-- | what it answers is whether a type may be shown with the kind evidence it
-- | gives, so a type it reaches that is ill-kinded is refused rather than given a
-- | kind. Every type a synthesizer observes passes through it, whether a builder
-- | made it or the elaborator did.
-- |
-- | **Every kind it answers with is settled.** Kinds and types are zonked against
-- | the current `Ψ` first, and a kind metavariable still standing anywhere the
-- | judgement reads — a variable's kind, a constructor's kind argument, a binder,
-- | a kind being synthesized — is refused as `KindNotSettled`. A synthesizer
-- | runs after the kinds of what it observes are decided, and a kind it could
-- | neither name nor wait on is one it must not be shown.
module Stella.Compiler.Elaborate.Mechanism.Kinding
  ( KindingEnv
  , KindEvidence(..)
  , KindingFault(..)
  , KindingScope
  , emptyScope
  , emptyKindingEnv
  , kindingOf
  , synthKind
  , checkConstraint
  , checkKind
  , settled
  , settledIn
  , quantifiable
  , wellFormedKey
  , instantiate
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..), fromCoreKind, kindMetasOf, kindVarsOf)
import Stella.Compiler.Elaborate.CorePlus.Type (MetaVar, XConstraint(..), XRowEntry(..), XType(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (MetaBinding(..), MetaContext, lookupMeta, substitute, substituteKind)
import Stella.Compiler.TypedCore (EffName, Kind, KindScheme, KindVar, Qualified, RegionName, RowElemKind(..), RowKey(..), Signature, TyName, TyVar, tyConKind)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (traverse_)
import Data.Traversable (traverse)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | The type-level part of the environment: the kind scheme of every type
-- | constructor, and the parameter kinds of every effect. It is assembled before
-- | the first job and its domain is fixed, as the value catalog's is; the two are
-- | separate, holding different namespaces.
type KindingEnv =
  { types :: Map (Qualified TyName) KindScheme
  , effects :: Map (Qualified EffName) (P.Array Kind)
  }

-- | The variables a type may mention free: the rigid kind variables in scope,
-- | the type variables with their kinds, and the region names.
type KindingScope =
  { kindVars :: Set KindVar
  , tyVars :: Map TyVar XKind
  , regions :: Set RegionName
  }

emptyScope :: KindingScope
emptyScope = { kindVars: Set.empty, tyVars: Map.empty, regions: Set.empty }

-- | What a type stands at.
data KindEvidence
  -- | One kind, zonked and holding no kind metavariable.
  = ExactKind XKind
  -- | Any row kind: what a row with no element and no tail stands at. It is not
  -- | a choice left open but the whole of what is true of such a row.
  | AnyRow

data KindingFault
  = UnboundTyVar TyVar
  | UnboundKindVar KindVar
  -- | A region name the scope does not bind.
  | UnboundRegion RegionName
  | NegativePosition P.Int
  | UnknownTyCon (Qualified TyName)
  | UnknownEffect (Qualified EffName)
  | UnknownMeta MetaVar
  -- | A kind metavariable where the judgement needs a settled kind.
  | KindNotSettled
  | KindArityMismatch (Qualified TyName) P.Int P.Int
  | EffectArityMismatch (Qualified EffName) P.Int P.Int
  | NotQuantifiable XKind
  | NotAFunctionKind XKind
  -- | A type standing at what it was required not to.
  | KindMismatch KindEvidence XKind
  -- | A key a row of the kind given cannot carry.
  | KeyNotOfRowKind RowKey RowElemKind
  -- | Two rows joined, or constrained together, at different row kinds.
  | RowKindsDiffer RowElemKind RowElemKind

emptyKindingEnv :: KindingEnv
emptyKindingEnv = { types: Map.empty, effects: Map.empty }

-- | The type-level part of a signature. Its values are not read: what names a
-- | value is the catalog's.
kindingOf :: Signature -> KindingEnv
kindingOf sig =
  { types: map tyConKind sig.types
  , effects: map (\info -> map _.kind info.params) sig.effects
  }

-- | A kind, zonked, where it holds no kind metavariable.
settled :: MetaContext -> XKind -> Either KindingFault XKind
settled metas kind =
  let
    k = substituteKind metas kind
  in
    if Set.isEmpty (kindMetasOf k) then Right k else Left KindNotSettled

-- | A kind, zonked, where it holds no kind metavariable and every kind variable
-- | it mentions is one the scope binds.
settledIn :: KindingScope -> MetaContext -> XKind -> Either KindingFault XKind
settledIn scope metas kind = do
  k <- settled metas kind
  case Set.findMin (Set.difference (kindVarsOf k) scope.kindVars) of
    Just v -> Left (UnboundKindVar v)
    Nothing -> Right k

-- | The kind evidence of a type, under the scope given.
synthKind :: KindingEnv -> KindingScope -> MetaContext -> XType -> Either KindingFault KindEvidence
synthKind env scope metas ty = (judgement env scope metas).synth scope.tyVars (substitute metas ty)

-- | `Γ ⊢ C ok`, under the scope given: each row is a row, a `Lacks`'s key is
-- | well-formed for its row, and a `Disjoint`'s sides stand at one row kind.
-- |
-- | This is the one judgement of a constraint's well-formedness. A constrained
-- | type is kinded through it, and so is every constraint a kernel operation is
-- | given.
checkConstraint :: KindingEnv -> KindingScope -> MetaContext -> XConstraint -> Either KindingFault Unit
checkConstraint env scope metas c = (judgement env scope metas).constraint scope.tyVars zonked
  where
  zonked = case c of
    XLacks key row -> XLacks key (substitute metas row)
    XDisjoint l r -> XDisjoint (substitute metas l) (substitute metas r)

-- The judgement over types and over constraints, which are kinded through each
-- other.
judgement
  :: KindingEnv
  -> KindingScope
  -> MetaContext
  -> { synth :: Map TyVar XKind -> XType -> Either KindingFault KindEvidence
     , constraint :: Map TyVar XKind -> XConstraint -> Either KindingFault Unit
     }
judgement env scope metas = { synth, constraint }
  where
  wellFormed = settledIn scope metas

  synth vars = case _ of
    XVar a -> case Map.lookup a vars of
      Just k -> ExactKind <$> wellFormed k
      Nothing -> Left (UnboundTyVar a)

    XMeta m -> case lookupMeta metas m of
      Just (Unsolved info) -> ExactKind <$> wellFormed info.kind
      _ -> Left (UnknownMeta m)

    XCon name kinds -> case Map.lookup name env.types of
      Nothing -> Left (UnknownTyCon name)
      Just scheme
        | Array.length scheme.kindVars /= Array.length kinds ->
            Left (KindArityMismatch name (Array.length scheme.kindVars) (Array.length kinds))
        | otherwise -> do
            args <- traverse (\k -> wellFormed k >>= quantifiable) kinds
            pure (ExactKind (instantiate scheme args))

    XApp f a -> do
      head <- synth vars f
      case head of
        ExactKind (XKFun domain result) -> do
          check vars domain a
          pure (ExactKind result)
        ExactKind other -> Left (NotAFunctionKind other)
        AnyRow -> Left (KindMismatch AnyRow (XKFun XKType XKType))

    XForall a kind body -> do
      k <- wellFormed kind >>= quantifiable
      check (Map.insert a k vars) XKType body
      pure (ExactKind XKType)

    XConstrained c body -> do
      constraint vars c
      check vars XKType body
      pure (ExactKind XKType)

    XRowEmpty -> Right AnyRow

    XRowExtend entry rest -> do
      element <- entryKind vars entry
      check vars (XKRow element) rest
      pure (ExactKind (XKRow element))

    XRowUnion l r -> do
      left <- synth vars l
      right <- synth vars r
      combine left right

  check vars expected t = do
    ev <- synth vars t
    case ev of
      ExactKind k | k == expected -> Right unit
      AnyRow | isRow expected -> Right unit
      _ -> Left (KindMismatch ev expected)

  entryKind vars = case _ of
    XRowTypeEntry key payload -> do
      wellFormedKey env scope.regions key (Just RowType)
      check vars XKType payload
      pure RowType
    XRowEffectEntry e args -> do
      effectArgs vars e args
      pure RowEffect
    XRowLabelledEffectEntry _ e args -> do
      effectArgs vars e args
      pure RowEffect
    XRowRegionEntry name
      | Set.member name scope.regions -> pure RowEffect
      | otherwise -> Left (UnboundRegion name)

  effectArgs vars e args = case Map.lookup e env.effects of
    Nothing -> Left (UnknownEffect e)
    Just params
      | Array.length params /= Array.length args ->
          Left (EffectArityMismatch e (Array.length params) (Array.length args))
      | otherwise ->
          traverse_ (\(Tuple k a) -> check vars (fromCoreKind k) a) (Array.zip params args)

  constraint vars = case _ of
    XLacks key row -> do
      ev <- synth vars row
      case ev of
        ExactKind (XKRow e) -> wellFormedKey env scope.regions key (Just e)
        AnyRow -> wellFormedKey env scope.regions key Nothing
        ExactKind other -> Left (KindMismatch (ExactKind other) (XKRow RowType))
    XDisjoint l r -> do
      left <- synth vars l
      right <- synth vars r
      void (combine left right)

  combine left right = case left, right of
    AnyRow, AnyRow -> Right AnyRow
    AnyRow, ExactKind k | isRow k -> Right (ExactKind k)
    ExactKind k, AnyRow | isRow k -> Right (ExactKind k)
    ExactKind (XKRow a), ExactKind (XKRow b)
      | a == b -> Right (ExactKind (XKRow a))
      | otherwise -> Left (RowKindsDiffer a b)
    ExactKind k, _ | not (isRow k) -> Left (KindMismatch left (XKRow RowType))
    _, ExactKind k -> Left (KindMismatch (ExactKind k) (XKRow RowType))
    _, _ -> Left (KindMismatch right (XKRow RowType))

-- | Whether a type stands at the kind given, under the scope given.
checkKind :: KindingEnv -> KindingScope -> MetaContext -> XKind -> XType -> Either KindingFault Unit
checkKind env scope metas expected ty = do
  ev <- synthKind env scope metas ty
  case ev of
    ExactKind k | k == expected -> Right unit
    AnyRow | isRow expected -> Right unit
    _ -> Left (KindMismatch ev expected)

-- | `Γ ⊢ k key ε`, for a row of the kind given where one is known.
-- |
-- | Every key is judged by this one rule, whether it is an element's or a
-- | constraint's. A position is non-negative; a structural key keys a `Row Type`,
-- | a `SymbolKey` either row kind, and an `EffectKey` or a `RegionKey` a
-- | `Row Effect`; an `EffectKey` names a declared effect, and a `RegionKey` one of
-- | the region names given, which are those in scope.
wellFormedKey :: KindingEnv -> Set RegionName -> RowKey -> Maybe RowElemKind -> Either KindingFault Unit
wellFormedKey env regions key element = case key of
  PositionKey n | n < 0 -> Left (NegativePosition n)
  EffectKey e | not (Map.member e env.effects) -> Left (UnknownEffect e)
  _ -> case element, keyKind key of
    Just e, Just k | e /= k -> Left (KeyNotOfRowKind key e)
    _, _ -> case key of
      RegionKey name | not (Set.member name regions) -> Left (UnboundRegion name)
      _ -> Right unit

isRow :: XKind -> P.Boolean
isRow = case _ of
  XKRow _ -> true
  _ -> false

-- | `Γ ⊢ κ qkind`, over a settled kind (D24).
quantifiable :: XKind -> Either KindingFault XKind
quantifiable kind = if ok kind then Right kind else Left (NotQuantifiable kind)
  where
  ok = case _ of
    XKVar _ -> true
    XKType -> true
    XKRow _ -> true
    XKEffect -> false
    XKMeta _ -> false
    XKFun a b -> ok a && ok b && producesType b

  producesType = case _ of
    XKType -> true
    XKFun _ b -> producesType b
    _ -> false

-- | The row kind a key settles, where it settles one. A `SymbolKey` keys a field
-- | and a labelled effect instance alike, so it settles none.
keyKind :: RowKey -> Maybe RowElemKind
keyKind = case _ of
  TagKey _ -> Just RowType
  PositionKey _ -> Just RowType
  EffectKey _ -> Just RowEffect
  RegionKey _ -> Just RowEffect
  SymbolKey _ -> Nothing

instantiate :: KindScheme -> P.Array XKind -> XKind
instantiate scheme args =
  fromCoreKindWith (Map.fromFoldable (Array.zip scheme.kindVars args)) scheme.body
  where
  fromCoreKindWith subst kind = substituteKindVars subst (fromCoreKind kind)

  substituteKindVars subst = case _ of
    XKVar v -> case Map.lookup v subst of
      Just k -> k
      Nothing -> XKVar v
    XKFun a b -> XKFun (substituteKindVars subst a) (substituteKindVars subst b)
    other -> other

derive instance Eq KindEvidence
derive instance Generic KindEvidence _

instance Show KindEvidence where
  show x = genericShow x

derive instance Eq KindingFault
derive instance Generic KindingFault _

instance Show KindingFault where
  show x = genericShow x
