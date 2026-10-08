-- | The kinding judgements of Typed Core.
-- |
-- | `Γ ⊢ κ kind`, `Γ ⊢ κ qkind`, `Γ ⊢ k key ε`, `Γ ⊢ τ : κ`, and `Γ ⊢ C ok`.
-- |
-- | Kinding is where a row becomes sharp. Row extension and row union each carry
-- | an entailment side condition, so a well-kinded row has no key twice and a
-- | well-kinded union is disjoint; what normalization reports defensively is
-- | decided here.
module Stella.Compiler.TypedCore.Kinding
  ( Synthesized(..)
  , KindError(..)
  , wellFormedKind
  , quantifiableKind
  , wellFormedKey
  , producesType
  , wellFormedConstraint
  , kindOf
  , checkKind
  , rowElemKindOf
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Context (Context, assume, bindTyVar, kindVarInScope, lookupRegion, lookupTyVar)
import Stella.Compiler.TypedCore.Entailment (DecomposeError, entails)
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), resultKind, substituteKind)
import Stella.Compiler.TypedCore.Name (EffName, KindVar, Qualified, RegionName, TyName, TyVar)
import Stella.Compiler.TypedCore.Signature (Signature, effectParamKinds, lookupEffect, lookupTyCon, tyConKind)
import Stella.Compiler.TypedCore.Type (Constraint(..), RowEntry(..), RowKey(..), Type(..), rowEntryKey)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (traverse_)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | What kinding synthesizes.
-- |
-- | The rule for `()` is schematic in `ε`, so the empty row has no one kind.
-- | `AnyRow` is that answer, and it stands wherever a row kind is required.
data Synthesized
  = Kinded Kind
  | AnyRow

data KindError
  = UnboundTyVar TyVar
  -- | A kind variable outside the declaration whose scheme binds it. Neither
  -- | grammar has a kind quantifier, so this is the only way one is bound (D3).
  | UnboundKindVar KindVar
  -- | A region name outside the `region` binder that binds it.
  | UnboundRegion RegionName
  | UndeclaredTyCon (Qualified TyName)
  | UndeclaredEffect (Qualified EffName)
  -- | `T [[κ̄']]` supplying a number of kinds the scheme does not bind, as
  -- | expected and actual.
  | KindArgCount (Qualified TyName) P.Int P.Int
  -- | A kind where a quantifiable one is required (D24). It names the part that
  -- | is not quantifiable, which for `Type -> Effect` is `Effect`.
  | NotQuantifiable Kind
  -- | A kind producing something other than `Type` where only a type
  -- | constructor may stand. It names the result found.
  | ResultNotType Kind
  -- | `τ1 τ2` where `τ1` is not of a function kind.
  | AppliedNonConstructor Type
  -- | `Γ ⊢ τ : κ` where `τ` has another kind.
  | ExpectedKind Type Kind Synthesized
  -- | A row operator over something that is not a row.
  | NotARowKind Type Kind
  -- | `Γ ⊬ k key ε`. A `TagKey` and a `PositionKey` are confined to `Row Type`,
  -- | and an `EffectKey` to `Row Effect`.
  | KeyNotAtKind RowKey RowElemKind
  -- | The index of a `PositionKey` is a `Nat`.
  | NegativePosition P.Int
  -- | `E τ̄` applying an effect constructor to a number of arguments its
  -- | declaration does not take, as expected and actual.
  | EffectArgCount (Qualified EffName) P.Int P.Int
  -- | `Γ ⊭ k ∉ ρ`, the sharpness condition of row extension.
  | NotSharp RowKey Type
  -- | `Γ ⊭ ρ1 # ρ2`, the disjointness condition of row union.
  | NotDisjoint Type Type
  -- | A side condition reached no verdict, the context or the row being at
  -- | fault rather than the constraint.
  | EntailmentError DecomposeError

-- | `Γ ⊢ κ kind`.
-- |
-- | `Row` has no rule of its own: `KRow` takes a row element kind, which is what
-- | keeps `Row (Type -> Type)` out of the grammar.
wellFormedKind :: Context -> Kind -> Either KindError Unit
wellFormedKind ctx = case _ of
  KVar k -> inScope ctx k
  KType -> Right unit
  KEffect -> Right unit
  KRow _ -> Right unit
  KFun a b -> wellFormedKind ctx a *> wellFormedKind ctx b

-- | `Γ ⊢ κ qkind`.
-- |
-- | Every quantifiable kind is a kind. What is missing is a rule for `Effect`,
-- | and that absence is D24: abstracting over a single effect is done with a
-- | `Row Effect` variable, which keeps a type variable off the head of a row
-- | element and so keeps every key rigid.
-- |
-- | An arrow is quantifiable only where it produces `Type`. A row is produced
-- | by row syntax alone, so that every well-kinded row has a normal form; a
-- | kind variable stands in result position no more than a row kind does, since
-- | it may be instantiated with one.
quantifiableKind :: Context -> Kind -> Either KindError Unit
quantifiableKind ctx = case _ of
  KVar k -> inScope ctx k
  KType -> Right unit
  KEffect -> Left (NotQuantifiable KEffect)
  KRow _ -> Right unit
  KFun a b -> do
    quantifiableKind ctx a
    quantifiableKind ctx b
    producesType b

-- | `Γ ⊢ k key ε`.
-- |
-- | A structural key is well formed wherever it may occur, needing nothing from
-- | `Σ`; an `EffectKey` is well formed only where the declaration exists, and a
-- | `RegionKey` only where its region name is in scope.
wellFormedKey :: Signature -> Context -> RowKey -> RowElemKind -> Either KindError Unit
wellFormedKey sig ctx key elemKind = case key of
  PositionKey n | n < 0 -> Left (NegativePosition n)
  _ -> case key, elemKind of
    SymbolKey _, _ -> Right unit
    TagKey _, RowType -> Right unit
    PositionKey _, RowType -> Right unit
    EffectKey name, RowEffect -> case lookupEffect sig name of
      Just _ -> Right unit
      Nothing -> Left (UndeclaredEffect name)
    RegionKey name, RowEffect -> regionInScope ctx name
    _, _ -> Left (KeyNotAtKind key elemKind)

-- | `Γ ⊢ C ok`.
-- |
-- | The rules are schematic in `ε`, and a constraint over the empty row fixes
-- | none; the key has then only to be a key at some `ε`.
wellFormedConstraint :: Signature -> Context -> Constraint -> Either KindError Unit
wellFormedConstraint sig ctx = case _ of
  Lacks key row -> do
    elemKind <- rowElemKindOf sig ctx row
    case elemKind of
      Just e -> wellFormedKey sig ctx key e
      Nothing -> case wellFormedKey sig ctx key RowType of
        Right _ -> Right unit
        Left _ -> wellFormedKey sig ctx key RowEffect

  Disjoint left right -> do
    l <- rowElemKindOf sig ctx left
    r <- rowElemKindOf sig ctx right
    void (agreeingElemKind right l r)

-- | `Γ ⊢ τ : κ`, synthesizing the kind.
kindOf :: Signature -> Context -> Type -> Either KindError Synthesized
kindOf sig ctx = case _ of
  TVar a -> case lookupTyVar ctx a of
    Just kind -> Right (Kinded kind)
    Nothing -> Left (UnboundTyVar a)

  -- Instantiation is explicit, so this is substitution alone: the kinds are
  -- written in the type, and the rule verifies their number and their layer.
  TCon name args -> case map tyConKind (lookupTyCon sig name) of
    Nothing -> Left (UndeclaredTyCon name)
    Just scheme -> do
      let expected = Array.length scheme.kindVars
      let actual = Array.length args
      when (expected /= actual) (Left (KindArgCount name expected actual))
      traverse_ (quantifiableKind ctx) args
      let kind = substituteKind (Map.fromFoldable (Array.zip scheme.kindVars args)) scheme.body
      -- The kind of a type constructor produces `Type`. Verifying it here
      -- rather than trusting `Σ` is what makes the shape of a row an invariant
      -- of kinding: a type of kind `Row ε` is row syntax and nothing else.
      producesType kind
      Right (Kinded kind)

  TApp f x -> do
    applied <- kindOf sig ctx f
    case applied of
      Kinded (KFun domain codomain) -> do
        checkKind sig ctx x domain
        Right (Kinded codomain)
      _ -> Left (AppliedNonConstructor f)

  TForall a kind body -> do
    quantifiableKind ctx kind
    checkKind sig (bindTyVar ctx a kind) body KType
    Right (Kinded KType)

  -- The constraint is assumed while the body is kinded. A type such as
  -- `(k ∉ r) => Record ( k : τ | r )` is sharp only under its own constraint,
  -- so kinding the body without it would leave no constrained row type
  -- well-kinded.
  TConstrained constraint body -> do
    wellFormedConstraint sig ctx constraint
    case assume ctx constraint of
      Left err -> Left (EntailmentError err)
      Right assumed -> do
        checkKind sig assumed body KType
        Right (Kinded KType)

  TRowEmpty -> Right AnyRow

  TRowExtend entry rest -> do
    elemKind <- entryElemKind sig ctx entry
    checkKind sig ctx rest (KRow elemKind)
    let key = rowEntryKey entry
    require ctx (Lacks key rest) (NotSharp key rest)
    Right (Kinded (KRow elemKind))

  TRowUnion left right -> do
    l <- rowElemKindOf sig ctx left
    r <- rowElemKindOf sig ctx right
    elemKind <- agreeingElemKind right l r
    require ctx (Disjoint left right) (NotDisjoint left right)
    Right (maybe AnyRow (Kinded <<< KRow) elemKind)

-- | `Γ ⊢ τ : κ` where the kind is already known, which is how most of the rules
-- | use the judgement.
checkKind :: Signature -> Context -> Type -> Kind -> Either KindError Unit
checkKind sig ctx ty expected = do
  actual <- kindOf sig ctx ty
  case actual, expected of
    Kinded kind, _ | kind == expected -> Right unit
    AnyRow, KRow _ -> Right unit
    _, _ -> Left (ExpectedKind ty expected actual)

-- | The `ε` of `Γ ⊢ ρ : Row ε`, absent where the row is empty and stands at
-- | either.
rowElemKindOf :: Signature -> Context -> Type -> Either KindError (Maybe RowElemKind)
rowElemKindOf sig ctx ty = do
  kind <- kindOf sig ctx ty
  case kind of
    AnyRow -> Right Nothing
    Kinded (KRow elemKind) -> Right (Just elemKind)
    Kinded other -> Left (NotARowKind ty other)

-- | `Γ ⊢ ent : ε entry`.
-- |
-- | At `Row Type` the key is written and the payload is a type. At `Row Effect`
-- | the payload is a saturated application of a declared effect constructor,
-- | whether or not a key is written for it.
entryElemKind :: Signature -> Context -> RowEntry -> Either KindError RowElemKind
entryElemKind sig ctx = case _ of
  RowTypeEntry key ty -> do
    wellFormedKey sig ctx key RowType
    checkKind sig ctx ty KType
    Right RowType

  RowEffectEntry name args -> effectPayload sig ctx name args

  RowLabelledEffectEntry _ name args -> effectPayload sig ctx name args

  -- A region consults the signature nowhere: it names no declaration, which is
  -- why nothing can declare one (D36). Its name must be in scope.
  RowRegionEntry name -> do
    regionInScope ctx name
    Right RowEffect

-- | `( E : κ̄ -> Effect ) ∈ Σ` and `Γ ⊢ τ̄ : κ̄`.
effectPayload
  :: Signature
  -> Context
  -> Qualified EffName
  -> P.Array Type
  -> Either KindError RowElemKind
effectPayload sig ctx name args = case lookupEffect sig name of
  Nothing -> Left (UndeclaredEffect name)
  Just info -> do
    let kinds = effectParamKinds info
    let expected = Array.length kinds
    let actual = Array.length args
    when (expected /= actual) (Left (EffectArgCount name expected actual))
    traverse_ (\(Tuple ty kind) -> checkKind sig ctx ty kind) (Array.zip args kinds)
    Right RowEffect

-- | Both sides of a union, and of a `#`, stand at one `ε`.
agreeingElemKind
  :: Type
  -> Maybe RowElemKind
  -> Maybe RowElemKind
  -> Either KindError (Maybe RowElemKind)
agreeingElemKind right l r = case l, r of
  Just a, Just b
    | a == b -> Right (Just a)
    | otherwise -> Left (ExpectedKind right (KRow a) (Kinded (KRow b)))
  Just a, Nothing -> Right (Just a)
  Nothing, _ -> Right r

-- | A side condition of the kinding rules. It is decided, never assumed: what
-- | makes a row sharp is that the context proves the key absent.
require :: Context -> Constraint -> KindError -> Either KindError Unit
require ctx constraint failure = case entails ctx.facts constraint of
  Left err -> Left (EntailmentError err)
  Right true -> Right unit
  Right false -> Left failure

-- | The result of a kind is `Type`.
-- |
-- | This holds of the kind of every type constructor and of every arrow inside
-- | a quantifiable kind, and it is what confines a row to row syntax.
producesType :: Kind -> Either KindError Unit
producesType kind = case resultKind kind of
  KType -> Right unit
  other -> Left (ResultNotType other)

inScope :: Context -> KindVar -> Either KindError Unit
inScope ctx k
  | kindVarInScope ctx k = Right unit
  | otherwise = Left (UnboundKindVar k)

derive instance Eq Synthesized
derive instance Generic Synthesized _

instance Show Synthesized where
  show x = genericShow x

derive instance Eq KindError
derive instance Generic KindError _

instance Show KindError where
  show x = genericShow x

regionInScope :: Context -> RegionName -> Either KindError Unit
regionInScope ctx name = case lookupRegion ctx name of
  Just _ -> Right unit
  Nothing -> Left (UnboundRegion name)
