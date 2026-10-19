-- | `Σ ok`, the contract every judgement presupposes of the signature.
-- |
-- | `Σ ok = Σ wf ∧ Σ prim`. Kinding, typing, and the safety argument read
-- | constructors, foreigns, and the classes of intrinsics out of `Σ` and rely
-- | on what they find there; this is the one statement of what that is. A
-- | signature a module's declarations produce satisfies it by construction,
-- | and one assembled from interfaces is checked against it rather than
-- | trusted to have arisen that way.
module Stella.Compiler.TypedCore.SignatureCheck
  ( SignatureError(..)
  , sigOk
  , sigWf
  , primWf
  , impureArrow
  , isEmptyRow
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.AttributeCheck (AttributeError, checkAttributeDecl)
import Stella.Compiler.TypedCore.Context (Context, bindKindVars, bindTyVar, emptyContext)
import Stella.Compiler.TypedCore.Decl (OpDecl)
import Stella.Compiler.TypedCore.Equality (typeEquiv)
import Stella.Compiler.TypedCore.Kind (Kind(..))
import Stella.Compiler.TypedCore.Kinding (KindError, checkKind, producesType, quantifiableKind)
import Stella.Compiler.TypedCore.Name (EffName, Ident, KindVar, OpName, Qualified(..), TyName)
import Stella.Compiler.TypedCore.Prim (asFunction, primModule, primSignature, pureFn)
import Stella.Compiler.TypedCore.Signature (AttributeInfo, CanonicalClass(..), CtorInfo, EffectInfo, Signature, TyConInfo(..), ValueInfo, tyConKind)
import Stella.Compiler.TypedCore.Type (RowEntry(..), TyBinder, Type(..), TypeScheme)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, foldl, foldr, traverse_)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))

-- | A signature that is not `Σ ok`, with the entry that makes it so.
data SignatureError
  -- | A name both a constructor and a value or foreign. A term's reference to
  -- | it would have no one scheme.
  = CtorValueCollision (Qualified Ident)
  -- | An effect keying an operation under a name other than the one its
  -- | declaration carries, as the key and the declared name.
  | OperationNameMismatch (Qualified EffName) OpName OpName
  -- | A type constructor's kind scheme that is not well formed, closed, and
  -- | producing `Type`.
  | TyConEntryError (Qualified TyName) KindError
  -- | An effect's parameters or one of its operations, ill kinded.
  | EffectEntryError (Qualified EffName) KindError
  -- | A constructor whose owner is no data type of `Σ`.
  | CtorOwnerNotData (Qualified Ident) (Qualified TyName)
  -- | A constructor its owner does not list, or lists more than once.
  | CtorListing (Qualified TyName) (Qualified Ident)
  -- | A constructor a data type lists that has no entry naming it as owner.
  | ListedCtorMissing (Qualified TyName) (Qualified Ident)
  -- | A constructor whose kind variables are not its owner's.
  | CtorKindVars (Qualified Ident)
  -- | A constructor whose type parameters are not its owner's: their kinds
  -- | differ from the owner's kind, or two share a name.
  | CtorParams (Qualified Ident)
  -- | A constructor whose scheme is not `forall k̄. forall (ā : κ̄). τ̄ -> T [[k̄]] ā`
  -- | over its own fields and parameters, with pure arrows.
  | CtorSchemeShape (Qualified Ident)
  | CtorEntryError (Qualified Ident) KindError
  | CtorTagCollision (Qualified TyName) P.Int
  | ValueEntryError (Qualified Ident) KindError
  -- | A foreign whose type carries an effect on an arrow where a value passes
  -- | through (D23), with the row it carries.
  | EffectfulForeignEntry (Qualified Ident) Type
  | AttributeEntryError (Qualified Ident) AttributeError
  -- | An entry of `Σ_Prim` missing or other than `Prim` fixes it.
  | PrimTyCon (Qualified TyName)
  | PrimCtor (Qualified Ident)
  | PrimAttribute (Qualified Ident)
  -- | An entry under `Prim` that `Σ_Prim` does not hold.
  | ForeignPrimEntry P.String
  -- | A type constructor outside `Prim` claiming a canonical-value class only
  -- | `Prim`'s may have.
  | ClassClaimed (Qualified TyName) CanonicalClass

sigOk :: Signature -> Either SignatureError Unit
sigOk sig = do
  sigWf sig
  primWf sig

-- | `Σ wf`.
sigWf :: Signature -> Either SignatureError Unit
sigWf sig = do
  traverse_ (Left <<< CtorValueCollision) (sharedKeys sig.ctors sig.values)
  traverse_ tyConOk (entries sig.types)
  traverse_ (effectOk sig) (entries sig.effects)
  traverse_ (ownerOk sig) (entries sig.types)
  traverse_ (ctorOk sig) (entries sig.ctors)
  traverse_ (valueOk sig) (entries sig.values)
  traverse_ (attributeOk sig) (entries sig.attributes)

-- | `Σ prim`: `Σ_Prim` as `Prim` fixes it, nothing else under `Prim`, and the
-- | canonical-value classes the rules dispatch on claimed by `Prim`'s type
-- | constructors alone.
-- |
-- | Every class but `opaque` comes with a canonical form the rules build and
-- | take apart: a literal, a `λ`, a record, a variant. A manifest intrinsic of
-- | one of them would be a type no value of which is canonical, a `foreign`'s
-- | result being an opaque value.
primWf :: Signature -> Either SignatureError Unit
primWf sig = do
  traverse_ (\(Tuple name info) -> unless (Map.lookup name sig.types == Just info) (Left (PrimTyCon name)))
    (entries primSignature.types)
  traverse_ (\(Tuple name info) -> unless (Map.lookup name sig.ctors == Just info) (Left (PrimCtor name)))
    (entries primSignature.ctors)
  traverse_ (\(Tuple name info) -> unless (Map.lookup name sig.attributes == Just info) (Left (PrimAttribute name)))
    (entries primSignature.attributes)
  traverse_ (\name -> unless (Map.member name primSignature.types) (Left (ForeignPrimEntry (show name))))
    (Array.filter inPrim (Array.fromFoldable (Map.keys sig.types)))
  traverse_ (\name -> unless (Map.member name primSignature.ctors) (Left (ForeignPrimEntry (show name))))
    (Array.filter inPrim (Array.fromFoldable (Map.keys sig.ctors)))
  traverse_ (Left <<< ForeignPrimEntry <<< show) (Array.filter inPrim (Array.fromFoldable (Map.keys sig.values)))
  traverse_ (Left <<< ForeignPrimEntry <<< show) (Array.filter inPrim (Array.fromFoldable (Map.keys sig.effects)))
  traverse_ (\name -> unless (Map.member name primSignature.attributes) (Left (ForeignPrimEntry (show name))))
    (Array.filter inPrim (Array.fromFoldable (Map.keys sig.attributes)))
  traverse_ classOk (entries sig.types)
  where
  inPrim :: forall n. Qualified n -> P.Boolean
  inPrim (Qualified m _) = m == primModule

  classOk (Tuple name info) = case info of
    IntrinsicTyCon _ cls
      | cls /= CanonicalOpaque && not (Map.member name primSignature.types) -> Left (ClassClaimed name cls)
    _ -> Right unit

-- | `T : forall k̄. κ` with `κ` a quantifiable kind under `k̄` alone, producing
-- | `Type`. A scheme such as `forall k. k` passes every use site that
-- | instantiates it at `Type` while producing a row at another, and neither an
-- | unbound kind variable nor a domain that cannot be quantified is visible
-- | from one occurrence.
tyConOk :: Tuple (Qualified TyName) TyConInfo -> Either SignatureError Unit
tyConOk (Tuple name info) = named (TyConEntryError name) do
  let scheme = tyConKind info
  quantifiableKind (bindKindVars emptyContext scheme.kindVars) scheme.body
  producesType scheme.body

-- | What an `effect` declaration would have produced: the parameters and an
-- | operation's own binders at a quantifiable kind (D24), the argument and the
-- | resumption type at `Type`, and every type variable in scope. An effect
-- | constructor binds no kind variable, so the context starts from the
-- | parameters alone (D3).
-- |
-- | The operations are keyed by the name each declares, which is what
-- | `Σ(E).op` is looked up by; an entry keying one name to a declaration
-- | carrying another would answer a lookup with a signature belonging to
-- | something else.
effectOk :: Signature -> Tuple (Qualified EffName) EffectInfo -> Either SignatureError Unit
effectOk sig (Tuple name info) = do
  named (EffectEntryError name) (traverse_ (\binder -> quantifiableKind emptyContext binder.kind) info.params)
  traverse_ operationOk (entries info.operations)
  where
  operationOk :: Tuple OpName OpDecl -> Either SignatureError Unit
  operationOk (Tuple key op) = do
    when (key /= op.name) (Left (OperationNameMismatch name key op.name))
    named (EffectEntryError name) do
      let ctx = paramContext [] info.params
      traverse_ (\binder -> quantifiableKind ctx binder.kind) op.tyBinders
      let inner = foldl (\acc binder -> bindTyVar acc binder.name binder.kind) ctx op.tyBinders
      checkKind sig inner op.argument KType
      checkKind sig inner op.resumesWith KType

-- | A data type lists exactly the constructors naming it as owner, each once.
ownerOk :: Signature -> Tuple (Qualified TyName) TyConInfo -> Either SignatureError Unit
ownerOk sig (Tuple owner info) = case info of
  IntrinsicTyCon _ _ -> Right unit
  DataTyCon _ listed -> do
    traverse_ (Left <<< CtorListing owner) (duplicates listed)
    traverse_
      ( \ctor -> case Map.lookup ctor sig.ctors of
          Just entry | entry.owner == owner -> Right unit
          _ -> Left (ListedCtorMissing owner ctor)
      )
      listed
    void (foldM (tagOk owner) Set.empty (Array.mapMaybe (\c -> map _.tag (Map.lookup c sig.ctors)) listed))

-- | `Ctor : forall k̄. forall (ā : κ̄). τ1 -> … -> τn -> T [[k̄]] ā`, exactly.
-- |
-- | `k̄` and `(ā : κ̄)` are the owner's, `τ̄` is the stored field list, each
-- | field of kind `Type` under them, and every arrow is pure. Taking a
-- | constructor's value apart instantiates the stored fields at the
-- | scrutinee's own arguments, so a constructor of `T Int` declared
-- | `forall a. a -> T Int` would hand a branch a field at one type while the
-- | value carries another. The fields are kinded themselves rather than
-- | through the scheme, `typeEquiv` relating ill-kinded types as well.
ctorOk :: Signature -> Tuple (Qualified Ident) CtorInfo -> Either SignatureError Unit
ctorOk sig (Tuple name info) = case Map.lookup info.owner sig.types of
  Just (DataTyCon ownerKind listed) -> do
    unless (Array.elem name listed) (Left (CtorListing info.owner name))
    unless (info.scheme.kindVars == ownerKind.kindVars) (Left (CtorKindVars name))
    unless
      ( ownerKind.body == foldr KFun KType (map _.kind info.params)
          && Array.length (Array.nub (map _.name info.params)) == Array.length info.params
      )
      (Left (CtorParams name))
    named (CtorEntryError name) do
      checkScheme sig info.scheme
      let ctx = paramContext ownerKind.kindVars info.params
      traverse_ (\field -> checkKind sig ctx field KType) info.fields
    let
      result = foldl TApp (TCon info.owner (map KVar ownerKind.kindVars)) (map (TVar <<< _.name) info.params)
      expected = foldr (\binder body -> TForall binder.name binder.kind body) (foldr pureFn result info.fields) info.params
    unless (typeEquiv expected info.scheme.body) (Left (CtorSchemeShape name))
  _ -> Left (CtorOwnerNotData name info.owner)

tagOk :: Qualified TyName -> Set.Set P.Int -> P.Int -> Either SignatureError (Set.Set P.Int)
tagOk owner seen tag
  | Set.member tag seen = Left (CtorTagCollision owner tag)
  | otherwise = Right (Set.insert tag seen)

-- | A value's or a foreign's scheme is well kinded, and a foreign's arrows are
-- | pure wherever a value passes through (D23).
valueOk :: Signature -> Tuple (Qualified Ident) ValueInfo -> Either SignatureError Unit
valueOk sig (Tuple name info) = do
  named (ValueEntryError name) (checkScheme sig info.scheme)
  when info.isForeign case impureArrow info.scheme.body of
    Just row -> Left (EffectfulForeignEntry name row)
    Nothing -> Right unit

attributeOk :: Signature -> Tuple (Qualified Ident) AttributeInfo -> Either SignatureError Unit
attributeOk sig (Tuple name info) = case checkAttributeDecl sig info of
  Left err -> Left (AttributeEntryError name err)
  Right _ -> Right unit

-- | `σκ = forall k̄. σ` with `·, k̄ ⊢ σ : Type`.
checkScheme :: Signature -> TypeScheme -> Either KindError Unit
checkScheme sig scheme = checkKind sig (bindKindVars emptyContext scheme.kindVars) scheme.body KType

-- | The row of an arrow performing effects that the type holds where a value
-- | passes through, a constraint's own types aside.
-- |
-- | A constraint is an erased proposition and carries no value across the
-- | `foreign` boundary, so the arrows inside one are not traversed: neither
-- | handler bypass nor a leaking calling convention can arise there.
impureArrow :: Type -> Maybe Type
impureArrow ty = case asFunction ty of
  Just parts | not (isEmptyRow parts.row) -> Just parts.row
  _ -> case ty of
    TApp f x -> orElse (impureArrow f) (impureArrow x)
    TForall _ _ body -> impureArrow body
    TConstrained _ body -> impureArrow body
    TRowExtend entry rest -> orElse (entryImpureArrow entry) (impureArrow rest)
    TRowUnion left right -> orElse (impureArrow left) (impureArrow right)
    _ -> Nothing

-- | An arrow reaches the boundary through the payload of a row element as
-- | readily as through an argument: `Record ( cb : a -{ρ}-> b )` hands a
-- | callback across it.
entryImpureArrow :: RowEntry -> Maybe Type
entryImpureArrow = case _ of
  RowTypeEntry _ ty -> impureArrow ty
  RowEffectEntry _ args -> Array.findMap impureArrow args
  RowLabelledEffectEntry _ _ args -> Array.findMap impureArrow args
  -- A region carries only its name, through which nothing crosses.
  RowRegionEntry _ -> Nothing

-- | Whether a row holds no element and no tail.
isEmptyRow :: Type -> P.Boolean
isEmptyRow row = typeEquiv row TRowEmpty

paramContext :: P.Array KindVar -> P.Array TyBinder -> Context
paramContext kindVars params =
  foldl (\ctx binder -> bindTyVar ctx binder.name binder.kind) (bindKindVars emptyContext kindVars) params

named :: forall e b. (e -> SignatureError) -> Either e b -> Either SignatureError b
named onError = case _ of
  Left err -> Left (onError err)
  Right value -> Right value

entries :: forall k v. Map k v -> P.Array (Tuple k v)
entries = Map.toUnfoldable

sharedKeys :: forall k v w. Ord k => Map k v -> Map k w -> P.Array k
sharedKeys left right =
  Set.toUnfoldable (Set.intersection (Set.fromFoldable (Map.keys left)) (Set.fromFoldable (Map.keys right)))

duplicates :: forall a. Ord a => P.Array a -> P.Array a
duplicates xs = Array.nub (Array.filter (\x -> Array.length (Array.filter (_ == x) xs) > 1) xs)

orElse :: forall x. Maybe x -> Maybe x -> Maybe x
orElse first second = case first of
  Just _ -> first
  Nothing -> second

derive instance Eq SignatureError
derive instance Generic SignatureError _

instance Show SignatureError where
  show x = genericShow x
