-- | Row normal forms.
-- |
-- | A row is a keyed, unordered, duplicate-free collection, so its normal form
-- | is a finite map from keys to payloads together with a set of row variables
-- | standing for the unknown tail. Normalization never closes a row variable,
-- | which is what makes row equality decidable on open rows.
-- |
-- | Keys are rigid — a structural key is a literal (D13) and a derived effect
-- | key is the head constructor (D16) — so no key changes while a row is
-- | normalized.
module Stella.Compiler.TypedCore.Row
  ( RowNormalForm
  , RowError(..)
  , emptyNormalForm
  , nf
  , fromNormalForm
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Name (TyVar)
import Stella.Compiler.TypedCore.Type (RowEntry(..), RowKey(..), RowPayload(..), Type(..), rowEntryKey, rowEntryPayload)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl, foldr)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))

-- | `⟨ F ; T ⟩`.
-- |
-- | `known` is `F` and `tail` is `T`. A row is closed exactly when `tail` is
-- | empty.
type RowNormalForm =
  { known :: Map RowKey RowPayload
  , tail :: Set TyVar
  }

-- | Normalization fails only on input the kinding rules already reject.
data RowError
  -- | The same key twice, which sharpness forbids (D4).
  = DuplicateKey RowKey
  -- | A type that is not a row at all.
  | NotARow Type

emptyNormalForm :: RowNormalForm
emptyNormalForm = { known: Map.empty, tail: Set.empty }

-- | `nf`.
-- |
-- | **The caller establishes `Γ ⊢ ρ : Row ε` first.** `NotARow` and
-- | `DuplicateKey` are defensive checks, not a replacement for kinding: a type
-- | variable alone does not carry its kind, so `nf` cannot decide on its own
-- | that what it is given is a row. Kind-check the tail of a row extension and
-- | both sides of a union before normalizing or deciding entailment.
-- |
-- | A duplicate is reported rather than silently resolved, because
-- | normalization is part of the trusted core and must not turn an ill-kinded
-- | row into a well-formed one.
-- |
-- | A repeated row *variable*, as in `r ⊎ r`, is absorbed by the union of sets
-- | and is not an error here. What decides it is the union's side condition
-- | `r # r`, which an ordinary context does not derive.
nf :: Type -> Either RowError RowNormalForm
nf = case _ of
  TRowEmpty ->
    Right emptyNormalForm

  TVar a ->
    Right { known: Map.empty, tail: Set.singleton a }

  TRowExtend entry rest -> do
    { known, tail } <- nf rest
    let key = rowEntryKey entry
    case Map.lookup key known of
      Just _ -> Left (DuplicateKey key)
      Nothing ->
        Right { known: Map.insert key (rowEntryPayload entry) known, tail }

  TRowUnion left right -> do
    l <- nf left
    r <- nf right
    union l r

  ty ->
    Left (NotARow ty)

-- | A row whose normal form is the one given.
-- |
-- | `nf` of the result is the input again, so the two stand for one row under
-- | `≡`. What is rebuilt is a row in normal order rather than the row that was
-- | normalized; the two differ in how they are written and in nothing else.
-- |
-- | `Nothing` is a pairing no element has: the payload of a declared effect
-- | under a key that is neither its own nor a `Symbol`.
fromNormalForm :: RowNormalForm -> Maybe Type
fromNormalForm n = do
  entries <- traverse entryOf (Map.toUnfoldable n.known :: P.Array (Tuple RowKey RowPayload))
  Just (foldr TRowExtend tailType entries)
  where
  tailType = case Array.uncons (Set.toUnfoldable n.tail :: P.Array TyVar) of
    Nothing -> TRowEmpty
    Just { head, tail } -> foldl (\acc t -> TRowUnion acc (TVar t)) (TVar head) tail

entryOf :: Tuple RowKey RowPayload -> Maybe RowEntry
entryOf (Tuple key payload) = case payload of
  TypePayload ty -> Just (RowTypeEntry key ty)
  EffectPayload name args -> case key of
    EffectKey e | e == name -> Just (RowEffectEntry name args)
    SymbolKey s -> Just (RowLabelledEffectEntry s name args)
    _ -> Nothing
  RegionPayload name -> case key of
    RegionKey name' | name' == name -> Just (RowRegionEntry name)
    _ -> Nothing

union :: RowNormalForm -> RowNormalForm -> Either RowError RowNormalForm
union l r =
  case Set.findMin (Set.intersection (keysOf l) (keysOf r)) of
    Just shared -> Left (DuplicateKey shared)
    Nothing ->
      Right
        { known: Map.union l.known r.known
        , tail: Set.union l.tail r.tail
        }
  where
  keysOf n = Set.fromFoldable (Map.keys n.known)

derive instance Eq RowError
derive instance Generic RowError _

instance Show RowError where
  show x = genericShow x
