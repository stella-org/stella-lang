-- | Sharp row normal forms.
-- |
-- | A sharp row has one payload at each key, so its normal form is a finite map
-- | from keys to payloads together with a set of row variables standing for the
-- | unknown tail. This is the projection a rule reads a payload through, as in
-- | `F(k) = τ`. It is partial, defined only where kinding has established
-- | sharpness; type equality compares canonical forms, which are total
-- | (`Stella.Compiler.TypedCore.Canonical`).
-- |
-- | Keys are rigid — a structural key is a literal (D13) and a derived effect
-- | key is the head constructor (D16) — so no key changes while a row is
-- | normalized.
module Stella.Compiler.TypedCore.Row
  ( RowNormalForm
  , RowError(..)
  , emptyNormalForm
  , nfSharp
  , fromNormalForm
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Canonical (canonicalPayload)
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

-- | Where the projection is undefined.
data RowError
  -- | Two payloads at one key that are not equal, so no payload is the one at
  -- | that key.
  = DuplicateKey RowKey
  -- | A type that is not a row at all.
  | NotARow Type

emptyNormalForm :: RowNormalForm
emptyNormalForm = { known: Map.empty, tail: Set.empty }

-- | `nf`, on a sharp row.
-- |
-- | **The caller establishes `Γ ⊢ ρ : Row ε` first.** `NotARow` and
-- | `DuplicateKey` are defensive checks, not a replacement for kinding: a type
-- | variable alone does not carry its kind, so `nfSharp` cannot decide on its
-- | own that what it is given is a row.
-- |
-- | A row kinded in a context whose assumptions are inconsistent need not be
-- | sharp, sharpness being an entailment that holds there of anything. Equal
-- | payloads at one key are one payload, as they are canonically, so
-- | `( x : Int ) ⊎ ( x : Int )` projects to `( x : Int )`; distinct ones have no
-- | projection and are reported.
-- |
-- | A repeated row *variable*, as in `r ⊎ r`, is absorbed by the union of sets.
nfSharp :: Type -> Either RowError RowNormalForm
nfSharp = case _ of
  TRowEmpty ->
    Right emptyNormalForm

  TVar a ->
    Right { known: Map.empty, tail: Set.singleton a }

  TRowExtend entry rest -> do
    n <- nfSharp rest
    union { known: Map.singleton (rowEntryKey entry) (rowEntryPayload entry), tail: Set.empty } n

  TRowUnion left right -> do
    l <- nfSharp left
    r <- nfSharp right
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
  case Array.find clashes (Map.toUnfoldable (Map.intersectionWith Tuple l.known r.known)) of
    Just (Tuple key _) -> Left (DuplicateKey key)
    Nothing ->
      Right
        { known: Map.union l.known r.known
        , tail: Set.union l.tail r.tail
        }
  where
  clashes (Tuple _ (Tuple a b)) = canonicalPayload a /= canonicalPayload b

derive instance Eq RowError
derive instance Generic RowError _

instance Show RowError where
  show x = genericShow x
