-- | Values between the interpreter and a session's generic JSON
-- | ([Value](../../../../cli/src/Stella/CLI/Session/Value.purs)).
-- |
-- | **A value holds identities and the wire holds names.** Going out, each
-- | constructor and key a value carries is named by the identity tables; coming
-- | in, each name is looked up in what is loaded. Neither direction reads a type:
-- | which values a place admits is checked against a descriptor before a value
-- | comes in, and nothing here repeats that.
-- |
-- | A constructor is named only where the name belongs to a committed module
-- | under the same identity and arity. A load that failed may leave an identity
-- | behind, and a value carrying one is none the interpreter could have built.
-- |
-- | Both directions walk the value with a stack of their own: a `List` nests once
-- | per element, so a long one is deep.
module Steam.CLI.Wire
  ( Unencodable(..)
  , toWire
  , fromWire
  , classOf
  ) where

import Prelude

import Prim as P

import Control.Monad.Rec.Class as Rec
import Data.Array as Array
import Data.Either (Either(..))
import Data.List (List(..), (:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Steam.CLI.Token as Token
import Steam.Load (Store, internKeyIn)
import Steam.Structural (RuntimeNames)
import Steam.Value (CtorId, KeyId, Value(..))
import Stella.CLI.Session.Guest (ValueClass(..))
import Stella.CLI.Session.Value (Step(..), ValueProblem, WireValue(..), compareKeys)
import Stella.Compiler.Bytecode.Module (Key)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))

-- | Why a value has no generic encoding.
data Unencodable
  -- | A value of a class the wire has no form for: a closure, a partial
  -- | application, a continuation, an `IO`, or an opaque value that is no token.
  = NotEncodable ValueClass
  -- | An identity with no committed name, which no value the interpreter built
  -- | carries.
  | Unaccounted P.String

data Out
  = Emit Value
  | MakeData (Qualified Ident) P.Int
  | MakeRecord (P.Array Key)
  | MakeVariant Key

-- | The generic value of an interpreter value.
toWire :: Store -> RuntimeNames -> Value -> Either Unencodable WireValue
toWire store names value = Rec.tailRec go { work: Emit value : Nil, built: Nil }
  where
  go { work, built } = case work of
    Nil -> case built of
      result : Nil -> Rec.Done (Right result)
      _ -> Rec.Done (Left (Unaccounted "a walk of one value left other than one value"))
    task : rest -> case task of
      Emit v -> case emit v of
        Left failure -> Rec.Done (Left failure)
        Right (Left leaf) -> Rec.Loop { work: rest, built: leaf : built }
        Right (Right parts) -> Rec.Loop { work: parts <> rest, built }
      MakeData name n ->
        let
          taken = pop n built
        in
          Rec.Loop { work: rest, built: WData name taken.values : taken.left }
      MakeRecord keys ->
        let
          taken = pop (Array.length keys) built
        in
          Rec.Loop
            { work: rest
            , built: WRecord (Array.zipWith (\key v -> { key, value: v }) keys taken.values) : taken.left
            }
      MakeVariant key -> case built of
        payload : left -> Rec.Loop { work: rest, built: WVariant key payload : left }
        Nil -> Rec.Done (Left (Unaccounted "a variant with no payload built"))

  -- a value whole, or the parts to encode and what to build of them
  emit :: Value -> Either Unencodable (Either WireValue (List Out))
  emit = case _ of
    VInt n -> Right (Left (WInt n))
    VNumber n -> Right (Left (WNumber n))
    VChar c -> Right (Left (WChar c))
    VString s -> Right (Left (WString s))
    VBoolean b -> Right (Left (WBoolean b))
    VData id fields -> do
      name <- committedCtor id (Array.length fields)
      pure (Right (List.fromFoldable (map Emit fields) <> (MakeData name (Array.length fields) : Nil)))
    VRecord fields -> do
      named <- traverse (\(Tuple id v) -> { key: _, value: v } <$> keyNamed id) (Map.toUnfoldable fields :: P.Array _)
      let ordered = Array.sortBy (\a b -> compareKeys a.key b.key) named
      pure (Right (List.fromFoldable (map (Emit <<< _.value) ordered) <> (MakeRecord (map _.key ordered) : Nil)))
    VVariant id payload -> do
      key <- keyNamed id
      pure (Right (Emit payload : MakeVariant key : Nil))
    VOpaque o -> case Token.unwrap o of
      Just token -> Right (Left (WToken token))
      Nothing -> Left (NotEncodable ClassOpaque)
    other -> Left (NotEncodable (classOf other))

  committedCtor :: CtorId -> P.Int -> Either Unencodable (Qualified Ident)
  committedCtor id arity = case Map.lookup id names.ctors of
    Nothing -> Left (Unaccounted ("constructor identity " <> show id <> " has no name"))
    Just name -> case Map.lookup name store.ctors of
      Just ref | ref.id == id && ref.arity == arity -> Right name
      _ -> Left (Unaccounted (ctorText name <> " is not committed with this identity and arity"))

  keyNamed :: KeyId -> Either Unencodable Key
  keyNamed id = case Map.lookup id names.keys of
    Just key -> Right key
    Nothing -> Left (Unaccounted ("key identity " <> show id <> " has no name"))

data In
  = Visit (List Step) WireValue
  | BuildData CtorId P.Int
  | BuildRecord (P.Array KeyId)
  | BuildVariant KeyId

-- | The interpreter value of a generic value, each constructor one committed with
-- | that arity. A key is interned where it has no identity yet: nothing loaded
-- | need name a record field an answer carries.
fromWire :: Store -> WireValue -> Effect (Either ValueProblem Value)
fromWire store value = Rec.tailRecM go { work: Visit Nil value : Nil, built: Nil }
  where
  go { work, built } = case work of
    Nil -> pure case built of
      result : Nil -> Rec.Done (Right result)
      _ -> Rec.Done (Left { path: [], problem: "a walk of one value left other than one value" })
    task : rest -> case task of
      Visit path v ->
        let
          leaf built' = pure (Rec.Loop { work: rest, built: built' : built })
        in
          case v of
            WInt n -> leaf (VInt n)
            WNumber n -> leaf (VNumber n)
            WChar c -> leaf (VChar c)
            WString s -> leaf (VString s)
            WBoolean b -> leaf (VBoolean b)
            WToken t -> leaf (VOpaque (Token.wrap t))
            WData name fields -> case Map.lookup name store.ctors of
              Just ref | ref.arity == Array.length fields ->
                pure $ Rec.Loop
                  { work: List.fromFoldable (Array.mapWithIndex (\i f -> Visit (Index i : Member "fields" : path) f) fields)
                      <> (BuildData ref.id ref.arity : rest)
                  , built
                  }
              Just ref -> refuse (Member "fields" : path) (ctorText name <> " has " <> show ref.arity <> " fields")
              Nothing -> refuse (Member "data" : path) (ctorText name <> " is no constructor of a loaded module")
            WRecord fields -> do
              ids <- traverse (internKeyIn store.identities <<< _.key) fields
              pure $ Rec.Loop
                { work: List.fromFoldable (Array.mapWithIndex (\i f -> Visit (Member "value" : Index i : Member "record" : path) f.value) fields)
                    <> (BuildRecord ids : rest)
                , built
                }
            WVariant key payload -> do
              id <- internKeyIn store.identities key
              pure (Rec.Loop { work: Visit (Member "value" : Member "variant" : path) payload : BuildVariant id : rest, built })
      BuildData id n ->
        let
          taken = pop n built
        in
          pure (Rec.Loop { work: rest, built: VData id taken.values : taken.left })
      BuildRecord ids ->
        let
          taken = pop (Array.length ids) built
        in
          pure (Rec.Loop { work: rest, built: VRecord (Map.fromFoldable (Array.zip ids taken.values)) : taken.left })
      BuildVariant id -> case built of
        payload : left -> pure (Rec.Loop { work: rest, built: VVariant id payload : left })
        Nil -> refuse Nil "a variant with no payload built"

  refuse :: forall a. List Step -> P.String -> Effect (Rec.Step a (Either ValueProblem Value))
  refuse path problem = pure (Rec.Done (Left { path: Array.reverse (Array.fromFoldable path), problem }))

-- | The class a value is of, which is what a refusal names in place of the value.
classOf :: Value -> ValueClass
classOf = case _ of
  VInt _ -> ClassInt
  VNumber _ -> ClassNumber
  VChar _ -> ClassChar
  VString _ -> ClassString
  VBoolean _ -> ClassBoolean
  VData _ _ -> ClassData
  VRecord _ -> ClassRecord
  VVariant _ _ -> ClassVariant
  VClos _ -> ClassClosure
  VPap _ -> ClassPartialApplication
  VCont _ -> ClassContinuation
  VIO _ -> ClassIO
  VOpaque _ -> ClassOpaque

-- | The last `n` values built, in the order they were built, and what is below them.
pop :: forall a. P.Int -> List a -> { values :: P.Array a, left :: List a }
pop n built =
  { values: Array.reverse (Array.fromFoldable (List.take n built))
  , left: List.drop n built
  }

ctorText :: Qualified Ident -> P.String
ctorText (Qualified (ModuleName m) (Ident c)) = m <> "." <> c
