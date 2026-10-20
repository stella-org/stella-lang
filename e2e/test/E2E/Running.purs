-- | A program built from its source under `fixtures/source`, loaded, and its
-- | values read as the machine holds them once its modules are initialized.
module Test.E2E.Running (running) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Fmt (fmt)
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Foreign (emptyTable)
import Steam.Load (Identities, emptyStore, globalNamed, load, noIdentities)
import Steam.Value (Value(..))
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Name (Symbol(..), Tag(..))
import E2E.Build (Sources, builtFrom)
import Test.Spec.Assertions (fail)

-- | The modules the directories of `fixtures/source` given build, loaded in the
-- | order they are built, and each global of `Main` named rendered.
running :: Sources -> P.Array P.String -> P.Array P.String -> (Map.Map P.String P.String -> Aff Unit) -> Aff Unit
running sources dirs globals k = case builtFrom sources dirs of
  Left failure -> fail failure
  Right dmos -> k =<< liftEffect do
    identities <- Ref.new noIdentities
    stored <- runBaseEffect (Except.runExcept (Array.foldM load (emptyStore emptyTable identities) dmos))
    case stored of
      Left err -> pure (Map.singleton "load" (show err))
      Right store -> do
        known <- Ref.read identities
        held <- Array.foldM
          ( \acc name -> case globalNamed store (Qualified (ModuleName "Main") (Ident name)) of
              Nothing -> pure (Array.snoc acc (Tuple name "absent"))
              Just slot -> Ref.read slot <#> \value -> Array.snoc acc (Tuple name (maybe "uninitialized" (render known) value))
          )
          []
          globals
        pure (Map.fromFoldable held)
  where
  maybe d f = case _ of
    Nothing -> d
    Just x -> f x

-- | A value as `Some(2)`, a constructor named by the store, or as
-- | `{a: 1, b: true}`, a record's fields in the order of their keys' names, or
-- | as `'Ok(1)`, a variant's tag and its payload.
render :: Identities -> Value -> P.String
render known = go
  where
  go = case _ of
    VInt n -> show n
    VBoolean b -> show b
    VData id fields ->
      let
        name = case Map.lookup id known.ctorNames of
          Just (Qualified _ (Ident c)) -> c
          Nothing -> "?"
      in
        if Array.null fields then name else fmt @"{name}({fields})" { name, fields: joinWith ", " (map go fields) }
    VRecord fields ->
      let
        named = Array.sortWith (\(Tuple k _) -> k) (map (\(Tuple id v) -> Tuple (keyName id) (go v)) (Map.toUnfoldable fields))
      in
        fmt @"{open}{fields}{close}" { open: "{", fields: joinWith ", " (map (\(Tuple k v) -> fmt @"{k}: {v}" { k, v }) named), close: "}" }
    VVariant id payload -> fmt @"{tag}({payload})" { tag: keyName id, payload: go payload }
    _ -> "…"
  keyName id = case Map.lookup id known.keyNames of
    Just (KSymbol (Symbol s)) -> s
    Just (KPosition n) -> show n
    Just (KTag (Tag t)) -> "'" <> t
    _ -> "?"
