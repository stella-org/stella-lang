-- | A module written in source, compiled and loaded, and its values read as
-- | the machine holds them once the module is initialized.
module Test.Steam.Compiled (running, runningAfter) where

import Prelude

import Prim as P

import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
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
import Stella.Compiler.Build (CompilerAction, compileModule, defaultHooks, printCompileError)
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment)
import Stella.Compiler.Macro.Run (ParseOutcome(..), defaultSettings)
import Stella.Compiler.Macro.Tree (Position(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Name (Symbol(..), Tag(..))
import Test.Spec.Assertions (fail)

-- | The module `Main` the lines given write, compiled, loaded, and each of its
-- | globals named rendered.
running :: P.Array P.String -> P.Array P.String -> (Map.Map P.String P.String -> Aff Unit) -> Aff Unit
running = runningAfter []

-- | `running`, the modules whose sources are given compiled before `Main`, in
-- | order, each against the interfaces of those before it, and every one loaded
-- | into the one store in that order.
runningAfter :: P.Array P.String -> P.Array P.String -> P.Array P.String -> (Map.Map P.String P.String -> Aff Unit) -> Aff Unit
runningAfter before source globals k = do
  compiled <- runExceptT (Array.foldM compiling { env: initialEnvironment, dmos: [] } (Array.snoc before (joinWith "\n" source)))
  case compiled of
    Left failure -> fail failure
    Right { dmos } -> k =<< liftEffect do
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
  -- each module compiled against the interfaces of those before it, and its
  -- own added
  compiling acc text = do
    made <- ExceptT (lmap (joinWith "; " <<< map printCompileError <<< Array.fromFoldable) <$> compileModule action defaultSettings acc.env Map.empty text)
    env <- except (lmap show (addInterface made.interface acc.env))
    pure { env, dmos: Array.snoc acc.dmos made.dmo }

  -- no macro is called, so no parser is run
  action :: CompilerAction Aff
  action =
    { readSource: \_ -> pure (Left "no file")
    , runParser: \_ _ _ -> pure (FailedAs { position: Position 0 0, expected: Set.empty, labels: [] })
    , hooks: defaultHooks
    }
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
