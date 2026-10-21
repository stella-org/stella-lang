-- | The sources of the `Base` modules, `stella-packages/base/src`, against the
-- | ABI catalog: each module the catalog names an entry or a type of has a
-- | source, and compiling it gives an interface declaring every entry of the
-- | module as a foreign at the scheme the catalog gives, the parameters the
-- | scheme takes as many as the arity the catalog gives; every type as a
-- | foreign type of the kind the catalog gives; and no other foreign.
module Test.Stella.Compiler.BaseSources (spec) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Identity (Identity(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String (Pattern(..), Replacement(..), joinWith, replaceAll)
import Effect.Class (liftEffect)
import Stella.Compiler.Build (CompilerAction, compileModule, defaultHooks, printCompileError, withoutSynthesizers)
import Stella.Compiler.Interface.Environment (initialEnvironment)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeSort(..), ValueSort(..))
import Stella.Compiler.Interface.Scheme (coreScheme)
import Stella.Compiler.Macro.Run (ExecutionReason(..), ParseOutcome(..), defaultSettings)
import Stella.Compiler.Primitive (abiTypeDescriptors, runtimeEntries, schemeOfRuntimeEntry)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Equality (schemeEquiv)
import Stella.Compiler.TypedCore.Prim (foreignArity)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.Sources (readRepositoryFile)

-- | Every module the catalog names an entry or a type of, in order.
catalogModules :: Array String
catalogModules = Array.nub (Array.sort (map _.name.module runtimeEntries <> map (\t -> moduleOf t.name) abiTypeDescriptors))
  where
  moduleOf (Qualified (ModuleName m) _) = m

-- | The source of the `Base` module given.
sourceOf :: String -> String
sourceOf m = "stella-packages/base/src/" <> replaceAll (Pattern ".") (Replacement "/") m <> ".stel"

-- | The text given compiled against `Prim` alone, as a build compiles a module.
interfaceOf :: String -> Either String ModuleInterface
interfaceOf text = case compileModule action defaultSettings initialEnvironment Map.empty text of
  Identity (Left errors) -> Left (joinWith "; " (map printCompileError (NonEmptyArray.toArray errors)))
  Identity (Right made) -> Right made.interface
  where
  action :: CompilerAction Identity
  action =
    { readSource: \_ -> pure (Left "no file is read")
    , runParser: \_ _ _ -> pure (ExecutionFailedAs { reason: NoSuchModule, detail: "no parser runs" })
    , synthesis: withoutSynthesizers
    , hooks: defaultHooks
    }

spec :: Spec Unit
spec = describe "the `Base` sources, against the ABI catalog" do
  it "names the modules the catalog does" do
    catalogModules `shouldEqual` [ "Base.Array", "Base.Char", "Base.IO", "Base.Int", "Base.Number", "Base.String" ]

  for_ catalogModules \m -> it ("declares the entries and the types of `" <> m <> "` as the catalog gives them") do
    text <- liftEffect (readRepositoryFile (sourceOf m))
    case interfaceOf text of
      Left why -> fail why
      Right i -> do
        let
          entries = Array.filter (\e -> e.name.module == m) runtimeEntries
          types = Array.filter (\t -> case t.name of Qualified (ModuleName n) _ -> n == m) abiTypeDescriptors
          foreigns = Map.filter
            ( \v -> case v.sort of
                SortForeign _ -> true
                _ -> false
            )
            i.declarations.values
          foreignTypes = Map.filter (\t -> t.sort == ForeignType) i.declarations.types
        Set.map (\(Ident x) -> x) (Map.keys foreigns) `shouldEqual` Set.fromFoldable (map _.name.value entries)
        for_ entries \e -> do
          let x = Ident e.name.value
          map (\v -> schemeEquiv (coreScheme v.scheme) (schemeOfRuntimeEntry e.id)) (Map.lookup x foreigns) `shouldEqual` Just true
          map (foreignArity <<< coreScheme <<< _.scheme) (Map.lookup x foreigns) `shouldEqual` Just e.arity
        Set.map (\(TyName x) -> x) (Map.keys foreignTypes) `shouldEqual` Set.fromFoldable (map (\t -> case t.name of Qualified _ (TyName x) -> x) types)
        for_ types \t -> case t.name of
          Qualified _ x -> map _.kind (Map.lookup x foreignTypes) `shouldEqual` Just t.kind
