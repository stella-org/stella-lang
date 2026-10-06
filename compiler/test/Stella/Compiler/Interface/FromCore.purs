-- | The canonical interface of a module written in Core: what a module importing
-- | it is resolved and elaborated against, read off the module and its checked
-- | signature.
module Test.Stella.Compiler.Interface.FromCore (spec) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Stella.Compiler.Elaborate.Environment.Imported (importedSignature)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Interface.FromCore (FromCoreError(..), interfaceOfCore)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeSort(..), ValueSort(..))
import Stella.Compiler.Interface.Prim (primAttribute)
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Surface.Decl (Observation(..))
import Stella.Compiler.TypedCore (CanonicalClass(..), Decl(..), Export(..), Expr(..), Literal(..), Module, declareAnnotated, primSignature)
import Stella.Compiler.TypedCore.Kind (monoScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), OpName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (intTy, pureFn, unitTy)
import Stella.Compiler.TypedCore.Type (Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

lib :: ModuleName
lib = ModuleName "Lib"

int :: Type
int = TCon intTy []

-- | `Lib`: `data Box = Box Int`, an effect `E` with `get : Unit ->* Int`, a
-- | foreign `ext`, a value `one`, a value `hidden` it does not export, and a
-- | macro `mac`.
libCore :: Module Unit
libCore =
  { annotation: unit
  , name: lib
  , imports: []
  , exports: [ ExportType (TyName "Box"), ExportCtor (Ident "Box"), ExportEffect (EffName "E"), ExportValue (Ident "ext"), ExportValue (Ident "one"), ExportValue (Ident "mac") ]
  , decls:
      [ DeclData unit { name: TyName "Box", kindVars: [], params: [], constructors: [ { name: Ident "Box", tag: 0, fields: [ int ] } ], isNewtype: false, attributes: [] }
      , DeclEffect unit { name: EffName "E", params: [], operations: [ { name: OpName "get", tyBinders: [], argument: TCon unitTy [], resumesWith: int } ], attributes: [] }
      , DeclForeign unit { name: Ident "ext", scheme: monoScheme (pureFn int int), attributes: [] }
      , DeclNonRec unit { name: Ident "one", scheme: monoScheme int, value: Lit unit (LitInt 1), attributes: [] }
      , DeclNonRec unit { name: Ident "hidden", scheme: monoScheme int, value: Lit unit (LitInt 2), attributes: [] }
      , DeclNonRec unit { name: Ident "mac", scheme: monoScheme int, value: Lit unit (LitInt 3), attributes: [ { name: primAttribute "macro", positional: [], keyword: [] } ] }
      ]
  }

-- | `Lib`'s interface, with the arities given.
interfaceWith :: Map.Map Ident Int -> Either FromCoreError ModuleInterface
interfaceWith arities = case declareAnnotated primSignature libCore of
  Left _ -> Left (DataTypeUndeclared (TyName "declare"))
  Right declared -> interfaceOfCore libCore declared arities

withInterface :: (ModuleInterface -> Aff Unit) -> Aff Unit
withInterface k = case interfaceWith (Map.singleton (Ident "ext") 1) of
  Left err -> fail (show err)
  Right i -> k i

spec :: Spec Unit
spec = describe "Stella.Compiler.Interface.FromCore" do
  describe "a module written in Core" do
    it "declares every value it holds, each of the sort Core says it is" do
      withInterface \i -> do
        let sortOf n = map _.sort (Map.lookup (Ident n) i.declarations.values)
        map show (sortOf "one") `shouldEqual` Just (show SortValue)
        map show (sortOf "hidden") `shouldEqual` Just (show SortValue)
        map show (sortOf "ext") `shouldEqual` Just (show (SortForeign MayObserve))
        map show (sortOf "Box") `shouldEqual` Just (show (SortConstructor (Qualified lib (TyName "Box"))))
        map show (sortOf "get") `shouldEqual` Just (show (SortOperation (Qualified lib (EffName "E"))))
        map show (sortOf "mac") `shouldEqual` Just (show SortValue)

    it "exports a value carrying Prim.macro as a macro, and as no value" do
      withInterface \i -> do
        Map.member "mac" i.exports.macros `shouldEqual` true
        Map.member "mac" i.exports.values `shouldEqual` false
        Array.sort (Array.fromFoldable (Map.keys i.exports.values)) `shouldEqual` [ "Box", "ext", "get", "one" ]

    it "publishes a type with its constructors, and an effect with its operations, one argument each" do
      withInterface \i -> do
        map _.members (Map.lookup "Box" i.exports.types) `shouldEqual` Just [ Ident "Box" ]
        map _.members (Map.lookup "E" i.exports.types) `shouldEqual` Just [ Ident "get" ]
        map (map _.arguments <<< _.operations) (Map.lookup (EffName "E") i.declarations.effects) `shouldEqual` Just [ [ TCon unitTy [] ] ]

    it "has no arity of a value no module downstream reaches, nor one below one" do
      interfaceWith (Map.singleton (Ident "hidden") 1) `shouldEqual` Left (ArityNotOwn (Ident "hidden"))
      interfaceWith (Map.singleton (Ident "ext") 0) `shouldEqual` Left (ArityBelowOne (Ident "ext") 0)

  describe "Stella.Syntax and the module it depends on" do
    it "are interfaces an environment admits, and a module importing them is checked against" do
      case compiled of
        Left err -> fail err
        Right syntax -> do
          case Array.find (\i -> i.name == syntaxModuleName) syntax.moduleInterfaces of
            Just i -> map (show <<< _.sort) (Map.lookup (TyName "OriginRef") i.declarations.types) `shouldEqual` Just (show (Intrinsic CanonicalOpaque))
            Nothing -> fail "no Stella.Syntax"
          case foldM (flip addInterface) initialEnvironment syntax.moduleInterfaces of
            Left err -> fail (show err)
            Right env -> case viewFor [ syntaxModuleName ] env of
              Left err -> fail (show err)
              Right view -> case importedSignature env view of
                Left err -> fail (show err)
                Right _ -> pure unit
