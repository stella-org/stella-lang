-- | The signature and the catalog a module is elaborated against, read off the
-- | interfaces of what it imports.
module Test.Stella.Compiler.Elaborate.Imported (spec) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.Elaborate.Environment.Imported (importedCatalog, importedSignature)
import Stella.Compiler.Interface.Environment (BuildEnvironment, ModuleView, addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeEntity(..), TypeSort(..), ValueSort(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Interface.Scheme (plainScheme)
import Stella.Compiler.Surface.Decl (Observation(..))
import Stella.Compiler.TypedCore (Decl(..), Export(..), Module, declare, primSignature)
import Stella.Compiler.TypedCore.Kind (Kind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), OpName(..), Qualified(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (intTy, pureFn, recordTy, unitTy)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), Signature, TyConInfo(..))
import Stella.Compiler.TypedCore.Type (RowEntry(..), RowKey(..), Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

lib :: ModuleName
lib = ModuleName "Lib"

re :: ModuleName
re = ModuleName "Re"

int :: Type
int = TCon intTy []

unitType :: Type
unitType = TCon unitTy []

a :: TyVar
a = TyVar "a"

box :: Type -> Type
box = TApp (TCon (Qualified lib (TyName "Box")) [])

hidden :: Type
hidden = TCon (Qualified lib (TyName "Hidden")) []

-- | `Lib`: `Box a = Box a` and the private `Hidden = Hidden`; `wrap`, exported;
-- | `peek`, exported, whose scheme mentions `Hidden`; `secret`, private;
-- | `found`, published to the catalog alone; and the foreign `ext`.
libInterface :: ModuleInterface
libInterface =
  { name: lib
  , imports: []
  , exports: emptyExports
      { values = Map.fromFoldable (map (\n -> Tuple n (declared n)) [ "wrap", "peek", "ext", "Box" ])
      , types = Map.singleton "Box" { entity: TypeEntity (Qualified lib (TyName "Box")), via: Declared, members: [ Ident "Box" ] }
      }
  , declarations: emptyDeclarations
      { values = Map.fromFoldable
          [ value "wrap" SortValue (TForall a KType (pureFn (TVar a) (box (TVar a))))
          , value "peek" SortValue (pureFn (box hidden) int)
          , value "secret" SortValue int
          , value "found" SortValue int
          , value "ext" (SortForeign MayObserve) (pureFn int int)
          , value "Box" (SortConstructor (Qualified lib (TyName "Box"))) (TForall a KType (pureFn (TVar a) (box (TVar a))))
          , value "Hidden" (SortConstructor (Qualified lib (TyName "Hidden"))) hidden
          ]
      , types = Map.fromFoldable
          [ Tuple (TyName "Box")
              { kind: monoScheme (KFun KType KType)
              , sort: DataType { params: [ { name: a, kind: KType } ], constructors: [ { name: Ident "Box", fields: [ TVar a ] } ], isNewtype: false }
              , attributes: []
              }
          , Tuple (TyName "Hidden")
              { kind: monoScheme KType
              , sort: DataType { params: [], constructors: [ { name: Ident "Hidden", fields: [] } ], isNewtype: false }
              , attributes: []
              }
          ]
      }
  , implicitHandlers: []
  , catalogOnly: Set.singleton (Ident "found")
  , arities: Map.empty
  }
  where
  declared n = { entity: Qualified lib (Ident n), via: Declared }
  value n sort ty = Tuple (Ident n) { sort, scheme: plainScheme (monoScheme ty), attributes: [] }

-- | `Re`, which imports `Lib` and re-exports `wrap`.
reInterface :: ModuleInterface
reInterface =
  { name: re
  , imports: [ lib ]
  , exports: emptyExports { values = Map.singleton "wrap" { entity: Qualified lib (Ident "wrap"), via: ThroughImport lib } }
  , declarations: emptyDeclarations
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }

-- | The same two data types as a Core module, which Core declares.
libCore :: Module Unit
libCore =
  { annotation: unit
  , name: lib
  , imports: []
  , exports: [ ExportType (TyName "Box"), ExportType (TyName "Hidden") ]
  , decls:
      [ DeclData unit { name: TyName "Box", kindVars: [], params: [ { name: a, kind: KType } ], constructors: [ { name: Ident "Box", tag: 0, fields: [ TVar a ] } ], isNewtype: false, attributes: [] }
      , DeclData unit { name: TyName "Hidden", kindVars: [], params: [], constructors: [ { name: Ident "Hidden", tag: 0, fields: [] } ], isNewtype: false, attributes: [] }
      ]
  }

environment :: Array ModuleInterface -> Either String BuildEnvironment
environment = Array.foldM
  ( \env i -> case addInterface i env of
      Right e -> Right e
      Left err -> Left (show err)
  )
  initialEnvironment

viewing :: Array ModuleInterface -> Array ModuleName -> (BuildEnvironment -> ModuleView -> Aff Unit) -> Aff Unit
viewing interfaces imports k = case environment interfaces of
  Left err -> fail err
  Right env -> case viewFor imports env of
    Left err -> fail (show err)
    Right view -> k env view

signatureIn :: BuildEnvironment -> ModuleView -> (Signature -> Aff Unit) -> Aff Unit
signatureIn env view k = case importedSignature env view of
  Left err -> fail (show err)
  Right sig -> k sig

spec :: Spec Unit
spec = describe "Stella.Compiler.Elaborate.Environment.Imported" do
  describe "the signature" do
    it "holds every declaration the imports reach, a private one among them" do
      viewing [ libInterface ] [ lib ] \env view -> signatureIn env view \sig -> do
        Map.member (Qualified lib (TyName "Hidden")) sig.types `shouldEqual` true
        Map.member (Qualified lib (Ident "secret")) sig.values `shouldEqual` true
        map _.isForeign (Map.lookup (Qualified lib (Ident "ext")) sig.values) `shouldEqual` Just true
        -- a constructor is the type's, and no value
        Map.member (Qualified lib (Ident "Box")) sig.values `shouldEqual` false

    it "reads a data type as Core declares it" do
      viewing [ libInterface ] [ lib ] \env view -> signatureIn env view \sig ->
        case declare primSignature libCore of
          Left err -> fail (show err.error)
          Right declared -> do
            Map.lookup (Qualified lib (TyName "Box")) sig.types `shouldEqual` Map.lookup (Qualified lib (TyName "Box")) declared.types
            Map.lookup (Qualified lib (Ident "Box")) sig.ctors `shouldEqual` Map.lookup (Qualified lib (Ident "Box")) declared.ctors

    it "gives an operation the one argument Core takes, whatever number it is written with" do
      let
        operation name arguments = { name: Ident name, binders: [], arguments, resumesWith: int }
        effects = libInterface
          { declarations = libInterface.declarations
              { effects = Map.singleton (EffName "Ops")
                  { params: [], operations: [ operation "none" [], operation "one" [ int ], operation "both" [ int, unitType ] ], attributes: [] }
              }
          }
        argumentOf sig op = map _.argument (Map.lookup (Qualified lib (EffName "Ops")) sig.effects >>= \e -> Map.lookup (OpName op) e.operations)
      viewing [ effects ] [ lib ] \env view -> signatureIn env view \sig -> do
        argumentOf sig "none" `shouldEqual` Just unitType
        argumentOf sig "one" `shouldEqual` Just int
        argumentOf sig "both" `shouldEqual` Just
          (TApp (TCon recordTy []) (TRowExtend (RowTypeEntry (PositionKey 0) int) (TRowExtend (RowTypeEntry (PositionKey 1) unitType) TRowEmpty)))

    it "holds a foreign type as an opaque type of its module, which a scheme may mention" do
      let
        window = TCon (Qualified lib (TyName "Window")) []
        withWindow = libInterface
          { declarations = libInterface.declarations
              { types = Map.insert (TyName "Window") { kind: monoScheme KType, sort: ForeignType, attributes: [] } libInterface.declarations.types
              , values = Map.insert (Ident "window") { sort: SortForeign MayObserve, scheme: plainScheme (monoScheme window), attributes: [] } libInterface.declarations.values
              }
          }
      viewing [ withWindow ] [ lib ] \env view -> signatureIn env view \sig ->
        Map.lookup (Qualified lib (TyName "Window")) sig.types `shouldEqual` Just (IntrinsicTyCon (monoScheme KType) CanonicalOpaque)

  describe "the catalog" do
    it "holds what source could reach, and what is published to the catalog alone" do
      viewing [ libInterface ] [ lib ] \env view ->
        names (importedCatalog env view) `shouldEqual`
          [ "Lib.Box:ConstructorEntry", "Lib.ext:ForeignEntry", "Lib.found:ValueEntry", "Lib.peek:ValueEntry", "Lib.wrap:ValueEntry", "Prim.Unit:ConstructorEntry" ]

    it "reads a value re-exported from the module declaring it" do
      viewing [ libInterface, reInterface ] [ re ] \env view ->
        names (importedCatalog env view) `shouldEqual`
          [ "Lib.Box:ConstructorEntry", "Lib.ext:ForeignEntry", "Lib.found:ValueEntry", "Lib.peek:ValueEntry", "Lib.wrap:ValueEntry", "Prim.Unit:ConstructorEntry" ]

    it "holds what a module reached only through another publishes" do
      let
        c = { name: ModuleName "C", imports: [ re ], exports: emptyExports, declarations: emptyDeclarations, implicitHandlers: [], catalogOnly: Set.empty, arities: Map.empty }
      viewing [ libInterface, reInterface, c ] [ ModuleName "C" ] \env view ->
        Array.filter (String.contains (String.Pattern "Lib.")) (names (importedCatalog env view)) `shouldEqual`
          [ "Lib.Box:ConstructorEntry", "Lib.ext:ForeignEntry", "Lib.found:ValueEntry", "Lib.peek:ValueEntry", "Lib.wrap:ValueEntry" ]
  where
  names entries = Array.sort (map (\e -> qualified e.name <> ":" <> show e.sort) entries)
  qualified (Qualified (ModuleName m) (Ident x)) = m <> "." <> x
