-- | An interface assembled from its surface part and its Core part, what makes
-- | the two no interface, and two modules compiled one against the other
-- | through the bytes of the first one's interface.
module Test.Stella.Compiler.Interface.Assemble (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.CST (parseModule, printSyntaxError)
import Stella.Compiler.Interface.Assemble (AssembleError(..), CoreInterface, CoreTypeSort(..), SurfaceInterface, Table(..), assemble, surfaceInterface)
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment)
import Stella.Compiler.Interface.File as File
import Stella.Compiler.Interface.Module (ModuleInterface, TypeSort(..), Via(..))
import Stella.Compiler.Interface.Scheme (SchemeBody(..))
import Stella.Compiler.Resolve.Module (resolveModule)
import Stella.Compiler.Surface.Decl (Constant(..), Declaration(..)) as Surface
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (intTy, pureFn, stringTy, unitTy)
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stella.Compiler.TypedCore.Type (RowEntry(..), Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

moduleA :: ModuleName
moduleA = ModuleName "A"

inA :: forall a. a -> Qualified a
inA = Qualified moduleA

int :: Type
int = TCon intTy []

-- | `A`, which `B` is compiled against.
sourceA :: P.Array P.String
sourceA =
  [ "module A where"
  , "data Shape = Circle Int | Square Int"
  , "effect E where"
  , "  get :: Unit ->* Int"
  , "infixl 6 area as +++"
  , "area :: Shape -> Int -> Int"
  , "area s n = n"
  , "attribute json (name :: String) (level :: Int = 3)"
  , "type Program = {| E |}"
  , "@[macro]"
  , "m x = x"
  ]

-- | What elaboration would decide of `A`, written out.
coreA :: CoreInterface
coreA =
  { schemes: Map.fromFoldable
      [ Tuple (Ident "Circle") (plain (fn int shape))
      , Tuple (Ident "Square") (plain (fn int shape))
      , Tuple (Ident "get") (plain (fn (TCon unitTy []) int))
      , Tuple (Ident "area") (plain (fn shape (fn int int)))
      , Tuple (Ident "m") (plain (fn int int))
      ]
  , types: Map.fromFoldable
      [ Tuple (TyName "Shape") { kind: monoScheme KType, sort: CoreData { params: [], fields: [ [ int ], [ int ] ] } }
      , Tuple (TyName "Program") { kind: monoScheme (KRow RowEffect), sort: CoreSynonym { params: [], body: TRowExtend (RowEffectEntry (inA (EffName "E")) []) TRowEmpty } }
      ]
  , effects: Map.singleton (EffName "E") { params: [], operations: [ { binders: [], arguments: [ TCon unitTy [] ], resumesWith: int } ] }
  , attributes: Map.singleton (Ident "json") { positional: [], keyword: [ TCon stringTy [], int ] }
  , implicitHandlers: Map.empty
  }
  where
  shape = TCon (inA (TyName "Shape")) []
  plain t = { kindVars: [], body: Plain t }
  fn = pureFn

aritiesA :: Map.Map Ident P.Int
aritiesA = Map.fromFoldable [ Tuple (Ident "area") 2, Tuple (Ident "m") 1 ]

-- | The surface part of `A`, read off its source.
surfaceA :: (SurfaceInterface -> Aff Unit) -> Aff Unit
surfaceA k = case parseModule (joinWith "\n" sourceA) of
  Left e -> fail (printSyntaxError e)
  Right m -> do
    let r = resolveModule initialEnvironment m
    r.errors `shouldEqual` []
    case surfaceInterface r.module r.exports of
      Nothing -> fail "A holds an invalid constant"
      Just s -> k s

-- | `A`'s interface carried through its bytes, as a build environment holding
-- | it.
throughBytes :: ModuleInterface -> Either P.String BuildEnvironment
throughBytes i = case File.encode { interface: i, buildHash: Nothing } of
  Left e -> Left (show e)
  Right bytes -> case File.decode bytes of
    Left e -> Left (show e)
    Right stored -> case addInterface stored.interface initialEnvironment of
      Left e -> Left (show e)
      Right env -> Right env

spec :: Spec Unit
spec = describe "Stella.Compiler.Interface.Assemble" do
  describe "the parts" do
    it "make an interface where they speak of one module" do
      surfaceA \s -> case assemble s coreA aritiesA of
        Left e -> fail (show e)
        Right i -> do
          Map.keys i.declarations.values `shouldEqual` Map.keys coreA.schemes
          map _.isNewtype (Array.head (Array.mapMaybe dataOf (Array.fromFoldable (Map.values i.declarations.types)))) `shouldEqual` Just false
          map (map _.label <<< _.keyword) (Map.lookup (Ident "json") i.declarations.attributes) `shouldEqual` Just [ "name", "level" ]

    it "are refused where a declaration has no Core entry, or a Core entry no declaration" do
      surfaceA \s -> do
        assemble s coreA { schemes = Map.delete (Ident "area") coreA.schemes } aritiesA `shouldEqual` Left (CoreMissing ValueTable "area")
        assemble s coreA { types = Map.insert (TyName "Extra") { kind: monoScheme KType, sort: CoreForeign } coreA.types } aritiesA
          `shouldEqual` Left (CoreExtra TypeTable "Extra")

    it "are refused where they disagree on what a declaration is or holds" do
      surfaceA \s -> do
        assemble s coreA { types = Map.insert (TyName "Program") { kind: monoScheme KType, sort: CoreForeign } coreA.types } aritiesA
          `shouldEqual` Left (TypeSortMismatch (TyName "Program"))
        assemble s coreA { types = Map.insert (TyName "Shape") { kind: monoScheme KType, sort: CoreData { params: [], fields: [ [ int ] ] } } coreA.types } aritiesA
          `shouldEqual` Left (ConstructorCount (TyName "Shape") 2 1)
        assemble s coreA { effects = Map.singleton (EffName "E") { params: [], operations: [] } } aritiesA
          `shouldEqual` Left (OperationCount (EffName "E") 1 0)
        assemble s coreA { attributes = Map.singleton (Ident "json") { positional: [], keyword: [ int ] } } aritiesA
          `shouldEqual` Left (AttributeParameterCount (Ident "json") 2 1)

    it "take the arity of a macro, which is published in the macro namespace" do
      surfaceA \s -> do
        Map.lookup "m" s.exports.macros `shouldEqual` Just { entity: inA (Ident "m"), via: Declared }
        map (Map.lookup (Ident "m") <<< _.arities) (assemble s coreA aritiesA) `shouldEqual` Right (Just 1)

    it "take the arity of a value reached only through an operator the module exports" do
      case parseModule (joinWith "\n" [ "module P ((+++)) where", "infixl 6 f as +++", "f a b = a" ]) of
        Left e -> fail (printSyntaxError e)
        Right m -> do
          let r = resolveModule initialEnvironment m
          r.errors `shouldEqual` []
          case surfaceInterface r.module r.exports of
            Nothing -> fail "P holds an invalid constant"
            Just s -> do
              let core = coreA { schemes = Map.singleton (Ident "f") { kindVars: [], body: Plain (pureFn int (pureFn int int)) }, types = Map.empty, effects = Map.empty, attributes = Map.empty }
              map (Map.lookup (Ident "f") <<< _.arities) (assemble s core (Map.singleton (Ident "f") 2)) `shouldEqual` Right (Just 2)

    it "are refused with an arity of no value the module declares and exports, or one below one" do
      surfaceA \s -> do
        assemble s coreA (Map.singleton (Ident "nope") 1) `shouldEqual` Left (ArityNotOwn (Ident "nope"))
        assemble s coreA (Map.singleton (Ident "area") 0) `shouldEqual` Left (ArityBelowOne (Ident "area") 0)

  describe "a module compiled against another through its interface's bytes" do
    it "resolves the names the other publishes, its members, fixities, attributes, and rows" do
      surfaceA \s -> case either (Left <<< show) throughBytes (assemble s coreA aritiesA) of
        Left e -> fail e
        Right env -> case parseModule (joinWith "\n" sourceB) of
          Left e -> fail (printSyntaxError e)
          Right m -> do
            let r = resolveModule env m
            r.errors `shouldEqual` []
            map name r.module.declarations `shouldEqual` [ "f", "g", "h", "run of A.E" ]
            Array.concatMap defaults r.module.declarations `shouldEqual` [ "level=3" ]
  where
  dataOf entry = case entry.sort of
    DataType d -> Just d
    _ -> Nothing

sourceB :: P.Array P.String
sourceB =
  [ "module B where"
  , "import A"
  , "f = Circle 1 +++ 2"
  , "@[json name=\"x\"]"
  , "g = 1"
  , "h = handle g with"
  , "  E | get _ -> resume 0"
  , "handler run :: (Unit -> a / Program) -> a where"
  , "  | get _ -> resume 0"
  ]

name :: Surface.Declaration -> P.String
name = case _ of
  Surface.DeclValue d -> local d.name
  Surface.DeclHandler d -> local d.name <> " of " <> case d.effect of
    Qualified (ModuleName m) (EffName e) -> m <> "." <> e
  _ -> "?"
  where
  local (Qualified _ (Ident n)) = n

-- | The keyword arguments a declaration's attributes were given by a default.
defaults :: Surface.Declaration -> P.Array P.String
defaults = case _ of
  Surface.DeclValue d -> Array.concatMap (\a -> Array.mapMaybe level a.keyword) d.attributes
  _ -> []
  where
  level k = case k.label, k.value of
    "level", Surface.ConstantLiteral _ (LitInt n) -> Just ("level=" <> show n)
    _, _ -> Nothing
