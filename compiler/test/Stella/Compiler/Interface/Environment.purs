-- | The build environment, assembled from interfaces written by hand, and the
-- | schemes an interface carries.
module Test.Stella.Compiler.Interface.Environment (spec) where

import Prelude
import Prim hiding (Type, Symbol)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Set as Set
import Effect.Aff (Aff)
import Stella.Compiler.Interface (importedArities, importsOf)
import Stella.Compiler.Interface.Environment (BuildEnvironment, EnvironmentError(..), ModuleView, addInterface, exportsOf, initialEnvironment, lookupAttribute, lookupType, lookupValue, reachable, viewFor)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeSort(..), ValueEntry, ValueSort(..), Via(..), emptyDeclarations, emptyExports, foreignSummary, isComputation)
import Stella.Compiler.Interface.Prim (primAttribute)
import Stella.Compiler.Interface.Scheme (SchemeBody(..), coreScheme, plainBody, plainScheme)
import Stella.Compiler.Surface.Decl (Observation(..))
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..), monoScheme)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), Symbol(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (fn, intTy, ioTy, primModule, pureFn, unitCtor, unitTy)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..))
import Stella.Compiler.TypedCore.Type (Constraint(..), RowKey(..), Type(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

moduleA :: ModuleName
moduleA = ModuleName "A"

moduleB :: ModuleName
moduleB = ModuleName "B"

moduleC :: ModuleName
moduleC = ModuleName "C"

tInt :: Type
tInt = TCon intTy []

value :: ValueEntry
value = { sort: SortValue, scheme: plainScheme (monoScheme tInt), attributes: [] }

-- | An interface declaring nothing and exporting nothing.
bare :: ModuleName -> Array ModuleName -> ModuleInterface
bare name imports =
  { name
  , imports
  , exports: emptyExports
  , declarations: emptyDeclarations
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }

-- | `A` declares and exports `x`, an `Int`.
interfaceA :: ModuleInterface
interfaceA = (bare moduleA [])
  { exports = emptyExports { values = Map.singleton "x" { entity: Qualified moduleA (Ident "x"), via: Declared } }
  , declarations = emptyDeclarations { values = Map.singleton (Ident "x") value }
  }

-- | `B` imports `A` and re-exports its `x`.
interfaceB :: ModuleInterface
interfaceB = (bare moduleB [ moduleA ])
  { exports = emptyExports { values = Map.singleton "x" { entity: Qualified moduleA (Ident "x"), via: ThroughImport moduleA } }
  }

added :: Array ModuleInterface -> (BuildEnvironment -> Aff Unit) -> Aff Unit
added interfaces k = case Array.foldM (\env i -> addInterface i env) initialEnvironment interfaces of
  Left e -> fail ("not added: " <> show e)
  Right env -> k env

viewed :: Array ModuleName -> BuildEnvironment -> (ModuleView -> Aff Unit) -> Aff Unit
viewed imports env k = case viewFor imports env of
  Left e -> fail ("no view: " <> show e)
  Right view -> k view

spec :: Spec Unit
spec = describe "Stella.Compiler.Interface.Environment" do
  describe "the environment a build starts from" do
    it "holds Prim, whose names every module sees without importing it" do
      viewed [] initialEnvironment \view -> do
        map (map _.entity <<< Map.lookup "Unit" <<< _.values) (exportsOf primModule view) `shouldEqual` Just (Just unitCtor)
        map _.sort (lookupValue unitCtor view) `shouldEqual` Just (SortConstructor unitTy)
        map _.sort (lookupType intTy view) `shouldEqual` Just (Intrinsic CanonicalLiteral)
        isJust (lookupAttribute (primAttribute "entrypoint") view) `shouldEqual` true

    it "publishes Unit as a data type whose one constructor is Unit" do
      viewed [] initialEnvironment \view ->
        case lookupType unitTy view of
          Just { sort: DataType d } -> map _.name d.constructors `shouldEqual` [ Ident "Unit" ]
          other -> fail ("not a data type: " <> show (map _.sort other))

  describe "adding an interface" do
    it "refuses a second interface of one module, Prim among them" do
      map (const unit) (addInterface interfaceA initialEnvironment >>= addInterface interfaceA)
        `shouldEqual` Left (ModuleTwice moduleA)
      map (const unit) (addInterface (bare primModule []) initialEnvironment) `shouldEqual` Left (ModuleTwice primModule)

    it "refuses an interface before a module it imports" do
      map (const unit) (addInterface interfaceB initialEnvironment) `shouldEqual` Left (ImportNotAdded moduleB moduleA)

  describe "what a module sees" do
    it "reaches every module its header reaches, and Prim, and nothing else" do
      added [ interfaceA, interfaceB, bare moduleC [] ] \env ->
        viewed [ moduleB ] env \view ->
          reachable view `shouldEqual` Set.fromFoldable [ primModule, moduleA, moduleB ]

    it "refuses a header naming a module the environment does not hold" do
      map (const unit) (viewFor [ moduleC ] initialEnvironment) `shouldEqual` Left (NotInEnvironment moduleC)

    it "takes a name from a module it imports, and none from one reached through it" do
      added [ interfaceA, interfaceB ] \env ->
        viewed [ moduleB ] env \view -> do
          isJust (exportsOf moduleB view) `shouldEqual` true
          isNothing (exportsOf moduleA view) `shouldEqual` true

    it "reads a re-exported name as the entity its declaring module declares, and the way it came" do
      added [ interfaceA, interfaceB ] \env ->
        viewed [ moduleB ] env \view -> do
          let export = exportsOf moduleB view >>= Map.lookup "x" <<< _.values
          map _.entity export `shouldEqual` Just (Qualified moduleA (Ident "x"))
          map _.via export `shouldEqual` Just (ThroughImport moduleA)
          map _.sort (export >>= \e -> lookupValue e.entity view) `shouldEqual` Just SortValue

    it "reads no entity of a module the header does not reach" do
      added [ interfaceA, bare moduleC [] ] \env ->
        viewed [ moduleC ] env \view ->
          isNothing (lookupValue (Qualified moduleA (Ident "x")) view) `shouldEqual` true

  describe "the arities a translation reads" do
    let
      f = Qualified moduleA (Ident "f")
      withF = interfaceA
        { exports = interfaceA.exports { values = Map.insert "f" { entity: f, via: Declared } interfaceA.exports.values }
        , declarations = interfaceA.declarations { values = Map.insert (Ident "f") value interfaceA.declarations.values }
        , arities = Map.singleton (Ident "f") 2
        }

    it "come from the interface, checked as an interface of their own" do
      case importsOf [ withF ] of
        Left e -> fail (show e)
        Right imports -> importedArities moduleB [ moduleA ] imports `shouldEqual` Map.singleton f 2

  describe "a scheme" do
    let
      a = TyVar "a"
      row = TVar (TyVar "e")
      lacks = Lacks (SymbolKey (Symbol "n")) row
      dictionary = TApp (TCon (Qualified moduleA (TyName "Show")) []) (TVar a)
      synthesized = { name: Just (Ident "d"), dictionary, synthesizer: Qualified moduleA (Ident "resolve") }

    it "takes the quantifiers and constraints of a Core type onto its spine" do
      plainBody (TForall a KType (TConstrained lacks (TVar a)))
        `shouldEqual` Forall a KType (Constrained lacks (Plain (TVar a)))

    it "stands for a thunk where it is a computation's" do
      let s = { kindVars: [], body: Forall (TyVar "e") (KRow RowEffect) (Computation tInt row) }
      isComputation s `shouldEqual` true
      (coreScheme s).body `shouldEqual` TForall (TyVar "e") (KRow RowEffect) (fn (TCon unitTy []) row tInt)

    it "stands for a parameter of the dictionary's type where it takes a synthesized argument" do
      let s = { kindVars: [], body: Forall a KType (Synthesized synthesized (Plain (pureFn (TVar a) tInt))) }
      isComputation s `shouldEqual` false
      (coreScheme s).body `shouldEqual` TForall a KType (pureFn dictionary (pureFn (TVar a) tInt))

    it "is read as the scheme it was made from, where it says nothing beyond Core" do
      let t = { kindVars: [], body: TForall a KType (pureFn (TVar a) (TVar a)) }
      coreScheme (plainScheme t) `shouldEqual` t

  describe "a foreign's summary" do
    it "says whether the result its type ends in is an IO" do
      let
        foreign_ t = { sort: SortForeign ObservesNone, scheme: plainScheme (monoScheme t), attributes: [] }
        io = TApp (TCon ioTy []) tInt
      map _.returnsIO (foreignSummary (foreign_ (pureFn tInt io))) `shouldEqual` Just true
      map _.returnsIO (foreignSummary (foreign_ (pureFn tInt tInt))) `shouldEqual` Just false
      map _.observation (foreignSummary (foreign_ io)) `shouldEqual` Just ObservesNone
      map _.returnsIO (foreignSummary value) `shouldEqual` Nothing
