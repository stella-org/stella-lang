-- | What a module's header and its top-level declarations put in scope, and
-- | what the module exports, against a build environment written by hand.
module Test.Stella.Compiler.Resolve.Scope (spec) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Stella.Compiler.CST (parseModule, printSyntaxError)
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment)
import Stella.Compiler.Interface.Module (Exports, ModuleInterface, TypeEntity(..), Via(..), emptyDeclarations, emptyExports)
import Stella.Compiler.Resolve.Group (groupModule)
import Stella.Compiler.Resolve.Scope (Namespace(..), ScopeError(..), ScopeReason(..), ScopeWarning(..), ScopedModule, resolveScope)
import Stella.Compiler.Surface.Name (OperatorName(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (unitCtor)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

moduleA :: ModuleName
moduleA = ModuleName "A"

moduleB :: ModuleName
moduleB = ModuleName "B"

inA :: forall a. a -> Qualified a
inA = Qualified moduleA

-- | `A` exports a value `x`, a data type `T` with constructors `C` and `D`, an
-- | effect `E` with operation `get`, an operator `+`, a type operator `+`, a
-- | macro `m`, and an attribute `json`.
exportsA :: Exports
exportsA = emptyExports
  { values = Map.fromFoldable
      [ declared "x" (inA (Ident "x"))
      , declared "C" (inA (Ident "C"))
      , declared "D" (inA (Ident "D"))
      , declared "get" (inA (Ident "get"))
      ]
  , types = Map.fromFoldable
      [ Tuple "T" { entity: TypeEntity (inA (TyName "T")), via: Declared, members: [ Ident "C", Ident "D" ] }
      , Tuple "E" { entity: EffectEntity (inA (EffName "E")), via: Declared, members: [ Ident "get" ] }
      ]
  , operators = Map.singleton "+" { entity: inA (OperatorName "+"), via: Declared }
  , typeOperators = Map.singleton "+" { entity: inA (OperatorName "+"), via: Declared }
  , macros = Map.singleton "m" { entity: inA (Ident "m"), via: Declared }
  , attributes = Map.singleton "json" { entity: inA (Ident "json"), via: Declared }
  }
  where
  declared n e = Tuple n { entity: e, via: Declared }

interfaceOf :: ModuleName -> Array ModuleName -> Exports -> ModuleInterface
interfaceOf name imports exports =
  { name
  , imports
  , exports
  , declarations: emptyDeclarations
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  }

-- | `B` imports `A`, exports its own `x`, and re-exports `A`'s `T` and `+`.
exportsB :: Exports
exportsB = emptyExports
  { values = Map.singleton "x" { entity: Qualified moduleB (Ident "x"), via: Declared }
  , types = Map.singleton "T" { entity: TypeEntity (inA (TyName "T")), via: ThroughImport moduleA, members: [] }
  , operators = Map.singleton "+" { entity: inA (OperatorName "+"), via: ThroughImport moduleA }
  }

environment :: BuildEnvironment
environment = case addInterface (interfaceOf moduleA [] exportsA) initialEnvironment >>= addInterface (interfaceOf moduleB [ moduleA ] exportsB) of
  Right env -> env
  Left _ -> initialEnvironment

type Resolved = { scoped :: ScopedModule, errors :: Array ScopeError, warnings :: Array ScopeWarning }

-- | The module `M` whose header and body are the lines given, resolved.
resolved :: Array String -> (Resolved -> Aff Unit) -> Aff Unit
resolved = resolvedAs "M"

resolvedAs :: String -> Array String -> (Resolved -> Aff Unit) -> Aff Unit
resolvedAs header body k = case parseModule (joinWith "\n" ([ "module " <> header <> " where" ] <> body)) of
  Left e -> fail (printSyntaxError e)
  Right m -> k (resolveScope environment (groupModule m).grouped)

reasons :: Resolved -> Array ScopeReason
reasons r = map (\(ScopeError _ reason) -> reason) r.errors

-- | The entities a name stands for unqualified, the module's own first.
unqualifiedValue :: String -> Resolved -> Array (Qualified Ident)
unqualifiedValue n r = case Map.lookup n r.scoped.scope.declared.values of
  Just cs -> map _.entity cs
  Nothing -> map _.entity (Array.concat (Array.fromFoldable (Map.lookup n r.scoped.scope.imported.values)))

spec :: Spec Unit
spec = describe "Stella.Compiler.Resolve.Scope" do
  describe "Prim" do
    it "is opened unqualified where the header imports it nowhere, and is no dependency" do
      resolved [ "x = 1" ] \r -> do
        unqualifiedValue "Unit" r `shouldEqual` [ unitCtor ]
        r.scoped.imports `shouldEqual` []

    it "is opened as an import of it says where one is written, and is still no dependency" do
      resolved [ "import Prim as P", "x = 1" ] \r -> do
        unqualifiedValue "Unit" r `shouldEqual` []
        map (map _.entity) (Map.lookup "P" r.scoped.scope.qualified >>= Map.lookup "Unit" <<< _.values) `shouldEqual` Just [ unitCtor ]
        r.scoped.imports `shouldEqual` []
      resolved [ "import Prim hiding (Unit)", "x = 1" ] \r -> do
        Map.member "Unit" r.scoped.scope.imported.types `shouldEqual` false
        unqualifiedValue "Unit" r `shouldEqual` [ unitCtor ]
      resolved [ "import Prim hiding (Unit(..))", "x = 1" ] \r ->
        unqualifiedValue "Unit" r `shouldEqual` []

  describe "imports" do
    it "bring everything a module exports, each through the import" do
      resolved [ "import A" ] \r -> do
        unqualifiedValue "x" r `shouldEqual` [ inA (Ident "x") ]
        map (map _.via) (Map.lookup "x" r.scoped.scope.imported.values) `shouldEqual` Just [ ThroughImport moduleA ]
        map _.module r.scoped.imports `shouldEqual` [ moduleA ]

    it "bring the items of a list, a type's members only where they are named" do
      resolved [ "import A (x, T, E(..), (+), type (+), macro m, attribute json)" ] \r -> do
        unqualifiedValue "x" r `shouldEqual` [ inA (Ident "x") ]
        unqualifiedValue "C" r `shouldEqual` []
        unqualifiedValue "get" r `shouldEqual` [ inA (Ident "get") ]
        map (map _.members) (Map.lookup "T" r.scoped.scope.imported.types) `shouldEqual` Just [ [] ]
        Map.member "+" r.scoped.scope.imported.typeOperators `shouldEqual` true
        Map.member "m" r.scoped.scope.imported.macros `shouldEqual` true
        r.errors `shouldEqual` []
      resolved [ "import A (T(C))" ] \r -> do
        unqualifiedValue "C" r `shouldEqual` [ inA (Ident "C") ]
        unqualifiedValue "D" r `shouldEqual` []

    it "report an item the module does not export, and a member a type is not published with" do
      resolved [ "import A (y, T(Z), type (*))" ] \r ->
        reasons r `shouldEqual`
          [ NotExported moduleA ValueNamespace "y", NotAMember "T" "Z", NotExported moduleA TypeOperatorNamespace "*" ]

    it "bring everything but what `hiding` names, and report a name hidden that is not exported" do
      resolved [ "import A hiding (x, T(..), nope)" ] \r -> do
        unqualifiedValue "x" r `shouldEqual` []
        unqualifiedValue "C" r `shouldEqual` []
        Map.member "T" r.scoped.scope.imported.types `shouldEqual` false
        unqualifiedValue "get" r `shouldEqual` [ inA (Ident "get") ]
        reasons r `shouldEqual` [ NotExported moduleA ValueNamespace "nope" ]

    it "bring nothing with an empty list, and declare the dependency all the same" do
      resolved [ "import A ()" ] \r -> do
        unqualifiedValue "x" r `shouldEqual` []
        map _.module r.scoped.imports `shouldEqual` [ moduleA ]

    it "bring names through an alias, and through a lazy alias only to a local open" do
      resolved [ "import A as Q", "import lazy A as L" ] \r -> do
        unqualifiedValue "x" r `shouldEqual` []
        Map.member "Q" r.scoped.scope.qualified `shouldEqual` true
        Map.member "L" r.scoped.scope.qualified `shouldEqual` false
        Map.member "L" r.scoped.scope.lazy `shouldEqual` true

    it "report a lazy import with no alias, or with a list" do
      resolved [ "import lazy A", "import lazy A (x) as L" ] \r ->
        reasons r `shouldEqual` [ LazyImportNotQualified, LazyImportNotQualified ]

    it "report a module the environment does not hold, and record no dependency on it" do
      resolved [ "import Nowhere" ] \r -> do
        reasons r `shouldEqual` [ ModuleNotFound (ModuleName "Nowhere") ]
        r.scoped.imports `shouldEqual` []

    it "keep one candidate for one entity two imports bring, and both for two" do
      resolved [ "import A", "import B (T, (+))" ] \r -> do
        map Array.length (Map.lookup "T" r.scoped.scope.imported.types) `shouldEqual` Just 1
        map Array.length (Map.lookup "+" r.scoped.scope.imported.operators) `shouldEqual` Just 1
      resolved [ "import A", "import B" ] \r ->
        unqualifiedValue "x" r `shouldEqual` [ inA (Ident "x"), Qualified moduleB (Ident "x") ]

  describe "declarations" do
    it "put the module's own names in scope, hiding an imported one with a warning" do
      resolved [ "import A", "x = 1", "data U = C" ] \r -> do
        unqualifiedValue "x" r `shouldEqual` [ Qualified (ModuleName "M") (Ident "x") ]
        map (\(HidesImport _ ns n) -> Tuple ns n) r.warnings `shouldEqual` [ Tuple ValueNamespace "x", Tuple ValueNamespace "C" ]

    it "report a name declared twice in one namespace, an operation and a value among them" do
      resolved [ "x = 1", "x = 2", "effect E where", "  get :: Unit ->* Int", "get = 3" ] \r ->
        reasons r `shouldEqual` [ DeclaredTwice ValueNamespace "x", DeclaredTwice ValueNamespace "get" ]

    it "keep one spelling apart in different namespaces" do
      resolved [ "data P = P", "infixl 6 add as +", "infixl 6 type P as +", "add = 1" ] \r -> do
        r.errors `shouldEqual` []
        Map.member "+" r.scoped.scope.declared.operators `shouldEqual` true
        Map.member "+" r.scoped.scope.declared.typeOperators `shouldEqual` true

    it "keep the module's own macro out of its value namespace, and its attributes in its own" do
      resolved [ "attribute instance", "@[macro]", "format = 1" ] \r -> do
        unqualifiedValue "format" r `shouldEqual` []
        Map.member "instance" r.scoped.scope.declared.attributes `shouldEqual` true

  describe "an elaboration-only entry" do
    let
      continuation = [ "@[elaborationOnly]", "newtype Continuation a = Continuation a" ]
      internal = Qualified (ModuleName "Base.Continuation") (Ident "$Continuation")

    it "takes its internal identity in the module the compiler lists, under its source name there" do
      resolvedAs "Base.Continuation" continuation \r -> do
        r.errors `shouldEqual` []
        unqualifiedValue "Continuation" r `shouldEqual` [ internal ]

    it "is exported by no export list, and is no member of its type" do
      resolvedAs "Base.Continuation" continuation \r -> do
        Map.member "Continuation" r.scoped.exports.values `shouldEqual` false
        map _.members (Map.lookup "Continuation" r.scoped.exports.types) `shouldEqual` Just []
      resolvedAs "Base.Continuation (Continuation(..))" continuation \r ->
        map _.members (Map.lookup "Continuation" r.scoped.exports.types) `shouldEqual` Just []
      resolvedAs "Base.Continuation (Continuation(Continuation))" continuation \r ->
        reasons r `shouldEqual` [ NotAMember "Continuation" "Continuation" ]

    it "is refused where the declaration is not exactly the one the compiler lists" do
      resolvedAs "Base.Continuation" [ "@[elaborationOnly]", "newtype Continuation a = Wrap a" ] \r -> do
        reasons r `shouldEqual` [ ElaborationOnlyNotAllowed ]
        unqualifiedValue "Wrap" r `shouldEqual` [ Qualified (ModuleName "Base.Continuation") (Ident "Wrap") ]
      resolvedAs "Base.Continuation" [ "@[elaborationOnly]", "data Continuation a = Continuation a" ] \r -> do
        reasons r `shouldEqual` [ ElaborationOnlyNotAllowed ]
        unqualifiedValue "Continuation" r `shouldEqual` [ Qualified (ModuleName "Base.Continuation") (Ident "Continuation") ]
      resolvedAs "Base.Continuation" [ "@[elaborationOnly]", "data Continuation a = Continuation a | Extra" ] \r -> do
        reasons r `shouldEqual` [ ElaborationOnlyNotAllowed ]
        map _.members (Map.lookup "Continuation" r.scoped.exports.types) `shouldEqual` Just [ Ident "Continuation", Ident "Extra" ]

    it "is reported on a declaration the compiler does not list" do
      resolved continuation \r -> do
        reasons r `shouldEqual` [ ElaborationOnlyNotAllowed ]
        unqualifiedValue "Continuation" r `shouldEqual` [ Qualified (ModuleName "M") (Ident "Continuation") ]

  describe "exports" do
    it "are every declaration of the module and nothing imported, where there is no list" do
      resolved [ "import A", "y = 1", "data U = K", "infixl 6 type U as *" ] \r -> do
        Map.keys r.scoped.exports.values `shouldEqual` Set.fromFoldable [ "y", "K" ]
        map _.members (Map.lookup "U" r.scoped.exports.types) `shouldEqual` Just [ Ident "K" ]
        Map.member "*" r.scoped.exports.typeOperators `shouldEqual` true

    it "re-export what an import brought, by the way it came, and the module's own as declared" do
      resolvedAs "M (x, y, T(..), (+), macro m)" [ "import A", "y = 1" ] \r -> do
        r.errors `shouldEqual` []
        Map.lookup "x" r.scoped.exports.values `shouldEqual` Just { entity: inA (Ident "x"), via: ThroughImport moduleA }
        Map.lookup "y" r.scoped.exports.values `shouldEqual` Just { entity: Qualified (ModuleName "M") (Ident "y"), via: Declared }
        Map.lookup "C" r.scoped.exports.values `shouldEqual` Just { entity: inA (Ident "C"), via: ThroughImport moduleA }
        map _.members (Map.lookup "T" r.scoped.exports.types) `shouldEqual` Just [ Ident "C", Ident "D" ]

    it "re-export by `T(..)` every member in scope, whichever import brought it" do
      resolvedAs "M (T(..))" [ "import A hiding (T)", "import A (T)" ] \r -> do
        r.errors `shouldEqual` []
        map _.members (Map.lookup "T" r.scoped.exports.types) `shouldEqual` Just [ Ident "C", Ident "D" ]
        Map.member "D" r.scoped.exports.values `shouldEqual` true
      resolvedAs "M (T(..), T(D))" [ "import A (T(C))" ] \r -> do
        map _.members (Map.lookup "T" r.scoped.exports.types) `shouldEqual` Just [ Ident "C" ]
        reasons r `shouldEqual` [ ExportNotInScope ValueNamespace "D" ]

    it "publish a member the way it came, which need not be the way its type did" do
      resolvedAs "M (T(C))" [ "import B (T)", "import A (T(C))" ] \r -> do
        r.errors `shouldEqual` []
        map _.via (Map.lookup "T" r.scoped.exports.types) `shouldEqual` Just (ThroughImport moduleB)
        map _.via (Map.lookup "C" r.scoped.exports.values) `shouldEqual` Just (ThroughImport moduleA)

    it "choose a member named twice once, on import and on export" do
      resolved [ "import A (T(C, C))" ] \r ->
        map (map _.members) (Map.lookup "T" r.scoped.scope.imported.types) `shouldEqual` Just [ [ Ident "C" ] ]
      resolvedAs "M (T(C, C))" [ "import A" ] \r -> do
        r.errors `shouldEqual` []
        map _.members (Map.lookup "T" r.scoped.exports.types) `shouldEqual` Just [ Ident "C" ]

    it "unite the members of one type two whole re-exports bring, in order" do
      resolvedAs "M (module Q, module R)" [ "import A (T(C)) as Q", "import A (T(D)) as R" ] \r -> do
        r.errors `shouldEqual` []
        map _.members (Map.lookup "T" r.scoped.exports.types) `shouldEqual` Just [ Ident "C", Ident "D" ]

    it "export a type, a macro, and an attribute named through an alias" do
      resolvedAs "M (Q.T(..), macro Q.m, attribute Q.json)" [ "import A as Q" ] \r -> do
        r.errors `shouldEqual` []
        map _.members (Map.lookup "T" r.scoped.exports.types) `shouldEqual` Just [ Ident "C", Ident "D" ]
        map _.via (Map.lookup "m" r.scoped.exports.macros) `shouldEqual` Just (ThroughImport moduleA)
        Map.member "json" r.scoped.exports.attributes `shouldEqual` true

    it "export the module's own macro by name" do
      resolvedAs "M (macro format)" [ "@[macro]", "format = 1" ] \r -> do
        r.errors `shouldEqual` []
        map _.entity (Map.lookup "format" r.scoped.exports.macros) `shouldEqual` Just (Qualified (ModuleName "M") (Ident "format"))

    it "report a name nothing stands for, one several stand for, and one exported for two entities" do
      resolvedAs "M (nope, x)" [ "import A", "import B" ] \r ->
        reasons r `shouldEqual` [ ExportNotInScope ValueNamespace "nope", ExportAmbiguous ValueNamespace "x" ]
      resolvedAs "M (A.x, B.x)" [ "import A as A", "import B as B" ] \r ->
        reasons r `shouldEqual` [ ExportedTwice ValueNamespace "x" ]

    it "re-export a whole alias, and a whole import without one" do
      resolvedAs "M (module Q)" [ "import A as Q" ] \r -> do
        r.errors `shouldEqual` []
        r.scoped.exports.modules `shouldEqual` [ moduleA ]
        Map.member "get" r.scoped.exports.values `shouldEqual` true
        Map.member "E" r.scoped.exports.types `shouldEqual` true
      resolvedAs "M (module A)" [ "import A (x)" ] \r -> do
        Map.keys r.scoped.exports.values `shouldEqual` Set.singleton "x"

    it "report the module itself, a lazy alias, and a name that is no import" do
      resolvedAs "M (module M, module L, module Z)" [ "import lazy A as L" ] \r ->
        reasons r `shouldEqual` [ ExportOwnModule, ExportLazyAlias "L", ExportModuleNotImported "Z" ]
