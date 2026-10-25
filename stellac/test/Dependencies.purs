-- | `dependencies` of `stella.json`: the order its interfaces enter the build
-- | environment, and how an interface that cannot be used is reported.
-- |
-- | The interfaces are empty but for their names and imports, which is all that
-- | ordering reads; the files are a map from path to text or bytes.
module Test.Stellac.Dependencies (spec) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), either)
import Data.Foldable (for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String (Pattern(..), stripPrefix)
import Data.Tuple (Tuple(..))
import Effect.Exception (error, throwException)
import Effect.Unsafe (unsafePerformEffect)
import Run (Run)
import Run as Run
import Stella.CLI.Effect.FS (FileSystem(..))
import Stella.CLI.Effect.FS as FS
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.Interface.Module (ModuleInterface, emptyDeclarations, emptyExports)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..))
import Stellac.Dependencies (Dependency, DependencyError(..), dependedOn, extend)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

interfaceOf :: String -> Array String -> ModuleInterface
interfaceOf name imports =
  { name: ModuleName name
  , imports: map ModuleName imports
  , exports: emptyExports
  , declarations: emptyDeclarations
  , implicitHandlers: []
  , catalogOnly: Set.empty
  , arities: Map.empty
  , entrypoint: Nothing
  }

-- | `Prim` and a module standing for one the compiler provides.
carried :: BuildEnvironment
carried = either (\e -> unsafePerformEffect (throwException (error (show e)))) identity
  (addInterface (interfaceOf "Base.Int" []) initialEnvironment)

loaded :: String -> Array String -> { dependency :: Dependency, interface :: ModuleInterface }
loaded name imports =
  { dependency: { module: ModuleName name, interface: name <> ".dmi", object: name <> ".dmo" }
  , interface: interfaceOf name imports
  }

-- | The modules of the environment, in the order of their names.
modulesOf :: BuildEnvironment -> Array String
modulesOf env = map (\(ModuleName m) -> m) (Array.fromFoldable (Map.keys env.interfaces))

extended :: Array { dependency :: Dependency, interface :: ModuleInterface } -> Either (Array DependencyError) (Array String)
extended ls = case extend carried ls of
  Left errors -> Left (NonEmptyArray.toArray errors)
  Right env -> Right (modulesOf env)

names :: String -> Array String -> NonEmptyArray.NonEmptyArray ModuleName
names first rest = NonEmptyArray.cons' (ModuleName first) (map ModuleName rest)

data File = Text String | Binary Bytes

-- | The files given, read from; a path is absolute where it begins with `/`.
reading :: forall a. Map String File -> Run (FS.FS ()) a -> a
reading files p = Run.extract (FS.interpret handler p)
  where
  handler :: FileSystem ~> Run ()
  handler = case _ of
    ReadText path reply -> pure
      ( reply
          ( case Map.lookup path files of
              Just (Text t) -> Right t
              _ -> Left "no such file"
          )
      )
    ReadBytes path reply -> pure
      ( reply
          ( case Map.lookup path files of
              Just (Binary b) -> Right b
              _ -> Left "no such file"
          )
      )
    IsAbsolute path reply -> pure (reply (stripPrefix (Pattern "/") path /= Nothing))
    Resolve path reply -> pure (reply path)
    WriteBytes _ _ reply -> pure (reply (Left "read only"))
    WriteText _ _ reply -> pure (reply (Left "read only"))
    MakeDirectory _ reply -> pure (reply (Left "read only"))
    Remove _ reply -> pure (reply (Left "read only"))
    Glob _ _ reply -> pure (reply (Right []))

bytesOf :: ModuleInterface -> File
bytesOf i = case Interface.encode { interface: i, buildHash: Nothing } of
  Right bytes -> Binary bytes
  Left e -> unsafePerformEffect (throwException (error (show e)))

spec :: Spec Unit
spec = describe "`dependencies`" do
  describe "the environment" do
    it "adds the interfaces in the order their imports give, whatever order they are listed in" do
      let
        listed = [ loaded "C" [ "B", "Base.Int" ], loaded "A" [], loaded "B" [ "A" ] ]
        expected = Right [ "A", "B", "Base.Int", "C", "Prim" ]
      extended listed `shouldEqual` expected
      extended (Array.reverse listed) `shouldEqual` expected

    it "accepts a listed module nothing imports" do
      extended [ loaded "A" [], loaded "Unused" [ "A" ] ] `shouldEqual` Right [ "A", "Base.Int", "Prim", "Unused" ]

    it "reports an import neither listed nor provided, of a module nothing imports as well" do
      extended [ loaded "A" [], loaded "Unused" [ "Gone" ] ] `shouldEqual` Left [ ImportUnlisted (ModuleName "Unused") (ModuleName "Gone") ]

    it "reports the modules of a cycle, and not a module that only imports one of them" do
      extended [ loaded "C" [ "A" ], loaded "B" [ "A" ], loaded "A" [ "B" ], loaded "D" [ "D" ] ]
        `shouldEqual` Left [ ImportCycle (names "A" [ "B" ]), ImportCycle (names "D" []) ]

    it "tells an unlisted import from a cycle where both stop it" do
      extended [ loaded "A" [ "B" ], loaded "B" [ "A" ], loaded "C" [ "Gone" ], loaded "E" [ "C" ] ]
        `shouldEqual` Left [ ImportUnlisted (ModuleName "C") (ModuleName "Gone"), ImportCycle (names "A" [ "B" ]) ]

    it "accepts a seed module, listed with the interface of the seed module held" do
      extended [ loaded "A" [ "Base.Int" ], loaded "Base.Int" [] ] `shouldEqual` Right [ "A", "Base.Int", "Prim" ]

    it "refuses a seed module, listed with another interface" do
      extended [ (loaded "Base.Int" []) { interface { arities = Map.singleton (Ident "add") 2 } } ]
        `shouldEqual` Left [ DiffersFromCarried (ModuleName "Base.Int") ]

    it "refuses `Prim`, whatever it is listed with" do
      for_ (Map.lookup (ModuleName "Prim") initialEnvironment.interfaces) \prim ->
        extended [ { dependency: (loaded "Prim" []).dependency, interface: prim } ]
          `shouldEqual` Left [ ProvidedByCompiler (ModuleName "Prim") ]
      extended [ loaded "Prim" [] ] `shouldEqual` Left [ ProvidedByCompiler (ModuleName "Prim") ]

    it "refuses a module listed twice, whether or not it is a seed module" do
      extended [ loaded "A" [], loaded "Base.Int" [], loaded "A" [], loaded "Base.Int" [] ]
        `shouldEqual` Left [ ListedTwice (ModuleName "A"), ListedTwice (ModuleName "Base.Int") ]

  describe "reading the interfaces" do
    let
      at m = { module: ModuleName m, interface: m <> ".dmi", object: m <> ".dmo" }

    it "adds the interfaces of the entries given, read from their paths" do
      let
        files = Map.fromFoldable
          [ Tuple "A.dmi" (bytesOf (interfaceOf "A" []))
          , Tuple "B.dmi" (bytesOf (interfaceOf "B" [ "A" ]))
          ]
      case reading files (dependedOn [ at "B", at "A" ] carried) of
        Left errors -> fail (show errors)
        Right env -> modulesOf env `shouldEqual` [ "A", "B", "Base.Int", "Prim" ]

    it "reports every interface that cannot be used, by its module and its path" do
      let
        files = Map.fromFoldable
          [ Tuple "B.dmi" (Binary [ 0x44, 0x4D, 0x4F, 0x00 ])
          , Tuple "C.dmi" (bytesOf (interfaceOf "D" []))
          ]
      case reading files (dependedOn [ at "A", at "B", at "C" ] carried) of
        Right _ -> fail "the interfaces were used"
        Left errors -> case NonEmptyArray.toArray errors of
          [ InterfaceUnreadable a _, InterfaceRejected b _, InterfaceOfAnother c other ] -> do
            a `shouldEqual` at "A"
            b `shouldEqual` at "B"
            c `shouldEqual` at "C"
            other `shouldEqual` ModuleName "D"
          other -> fail (show other)
