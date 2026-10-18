-- | Loading a build's modules into its compile-time session: the walk through
-- | a module's imports stops at the seed, the modules the session holds from
-- | its opening; a module of the seed is never located or loaded, and one the
-- | build compiled anew must have the interface of the one held.
-- |
-- | Every module here that would be loaded is one `locate` finds no bytecode
-- | of, so the session is asked for nothing, and what `locate` was asked is
-- | what the walk went to load.
module Test.Stella.CLI.Session.CompileTime (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run)
import Run as Run
import Run.Except (EXCEPT)
import Run.Except as Except
import Stella.CLI.Effect.Process (PROCESS)
import Stella.CLI.Session.CompileTime (CompileTimeError, ensureLoaded, reached)
import Stella.Compiler.Build (BuiltModules)
import Stella.Compiler.Interface.Module (ModuleInterface, emptyDeclarations, emptyExports)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Stella.CLI.Session.Broker (node, withSession)
import Type.Row (type (+))

-- | A module importing the modules given, declaring nothing; or declaring
-- | the value `n` where `marked`.
interfaceOf :: String -> Array String -> Boolean -> ModuleInterface
interfaceOf name imports marked =
  { name: ModuleName name
  , imports: map ModuleName imports
  , exports: emptyExports
  , declarations: emptyDeclarations
  , implicitHandlers: []
  , catalogOnly: if marked then Set.singleton (Ident "n") else Set.empty
  , arities: Map.empty
  }

-- | The seed: `Base.Int`, and `Stella.Syntax` over it.
seed :: Map.Map ModuleName ModuleInterface
seed = Map.fromFoldable (map (\i -> Tuple i.name i) [ interfaceOf "Base.Int" [] false, interfaceOf "Stella.Syntax" [ "Base.Int" ] false ])

importsIn :: BuiltModules -> ModuleName -> Maybe (Array ModuleName)
importsIn built m = map _.imports (Map.lookup m built)

builtOf :: Array ModuleInterface -> BuiltModules
builtOf = Map.fromFoldable <<< map (\i -> Tuple i.name i)

type Running = Run (EXCEPT CompileTimeError + PROCESS + AFF + EFFECT + ())

-- | `ensureLoaded` for the module given, the build's modules the ones given:
-- | how it ended, and the modules `locate` was asked for.
loading :: BuiltModules -> String -> Aff { ended :: String, located :: Array String }
loading built declaring = do
  asked <- liftEffect (Ref.new [])
  ended <- liftEffect (Ref.new "")
  _ <- withSession "const guest = async (p) => failed('unused');" \session -> do
    loaded <- liftEffect (Ref.new Set.empty)
    let
      run =
        { seed
        , importsOf: const Nothing
        , loaded
        , locate: \(ModuleName m) -> Nothing <$ Run.liftEffect (Ref.modify_ (\l -> Array.snoc l m) asked)
        }
    outcome <- node (Except.runExcept (ensureLoaded run session built (ModuleName declaring) :: Running Unit))
    liftEffect $ Ref.write (either' outcome) ended
  { ended: _, located: _ } <$> liftEffect (Ref.read ended) <*> liftEffect (Ref.read asked)
  where
  either' = case _ of
    Left failure -> show failure
    Right _ -> "loaded"

spec :: Spec Unit
spec = describe "Stella.CLI.Session.CompileTime" do
  describe "the walk through a module's imports" do
    it "goes to load each module after those it imports, and stops at the seed" do
      let built = builtOf [ interfaceOf "Support" [ "Base.Int" ] false, interfaceOf "Pass" [ "Support", "Stella.Syntax", "Prim" ] false ]
      reached (importsIn built) (Map.keys seed) (ModuleName "Pass") `shouldEqual`
        { load: map ModuleName [ "Support", "Pass" ], seedsReached: Set.fromFoldable (map ModuleName [ "Base.Int", "Stella.Syntax" ]) }

    it "takes a module of the seed the build compiled anew for the one the session holds, walking nothing past it" do
      let built = builtOf [ interfaceOf "Base.Int" [ "Support" ] false, interfaceOf "Support" [] false, interfaceOf "Pass" [ "Base.Int" ] false ]
      reached (importsIn built) (Map.keys seed) (ModuleName "Pass") `shouldEqual`
        { load: [ ModuleName "Pass" ], seedsReached: Set.singleton (ModuleName "Base.Int") }

  describe "loading a module" do
    it "locates the modules of the build it reaches and none of the seed, one compiled anew among them" do
      r <- loading (builtOf [ interfaceOf "Base.Int" [] false, interfaceOf "Pass" [ "Base.Int", "Stella.Syntax" ] false ]) "Pass"
      r `shouldEqual` { ended: "(ModuleUnavailable \"Pass\")", located: [ "Pass" ] }

    it "locates nothing for a module of the seed" do
      r <- loading Map.empty "Stella.Syntax"
      r `shouldEqual` { ended: "loaded", located: [] }

    it "refuses a module of the seed compiled anew with another interface, before locating anything" do
      r <- loading (builtOf [ interfaceOf "Base.Int" [] true, interfaceOf "Pass" [ "Base.Int" ] false ]) "Pass"
      r `shouldEqual` { ended: "(RebuiltDiffersFromSeed \"Base.Int\")", located: [] }
