-- | The modules the compiler carries, made from their sources: the text the
-- | compiler holds is the file's as it stands, and the `Base.Int` it carries is
-- | that text compiled as a build compiles a module.
-- |
-- | **The last group watches the hand-written Core of the fixtures**, which
-- | stands for `Base.Int` where a test compiles Core rather than source: it is to
-- | give what the source gives, and goes with those fixtures.
module Test.Stella.Compiler.Bootstrap (spec) where

import Prelude

import Control.Monad.State (State, put, runState)
import Data.Array as Array
import Data.Array.NonEmpty as NonEmptyArray
import Data.Bifunctor (bimap, lmap)
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Stella.Compiler.Bootstrap.Source as Source
import Stella.Compiler.Build (CompilerAction, compileModule, defaultHooks, printCompileError, withoutSynthesizers)
import Stella.Compiler.Bytecode (Dmo, encode, lower)
import Stella.Compiler.Interface (importsOf)
import Stella.Compiler.Interface.Environment (initialEnvironment)
import Stella.Compiler.Interface.FromCore (FromCoreError, interfaceOfCore)
import Stella.Compiler.Interface.Module (ModuleInterface)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.Macro.Run (ExecutionReason(..), ParseOutcome(..), defaultSettings)
import Stella.Compiler.Primitive (baseModule, withBaseTypes)
import Stella.Compiler.Surface.Origin (Origin)
import Stella.Compiler.TypedCore (Decl(..), Module, declareAnnotated, primSignature)
import Stella.Compiler.TypedCore.Name (Ident, ModuleName(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

foreign import readRepositoryFile :: String -> Effect String

baseIntPath :: String
baseIntPath = "stella-packages/base/src/Base/Int.stel"

-- | The text given compiled as a build compiles a module against `Prim` alone:
-- | its interface and its bytecode, or the errors compiling it gave, and the Core
-- | it elaborates to.
compiledSource :: String -> { made :: Either String { interface :: ModuleInterface, dmo :: Dmo }, core :: Maybe (Module Origin) }
compiledSource text = case runState (compileModule action defaultSettings initialEnvironment Map.empty text) Nothing of
  Tuple made core -> { made: bimap printed (\m -> { interface: m.interface, dmo: m.dmo }) made, core }
  where
  printed errors = joinWith "; " (map printCompileError (NonEmptyArray.toArray errors))

  action :: CompilerAction (State (Maybe (Module Origin)))
  action =
    { readSource: \_ -> pure (Left "no file is read")
    , runParser: \_ _ _ -> pure (ExecutionFailedAs { reason: NoSuchModule, detail: "no parser runs" })
    , synthesis: withoutSynthesizers
    , hooks: defaultHooks { onElaborated = \m -> put (Just m) }
    }

-- | A module of foreigns with its annotations forgotten, or nothing where it
-- | declares anything else.
foreignsOnly :: forall a. Module a -> Maybe (Module Unit)
foreignsOnly m = do
  decls <- traverse forgotten m.decls
  pure { annotation: unit, name: m.name, imports: m.imports, exports: m.exports, decls }
  where
  forgotten = case _ of
    DeclForeign _ f -> Just (DeclForeign unit f)
    _ -> Nothing

-- | The hand-written `Base.Int` checked, translated, and lowered as the fixtures
-- | compile it, with the interface it gives at the arities given.
handWritten :: Either String { dmo :: Dmo, interface :: Map Ident Int -> Either FromCoreError ModuleInterface }
handWritten = do
  declared <- lmap (show <<< _.error) (declareAnnotated (withBaseTypes primSignature) hand)
  imports <- lmap show (importsOf [])
  mid <- lmap show (translate imports hand declared)
  lowered <- lmap show (lower mid)
  pure { dmo: lowered.dmo, interface: interfaceOfCore hand declared }
  where
  hand = baseModule unit (ModuleName "Base.Int")

spec :: Spec Unit
spec = describe "the modules the compiler carries, from their sources" do
  it "holds the text of `stella-packages/base/src/Base/Int.stel` as the file stands" do
    text <- liftEffect (readRepositoryFile baseIntPath)
    when (text /= Source.baseInt) (fail (baseIntPath <> " differs from the text the compiler holds; run `npm run embed -w compiler`"))

  it "carries `Base.Int` as that text compiles, its interface and its bytecode" do
    case (compiledSource Source.baseInt).made, compiled of
      Left why, _ -> fail why
      _, Left why -> fail why
      Right made, Right carried -> do
        Map.lookup (ModuleName "Base.Int") carried.preloaded `shouldEqual` Just made.interface
        map encode (Array.head carried.modules) `shouldEqual` Just (encode made.dmo)

  describe "the hand-written `Base.Int` the fixtures compile" do
    it "is the Core the source elaborates to" do
      case compiledSource Source.baseInt of
        { made: Left why } -> fail why
        { core: Just core } -> foreignsOnly core `shouldEqual` Just (baseModule unit (ModuleName "Base.Int"))
        _ -> fail "no Core"

    it "has the interface and the bytecode of the source" do
      case (compiledSource Source.baseInt).made, handWritten of
        Left why, _ -> fail why
        _, Left why -> fail why
        Right made, Right hand -> do
          hand.interface made.interface.arities `shouldEqual` Right made.interface
          encode hand.dmo `shouldEqual` encode made.dmo
