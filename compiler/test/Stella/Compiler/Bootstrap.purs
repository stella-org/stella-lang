-- | The modules the compiler carries, made from their sources: what the compiler
-- | holds of `Base.Int` and of `Stella.Syntax` is what compiling each source as
-- | a build compiles a module writes, the interface file and the bytecode file
-- | to the byte, and the modules it carries are those files decoded.
-- |
-- | **The last group watches the hand-written Core of the fixtures**, which
-- | stands for `Base.Int` where a test compiles Core rather than source: it is to
-- | give what the source gives, and goes with those fixtures.
module Test.Stella.Compiler.Bootstrap (spec) where

import Prelude

import Control.Monad.State (State, put, runState)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Bifunctor (bimap, lmap)
import Data.Either (Either(..))
import Data.Int as Int
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect.Class (liftEffect)
import Stella.Compiler.Bootstrap.Source (Carried)
import Stella.Compiler.Bootstrap.Source as Source
import Stella.Compiler.Build (CompilerAction, compileModule, defaultHooks, printCompileError, withoutSynthesizers)
import Stella.Compiler.Bytecode (Dmo, encode, lower)
import Stella.Compiler.Interface (importsOf)
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment)
import Stella.Compiler.Interface.File as Interface
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
import Test.Stella.Compiler.Sources (baseIntPath, readRepositoryFile, syntaxPath)

-- | The text given compiled as a build compiles a module against the
-- | environment given: its interface and its bytecode, or the errors compiling
-- | it gave, and the Core it elaborates to.
compiledSource :: BuildEnvironment -> String -> { made :: Either String { interface :: ModuleInterface, dmo :: Dmo }, core :: Maybe (Module Origin) }
compiledSource env text = case runState (compileModule action defaultSettings env Map.empty text) Nothing of
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

-- | `Base.Int` compiled from the text given against `Prim` alone, and
-- | `Stella.Syntax` from the text given against an environment holding it.
fromSources :: String -> String -> Either String { base :: { interface :: ModuleInterface, dmo :: Dmo }, syntax :: { interface :: ModuleInterface, dmo :: Dmo } }
fromSources baseText syntaxText = do
  base <- (compiledSource initialEnvironment baseText).made
  env <- lmap show (addInterface base.interface initialEnvironment)
  syntax <- (compiledSource env syntaxText).made
  pure { base, syntax }

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

-- | A module's interface file and bytecode file, each in hexadecimal, as the
-- | compiler holds a module it carries.
filesOf :: { interface :: ModuleInterface, dmo :: Dmo } -> Either String Carried
filesOf made = do
  interface <- lmap show (Interface.encode { interface: made.interface, buildHash: Nothing })
  bytecode <- lmap show (encode made.dmo)
  pure { interface: toHex interface, bytecode: toHex bytecode }
  where
  toHex = joinWith "" <<< map (\b -> (if b < 16 then "0" else "") <> Int.toStringAs Int.hexadecimal b)

spec :: Spec Unit
spec = describe "the modules the compiler carries, from their sources" do
  it "holds the files compiling `Base.Int` and `Stella.Syntax` from their sources writes, the second against the first" do
    baseText <- liftEffect (readRepositoryFile baseIntPath)
    syntaxText <- liftEffect (readRepositoryFile syntaxPath)
    case fromSources baseText syntaxText of
      Left why -> fail why
      Right made -> do
        when (filesOf made.base /= Right Source.baseInt) (fail (baseIntPath <> " compiles to other files than the compiler holds; run `npm run embed -w compiler`"))
        when (filesOf made.syntax /= Right Source.stellaSyntax) (fail (syntaxPath <> " compiles to other files than the compiler holds; run `npm run embed -w compiler`"))

  it "carries those modules as their files decode" do
    baseText <- liftEffect (readRepositoryFile baseIntPath)
    syntaxText <- liftEffect (readRepositoryFile syntaxPath)
    case fromSources baseText syntaxText, compiled of
      Left why, _ -> fail why
      _, Left why -> fail why
      Right made, Right carried -> do
        Map.lookup (ModuleName "Base.Int") carried.preloaded `shouldEqual` Just made.base.interface
        Map.lookup (ModuleName "Stella.Syntax") carried.preloaded `shouldEqual` Just made.syntax.interface
        map encode carried.modules `shouldEqual` map encode [ made.base.dmo, made.syntax.dmo ]

  describe "the hand-written `Base.Int` the fixtures compile" do
    it "is the Core the source elaborates to" do
      text <- liftEffect (readRepositoryFile baseIntPath)
      case compiledSource initialEnvironment text of
        { made: Left why } -> fail why
        { core: Just core } -> foreignsOnly core `shouldEqual` Just (baseModule unit (ModuleName "Base.Int"))
        _ -> fail "no Core"

    it "has the interface and the bytecode of the source" do
      text <- liftEffect (readRepositoryFile baseIntPath)
      case (compiledSource initialEnvironment text).made, handWritten of
        Left why, _ -> fail why
        _, Left why -> fail why
        Right made, Right hand -> do
          hand.interface made.interface.arities `shouldEqual` Right made.interface
          encode hand.dmo `shouldEqual` encode made.dmo
