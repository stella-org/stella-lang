-- | The modules of `stella-packages/compiler-lib` built from their sources of
-- | truth, `Stella.Syntax` and `Stella.Elab`, by `stellac build` run as a
-- | process.
-- |
-- | The sources are copied as they stand into a package of their own, which
-- | compiles both modules the compiler carries anew, `Stella.Syntax` against
-- | the `Base.Int` the compiler carries; the files it writes are the
-- | compiler's modules to the byte. The cases run in order: the first builds
-- | the package.
module Test.Stellac.CompilerLib (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (for)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Stella.Compiler.Bytecode (encode)
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.TypedCore (ModuleName(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stellac.Process (removeTree, stellac, writeFiles)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "stellac/.test-integration/compiler-lib"

-- | The file of the module given the package wrote, of the extension given.
built :: String -> String -> String
built m ext = dir <> "/output/_build/" <> m <> "." <> ext

bytesOf :: String -> Aff Bytes
bytesOf path = FS.readFile path >>= liftEffect <<< Buffer.toArray

spec :: Spec Unit
spec = describe "`Stella.Syntax` and `Stella.Elab` from their sources" do
  it "builds both from `stella-packages/compiler-lib`, compiled anew" do
    removeTree dir
    sources <- for [ "Stella/Syntax.stel", "Stella/Elab.stel" ] \path -> do
      text <- FS.readTextFile UTF8 ("stella-packages/compiler-lib/src/" <> path)
      pure { path: "src/" <> path, text }
    writeFiles dir sources
    outcome <- stellac [ "--workdir", dir, "--toolchain-rebuild", "Stella.Syntax", "--toolchain-rebuild", "Stella.Elab" ]
    when (outcome.status /= 0) (fail ("the package did not build: " <> outcome.err))

  it "writes the interfaces and the bytecode of the modules the compiler carries" do
    case compiled of
      Left why -> fail why
      Right carried -> for_ [ "Stella.Syntax", "Stella.Elab" ] \m -> do
        dmi <- bytesOf (built m "dmi")
        dmo <- bytesOf (built m "dmo")
        case Interface.decode dmi of
          Left err -> fail (show err)
          Right stored -> Just stored.interface `shouldEqual` Map.lookup (ModuleName m) carried.preloaded
        let
          bytecode = case m of
            "Stella.Elab" -> Just carried.elaboration.dmo
            _ -> Array.find (\d -> d.name == ModuleName m) carried.modules
        map encode bytecode `shouldEqual` Just (Right dmo)
