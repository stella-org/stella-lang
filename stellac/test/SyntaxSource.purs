-- | `Stella.Syntax` built from its source of truth,
-- | `stella-packages/compiler-lib/src/Stella/Syntax.stel`, by `stellac build`
-- | run as a process.
-- |
-- | The source is copied as it stands into a package of its own, which compiles
-- | the module the compiler carries anew against the `Base.Int` the compiler
-- | carries; the files it writes are the compiler's `Stella.Syntax` to the
-- | byte. The cases run in order: the first builds the package.
module Test.Stellac.SyntaxSource (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
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
dir = "stellac/.test-integration/syntax"

-- | The file the package wrote, of the extension given.
syntaxFile :: String -> String
syntaxFile ext = dir <> "/output/_build/Stella.Syntax." <> ext

bytesOf :: String -> Aff Bytes
bytesOf path = FS.readFile path >>= liftEffect <<< Buffer.toArray

spec :: Spec Unit
spec = describe "`Stella.Syntax` from its source" do
  it "builds `Stella.Syntax` from `stella-packages/compiler-lib/src/Stella/Syntax.stel`, compiled anew" do
    removeTree dir
    source <- FS.readTextFile UTF8 "stella-packages/compiler-lib/src/Stella/Syntax.stel"
    writeFiles dir [ { path: "src/Stella/Syntax.stel", text: source } ]
    built <- stellac [ "--workdir", dir, "--toolchain-rebuild", "Stella.Syntax" ]
    when (built.status /= 0) (fail ("`Stella.Syntax` did not build: " <> built.err))

  it "writes the interface and the bytecode of the `Stella.Syntax` the compiler carries" do
    dmi <- bytesOf (syntaxFile "dmi")
    dmo <- bytesOf (syntaxFile "dmo")
    case compiled, Interface.decode dmi of
      Left why, _ -> fail why
      _, Left err -> fail (show err)
      Right carried, Right stored -> do
        Just stored.interface `shouldEqual` Map.lookup (ModuleName "Stella.Syntax") carried.preloaded
        map encode (Array.find (\m -> m.name == ModuleName "Stella.Syntax") carried.modules) `shouldEqual` Just (Right dmo)
