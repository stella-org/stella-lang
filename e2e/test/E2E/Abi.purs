-- | A program whose `Base.IO` and `Base.Array` are written in source, built by
-- | `stellac compile` and run by `steam run`, as processes.
-- |
-- | The package declares the two `Base` modules at the schemes the ABI declares
-- | their entries at, `Base.Array.Array` among them as a foreign type, beside
-- | `Console`, whose two foreigns the host implements. The foreign manifest
-- | names `Console` alone: an entry the runtime carries out has no host
-- | implementation to name, and what the build states of its host foreigns
-- | is the manifest's entry. The cases run in order: the first builds the
-- | package.
module Test.E2E.Abi (spec) where

import Prelude

import Data.Argonaut.Core (toObject)
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..), hush, note)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Foreign.Object as Object
import Stella.Compiler.ForeignManifest (parse, readBody)
import Stella.Compiler.TypedCore (ModuleName(..))
import Stellac.Output as Output
import Data.String (Pattern(..), contains, split)
import Data.Traversable (for_)
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.E2E.Process (Outcome, compile, copyTree, removeTree, steamRun, writeFiles)
import Test.E2E.StellaJson (listedAt, settings, stellaJson)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/abi"

-- | The bytecode of each module named, in the order named.
program :: Array String -> Array String
program = map \m -> dir <> "/output/" <> m <> ".dmo"

-- | The lines a run printed, the development entry point's banner left out.
printed :: Outcome -> Array String
printed o = Array.filter (\l -> l /= "" && not (isBanner l)) (split (Pattern "\n") o.out)
  where
  isBanner = contains (Pattern "!!! This is development version of steam !!!")

spec :: Spec Unit
spec = describe "steam run, over `Base` modules written in source" do
  it "builds the package, its `Base` modules among it" do
    removeTree dir
    copyTree "fixtures/source/abi" dir
    -- the `Base` modules the package compiles, as `stella-packages/base` writes them
    for_ [ "IO", "Array" ] \m -> do
      text <- FS.readTextFile UTF8 ("stella-packages/base/src/Base/" <> m <> ".stel")
      writeFiles dir [ { path: "src/Base/" <> m <> ".stel", text } ]
    writeFiles dir [ { path: "stella.json", text: stellaJson ((settings (map listedAt [ "src/Base/IO.stel", "src/Base/Array.stel", "src/Console.stel", "src/Main.stel" ])) { target = Just "javascript", foreigns = [ { module: "Console", specifier: "./host/console.mjs" } ] }) } ]
    built <- compile (dir <> "/stella.json")
    when (built.status /= 0) (fail ("the package did not build: " <> built.err))

  it "states the host foreigns as the manifest written by hand gives them, `Console` alone, its specifier from the output directory" do
    stated <- FS.readTextFile UTF8 (dir <> "/output/output.json")
    byHand <- FS.readTextFile UTF8 (dir <> "/foreign.json")
    let
      foreigns = map (map _.foreigns <<< _.entries)
      written = Output.decode stated
      body = note "no `foreign`" (Object.lookup "foreign" =<< toObject =<< hush (jsonParser stated))
    map (map (map (\f -> Tuple f.module f.specifier) <<< _.modules) <<< _.foreign) written `shouldEqual` Right (Just [ Tuple (ModuleName "Console") "../host/console.mjs" ])
    foreigns (body >>= lmap show <<< readBody "javascript") `shouldEqual` foreigns (lmap show (parse "javascript" byHand))

  it "runs main, the runtime carrying out the `Base` entries the manifest does not name" do
    outcome <- steamRun { manifest: dir <> "/foreign.json", entry: "Main", modules: program [ "Base.IO", "Base.Array", "Console", "Main" ] }
    outcome.err `shouldEqual` ""
    outcome.status `shouldEqual` 0
    printed outcome `shouldEqual` [ "from source", "2" ]
