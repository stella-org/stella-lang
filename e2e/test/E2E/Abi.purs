-- | A program whose `Base.IO` and `Base.Array` are written in source, built by
-- | `stellac build` and run by `steam run`, as processes.
-- |
-- | The package declares the two `Base` modules at the schemes the ABI declares
-- | their entries at, `Base.Array.Array` among them as a foreign type, beside
-- | `Console`, whose two foreigns the host implements. The foreign manifest
-- | names `Console` alone: an entry the runtime carries out has no host
-- | implementation to name. The cases run in order: the first builds the
-- | package.
module Test.E2E.Abi (spec) where

import Prelude

import Data.Array as Array
import Data.String (Pattern(..), contains, split)
import Data.Traversable (for_)
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.E2E.Process (Outcome, copyTree, removeTree, steamRun, stellac, writeFiles)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/abi"

-- | The bytecode of each module named, in the order named.
program :: Array String -> Array String
program = map \m -> dir <> "/output/_build/" <> m <> ".dmo"

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
    built <- stellac [ "--workdir", dir ]
    when (built.status /= 0) (fail ("the package did not build: " <> built.err))

  it "runs main, the runtime carrying out the `Base` entries the manifest does not name" do
    outcome <- steamRun { manifest: dir <> "/foreign.json", entry: "Main", modules: program [ "Base.IO", "Base.Array", "Console", "Main" ] }
    outcome.err `shouldEqual` ""
    outcome.status `shouldEqual` 0
    printed outcome `shouldEqual` [ "from source", "2" ]
