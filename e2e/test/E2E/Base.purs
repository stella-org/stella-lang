-- | `Base.Int` built from its source of truth,
-- | `stella-packages/base/src/Base/Int.stel`, by `stella-devtools build-seeds`
-- | run as a process, and a program over it run by `steam run`.
-- |
-- | `App` is an ordinary package importing `Base.Int`, compiled against the
-- | seed module the compiler holds, beside `Console`, whose foreign the host
-- | implements; it runs over the bytecode `build-seeds` wrote. The cases run
-- | in order: the first builds `Base.Int`.
module Test.E2E.Base (spec) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.String (Pattern(..), contains, split)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.E2E.Process (Outcome, compile, copyTree, devtools, removeTree, steamRun, writeFiles)
import Test.E2E.Program (programFrom, statedSeeds)
import Test.E2E.StellaJson (listedAt, settings, stellaJson)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/base"

-- | The lines a run printed, the development entry point's banner left out.
printed :: Outcome -> Array String
printed o = Array.filter (\l -> l /= "" && not (isBanner l)) (split (Pattern "\n") o.out)
  where
  isBanner = contains (Pattern "!!! This is development version of steam !!!")

spec :: Spec Unit
spec = describe "`Base.Int` from its source" do
  it "builds `Base.Int` from `stella-packages/base/src/Base/Int.stel`, compiled anew" do
    removeTree dir
    built <- devtools [ "build-seeds", "--output", dir <> "/seeds" ]
    when (built.status /= 0) (fail ("`Base.Int` did not build: " <> built.err))

  it "runs a program over the bytecode it wrote, the package compiled against the seed `Base.Int`" do
    copyTree "fixtures/source/base" dir
    writeFiles dir [ { path: "app/stella.json", text: stellaJson ((settings (map listedAt [ "src/Console.stel", "src/Main.stel" ])) { target = Just "javascript", foreigns = [ { module: "Console", specifier: "./host/console.mjs" } ] }) } ]
    built <- compile (dir <> "/app/stella.json")
    when (built.status /= 0) (fail ("the program did not build: " <> built.err))
    stated <- statedSeeds (dir <> "/seeds") [ "Base.Int" ]
    stated `shouldEqual` Right unit
    written <- programFrom { outputs: [ dir <> "/seeds/output.json", dir <> "/app/output/output.json" ], entry: "Main", at: dir <> "/program.json" }
    written `shouldEqual` Right unit
    outcome <- steamRun (dir <> "/program.json")
    outcome.err `shouldEqual` ""
    outcome.status `shouldEqual` 0
    printed outcome `shouldEqual` [ "3" ]
