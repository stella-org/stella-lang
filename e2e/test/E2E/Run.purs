-- | A program of two packages built apart, run on Steam as processes.
-- |
-- | The library `lib` declares a host foreign, `Lib.Console.log`, and
-- | `Lib.Greet` writes ordinary code over it; it imports no `Base` module. It is
-- | built from source into `store`, and its sources removed. `App.Main`, whose
-- | `main` uses `Lib.Greet`, is built, its `dependencies` listing the files in
-- | `store`. The program is then run by `steam run`, given the descriptor made
-- | from what both builds wrote. The cases run in order: the first builds both
-- | packages.
module Test.E2E.Run (spec) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Either (Either(..))
import Data.String (Pattern(..), contains, split)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Fmt (fmt)
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Node.FS.Sync as Sync
import Stella.Compiler.ProgramDescriptor as ProgramDescriptor
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.E2E.Process (Outcome, compile, copyTree, removeTree, steamRun, writeFiles)
import Test.E2E.Program (programFrom)
import Test.E2E.StellaJson (listedAt, settings, stellaJson)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/run"

libModules :: Array String
libModules = [ "Lib.Console", "Lib.Greet" ]

-- | `stella.json` of each package.
configs :: Array { path :: String, text :: String }
configs =
  [ { path: "lib/stella.json", text: stellaJson ((settings (map listedAt [ "src/Lib/Console.stel", "src/Lib/Greet.stel" ])) { output = "../store", target = Just "javascript", foreigns = [ { module: "Lib.Console", specifier: "../host/console.mjs" } ] }) }
  , { path: "app/stella.json"
    , text: stellaJson ((settings [ listedAt "src/App/Main.stel" ]) { dependencies = map (\m -> { module: m, interface: fmt @"../store/{m}.dmi" { m }, object: fmt @"../store/{m}.dmo" { m } }) libModules })
    }
  ]

-- | The library built, its artifacts in `store` and its sources gone, and
-- | `App.Main` built against them.
setUp :: Aff Unit
setUp = do
  removeTree dir
  copyTree "fixtures/source/run" dir
  writeFiles dir configs
  lib <- compile (dir <> "/lib/stella.json")
  when (lib.status /= 0) (fail ("the library did not build: " <> lib.err))
  removeTree (dir <> "/lib")
  app <- compile (dir <> "/app/stella.json")
  when (app.status /= 0) (fail ("the application did not build: " <> app.err))

-- | The program's descriptor, from what both builds wrote.
program :: String
program = dir <> "/program.json"

-- | The lines a run printed, the development entry point's banner left out.
printed :: Outcome -> Array String
printed o = Array.filter (\l -> l /= "" && not (isBanner l)) (split (Pattern "\n") o.out)
  where
  isBanner = contains (Pattern "!!! This is development version of steam !!!")

spec :: Spec Unit
spec = describe "steam run, over packages built apart" do
  it "builds the library, keeps only its artifacts, and builds the application against them" do
    setUp
    kept <- liftEffect (Sync.exists (dir <> "/lib"))
    kept `shouldEqual` false

  it "runs the application's main, which calls the library's code and its host foreign" do
    written <- programFrom { outputs: [ dir <> "/store/output.json", dir <> "/app/output/output.json" ], entry: "App.Main", at: program }
    written `shouldEqual` Right unit
    outcome <- steamRun program
    outcome.err `shouldEqual` ""
    outcome.status `shouldEqual` 0
    printed outcome `shouldEqual` [ "glad to be built apart" ]

  it "is refused where the descriptor lists a module before one it imports, and runs nothing" do
    text <- FS.readTextFile UTF8 program
    case ProgramDescriptor.parse text of
      Left err -> fail (show err)
      Right d -> FS.writeTextFile UTF8 (dir <> "/reordered.json") (ProgramDescriptor.print d { modules = Array.reverse (Array.take 2 d.modules) <> Array.drop 2 d.modules })
    outcome <- steamRun (dir <> "/reordered.json")
    outcome.status `shouldEqual` 1
    printed outcome `shouldEqual` []
