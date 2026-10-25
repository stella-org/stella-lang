-- | A program of two packages built apart, run on Steam as processes.
-- |
-- | The library `lib` declares a host foreign, `Lib.Console.log`, and
-- | `Lib.Greet` writes ordinary code over it; it imports no `Base` module. It is
-- | built from source, its artifacts copied to `store`, and its sources removed.
-- | `App.Main`, whose `main` uses `Lib.Greet`, is built, its `dependencies`
-- | listing the files in `store`. The program is then run by `steam run`, given
-- | a foreign manifest and a JavaScript implementation written here, and the
-- | bytecode of each module in the order the case states, the library's taken
-- | from `store`. The cases run in order: the first builds both packages.
module Test.E2E.Run (spec) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.String (Pattern(..), contains, split)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Fmt (fmt)
import Node.FS.Sync as Sync
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.E2E.Process (Outcome, compile, copyArtifacts, copyTree, removeTree, steamRun, writeFiles)
import Test.E2E.StellaJson (listedAt, settings, stellaJson)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/run"

libModules :: Array String
libModules = [ "Lib.Console", "Lib.Greet" ]

-- | `stella.json` of each package.
configs :: Array { path :: String, text :: String }
configs =
  [ { path: "lib/stella.json", text: stellaJson ((settings (map listedAt [ "src/Lib/Console.stel", "src/Lib/Greet.stel" ])) { target = Just "javascript", foreigns = [ { module: "Lib.Console", specifier: "../host/console.mjs" } ] }) }
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
  copyArtifacts { from: dir <> "/lib/output", to: dir <> "/store", modules: libModules }
  removeTree (dir <> "/lib")
  app <- compile (dir <> "/app/stella.json")
  when (app.status /= 0) (fail ("the application did not build: " <> app.err))

-- | The bytecode of each module named, in the order named: a module of the
-- | library from `store`, and `App.Main` from where its build wrote it.
programIn :: Array String -> Array String
programIn = map \m ->
  if m == "App.Main" then dir <> "/app/output/App.Main.dmo" else fmt @"{dir}/store/{m}.dmo" { dir, m }

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
    outcome <- steamRun { manifest: dir <> "/foreign.json", entry: "App.Main", modules: programIn [ "Lib.Console", "Lib.Greet", "App.Main" ] }
    outcome.err `shouldEqual` ""
    outcome.status `shouldEqual` 0
    printed outcome `shouldEqual` [ "glad to be built apart" ]

  it "is refused where the bytecode is not given in dependency order, and runs nothing" do
    outcome <- steamRun { manifest: dir <> "/foreign.json", entry: "App.Main", modules: programIn [ "Lib.Greet", "Lib.Console", "App.Main" ] }
    outcome.status `shouldEqual` 1
    printed outcome `shouldEqual` []
