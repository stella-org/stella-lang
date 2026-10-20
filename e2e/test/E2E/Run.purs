-- | A program of two packages built apart, run on Steam as processes.
-- |
-- | The library `lib` declares a host foreign, `Lib.Console.log`, and
-- | `Lib.Greet` writes ordinary code over it; it imports no `Base` module. It is
-- | built from source, its artifacts copied to `store`, and its sources removed.
-- | `App.Main`, whose `main` uses `Lib.Greet`, is built through a dependency map
-- | listing the files in `store`. The program is then run by `steam run`, given
-- | a foreign manifest and a JavaScript implementation written here, and the
-- | bytecode of each module in the order the case states, the library's taken
-- | from the map. The cases run in order: the first builds both packages.
module Test.E2E.Run (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, split)
import Data.Traversable (traverse)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Fmt (DefaultConfig, SetOpenClose, fmt, fmtWith)
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Node.FS.Sync as Sync
import Stella.Compiler.TypedCore (ModuleName(..))
import Stellac.Dependencies (parse)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.E2E.Process (Outcome, copyArtifacts, removeTree, copyTree, steamRun, stellac)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/run"

libModules :: Array String
libModules = [ "Lib.Console", "Lib.Greet" ]

mapPath :: String
mapPath = dir <> "/deps.json"

mapText :: String
mapText = fmtWith @(SetOpenClose "<" ">" DefaultConfig) @"""{ "formatVersion": 0, "modules": [ <entries> ] }""" { entries: Array.intercalate ", " (map entry libModules) }
  where
  entry m = fmtWith @(SetOpenClose "<" ">" DefaultConfig) @"""{ "module": "<m>", "interface": "store/<m>.dmi", "object": "store/<m>.dmo" }""" { m }

-- | The library built, its artifacts in `store` and its sources gone, and
-- | `App.Main` built through the map.
setUp :: Aff Unit
setUp = do
  removeTree dir
  copyTree "fixtures/source/run" dir
  lib <- stellac [ "--workdir", dir <> "/lib" ]
  when (lib.status /= 0) (fail ("the library did not build: " <> lib.err))
  copyArtifacts { from: dir <> "/lib/output/_build", to: dir <> "/store", modules: libModules }
  removeTree (dir <> "/lib")
  FS.writeTextFile UTF8 mapPath mapText
  app <- stellac [ "--workdir", dir <> "/app", "--dependencies", "../deps.json" ]
  when (app.status /= 0) (fail ("the application did not build: " <> app.err))

-- | The bytecode of each module named, in the order named: a module the map
-- | lists by the path its entry gives, resolved against the directory of the
-- | map, and `App.Main` by where its build wrote it.
programIn :: Array String -> Aff (Array String)
programIn order = do
  text <- FS.readTextFile UTF8 mapPath
  case parse mapPath text of
    Left err -> fail (show err) $> []
    Right entries -> case traverse (pathOf entries) order of
      Just paths -> pure paths
      Nothing -> fail "a module named is in neither package" $> []
  where
  pathOf entries m
    | m == "App.Main" = Just (dir <> "/app/output/_build/App.Main.dmo")
    | otherwise = Array.find (\e -> e.module == ModuleName m) entries <#> \e -> fmt @"{dir}/{object}" { dir, object: e.object }

-- | The lines a run printed, the development entry point's banner left out.
printed :: Outcome -> Array String
printed o = Array.filter (\l -> l /= "" && not (isBanner l)) (split (Pattern "\n") o.out)
  where
  isBanner = contains (Pattern "!!! This is development version of steam !!!")

spec :: Spec Unit
spec = describe "steam run, over packages built apart" do
  it "builds the library, keeps only its artifacts, and builds the application through the map" do
    setUp
    kept <- liftEffect (Sync.exists (dir <> "/lib"))
    kept `shouldEqual` false

  it "runs the application's main, which calls the library's code and its host foreign" do
    modules <- programIn [ "Lib.Console", "Lib.Greet", "App.Main" ]
    outcome <- steamRun { manifest: dir <> "/foreign.json", entry: "App.Main", modules }
    outcome.err `shouldEqual` ""
    outcome.status `shouldEqual` 0
    printed outcome `shouldEqual` [ "glad to be built apart" ]

  it "is refused where the bytecode is not given in dependency order, and runs nothing" do
    modules <- programIn [ "Lib.Greet", "Lib.Console", "App.Main" ]
    outcome <- steamRun { manifest: dir <> "/foreign.json", entry: "App.Main", modules }
    outcome.status `shouldEqual` 1
    printed outcome `shouldEqual` []
