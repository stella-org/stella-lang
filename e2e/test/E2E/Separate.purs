-- | A package built from the artifacts of another, by `stellac compile` run as
-- | a process.
-- |
-- | The library `lib`, of `Lib.Core` and `Lib.Extra` importing it, is built from
-- | source once; its `.dmo` and `.dmi` files are copied to `store` and its
-- | sources removed. Each case then builds `App.Main`, which imports `Lib.Extra`
-- | alone and uses a type `Lib.Core` declares, its `dependencies` listing the
-- | files in `store`. The cases run in order: the first builds the library,
-- | and the third compares what it builds with what the second built.
module Test.E2E.Separate (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.String (Pattern(..), contains)
import Data.Traversable (for_)
import Fmt (fmt)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Node.FS.Sync as Sync
import Stella.Compiler.Bytecode (decode)
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.TypedCore (ModuleName(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.E2E.Process (Outcome, compile, copyArtifacts, copyTree, removeTree, writeFiles)
import Test.E2E.StellaJson (Settings, listedAt, settings, stellaJson)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/separate"

libModules :: Array String
libModules = [ "Lib.Core", "Lib.Extra" ]

-- | `stella.json` of `app`, building to the output directory given, its
-- | `dependencies` listing the modules given, each by its files in `store`.
configOf :: String -> Array String -> String
configOf output modules = stellaJson (appSettings output modules)

appSettings :: String -> Array String -> Settings
appSettings output modules = (settings [ listedAt "src/App/Main.stel" ]) { output = output, dependencies = map entry modules }
  where
  entry m = { module: m, interface: fmt @"../store/{m}.dmi" { m }, object: fmt @"../store/{m}.dmo" { m } }

-- | The library built, its artifacts in `store`, and its sources gone.
setUp :: Aff Unit
setUp = do
  removeTree dir
  copyTree "fixtures/source/separate" dir
  writeFiles dir [ { path: "lib/stella.json", text: stellaJson (settings (map listedAt [ "src/Lib/Core.stel", "src/Lib/Extra.stel" ])) } ]
  lib <- compile (dir <> "/lib/stella.json")
  when (lib.status /= 0) (fail ("the library did not build: " <> lib.err))
  copyArtifacts { from: dir <> "/lib/output", to: dir <> "/store", modules: libModules }
  removeTree (dir <> "/lib")

bytesOf :: String -> Aff Bytes
bytesOf path = FS.readFile path >>= liftEffect <<< Buffer.toArray

-- | `App.Main` built by the `stella.json` written as the file given in `app`,
-- | to the output directory given, against the modules given.
buildApp :: String -> String -> Array String -> Aff Outcome
buildApp file output modules = do
  FS.writeTextFile UTF8 (fmt @"{dir}/app/{file}" { dir, file }) (configOf output modules)
  compile (fmt @"{dir}/app/{file}" { dir, file })

builtPath :: String -> String -> String
builtPath output ext = fmt @"{dir}/app/{output}/App.Main.{ext}" { dir, output, ext }

spec :: Spec Unit
spec = describe "stellac compile against `dependencies`" do
  it "builds the library from source, and keeps only its artifacts" do
    setUp
    kept <- liftEffect (Sync.exists (dir <> "/lib"))
    kept `shouldEqual` false

  it "builds a package from the interfaces of another, whose sources it cannot reach" do
    outcome <- buildApp "in-order.json" "out-in-order" libModules
    outcome.status `shouldEqual` 0
    dmi <- bytesOf (builtPath "out-in-order" "dmi")
    case Interface.decode dmi of
      Left err -> fail (show err)
      Right stored -> do
        stored.interface.name `shouldEqual` ModuleName "App.Main"
        stored.interface.imports `shouldEqual` [ ModuleName "Lib.Extra" ]
    dmo <- bytesOf (builtPath "out-in-order" "dmo")
    case decode dmo of
      Left err -> fail (show err)
      Right m -> do
        m.name `shouldEqual` ModuleName "App.Main"
        m.imports `shouldEqual` [ ModuleName "Lib.Extra" ]

  it "builds the same files whatever order `dependencies` lists the modules in" do
    reversed <- buildApp "reversed.json" "out-reversed" (Array.reverse libModules)
    reversed.status `shouldEqual` 0
    for_ [ "dmo", "dmi" ] \ext -> do
      a <- bytesOf (builtPath "out-in-order" ext)
      b <- bytesOf (builtPath "out-reversed" ext)
      a `shouldEqual` b

  it "fails, naming the import, where `dependencies` leaves out a module an interface imports" do
    outcome <- buildApp "partial.json" "out-partial" [ "Lib.Extra" ]
    outcome.status `shouldEqual` 1
    contains (Pattern "The interface of `Lib.Extra` imports `Lib.Core`, which `dependencies` does not list") outcome.err
      `shouldEqual` true
    written <- liftEffect (Sync.exists (builtPath "out-partial" "dmo"))
    written `shouldEqual` false

  it "says no progress at `logLevel` `error`, and colours what it says only where `monochrome` is not set" do
    FS.writeTextFile UTF8 (dir <> "/app/quiet.json") (stellaJson ((appSettings "out-quiet" libModules) { logLevel = "error" }))
    quiet <- compile (dir <> "/app/quiet.json")
    quiet.status `shouldEqual` 0
    contains (Pattern "Compiling") (quiet.out <> quiet.err) `shouldEqual` false
    FS.writeTextFile UTF8 (dir <> "/app/colour.json") (stellaJson ((appSettings "out-colour" [ "Lib.Extra" ]) { logLevel = "debug", monochrome = false }))
    coloured <- compile (dir <> "/app/colour.json")
    FS.writeTextFile UTF8 (dir <> "/app/plain.json") (stellaJson ((appSettings "out-plain" [ "Lib.Extra" ]) { logLevel = "debug" }))
    plain <- compile (dir <> "/app/plain.json")
    map _.status [ coloured, plain ] `shouldEqual` [ 1, 1 ]
    map (contains (Pattern "\x1b[") <<< _.err) [ coloured, plain ] `shouldEqual` [ true, false ]
