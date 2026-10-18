-- | A package built from the artifacts of another, by `stellac build` run as a
-- | process.
-- |
-- | The library `lib`, of `Lib.Core` and `Lib.Extra` importing it, is built from
-- | source once; its `.dmo` and `.dmi` files are copied to `store` and its
-- | sources removed. Each case then builds `App.Main`, which imports `Lib.Extra`
-- | alone and uses a type `Lib.Core` declares, through a dependency map listing
-- | the files in `store`. The cases run in order: the first builds the library,
-- | and the third compares what it builds with what the second built.
module Test.Stellac.Separate (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (maybe)
import Data.String (Pattern(..), contains)
import Data.String as String
import Data.Traversable (for_)
import Fmt (DefaultConfig, SetOpenClose, fmt, fmtWith)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.ChildProcess.Types (Exit(..))
import Node.FS.Aff as FS
import Node.FS.Perms as Perms
import Node.FS.Sync as Sync
import Node.Library.Execa (execa)
import Stella.Compiler.Bytecode (decode)
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.TypedCore (ModuleName(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "stellac/.test-integration"

sources :: Array { path :: String, text :: String }
sources =
  [ { path: "lib/src/Lib/Core.stel"
    , text:
        """module Lib.Core where

import Base.Int (add)

data Pair = Pair Int Int

double :: Int -> Int
double n = add n n
"""
    }
  , { path: "lib/src/Lib/Extra.stel"
    , text:
        """module Lib.Extra where

import Lib.Core

origin :: Pair
origin = Pair 1 (double 2)

swap :: Pair -> Pair
swap p = case p of
  Pair a b -> Pair b a

twice :: Int -> Int
twice n = double n
"""
    }
  , { path: "app/src/App/Main.stel"
    , text:
        """module App.Main where

import Lib.Extra

flipped = swap origin

four :: Int
four = twice 2
"""
    }
  ]

libModules :: Array String
libModules = [ "Lib.Core", "Lib.Extra" ]

-- | A map listing the modules given, each by its files in `store`.
mapOf :: Array String -> String
mapOf modules = fmtWith @(SetOpenClose "<" ">" DefaultConfig) @"""{ "formatVersion": 0, "modules": [ <entries> ] }""" { entries: Array.intercalate ", " (map entry modules) }
  where
  entry m = fmtWith @(SetOpenClose "<" ">" DefaultConfig) @"""{ "module": "<m>", "interface": "store/<m>.dmi", "object": "store/<m>.dmo" }""" { m }

type Outcome = { status :: Int, err :: String }

stellac :: Array String -> Aff Outcome
stellac args = do
  result <- execa "node" ([ "stellac/index.dev.js", "build" ] <> args) identity >>= _.getResult
  pure
    { status: case result.exit of
        Normally code -> code
        BySignal _ -> -1
    , err: result.stderr
    }

-- | The library built, its artifacts in `store`, and its sources gone.
setUp :: Aff Unit
setUp = do
  FS.rm' dir { force: true, maxRetries: 0, recursive: true, retryDelay: 0 }
  for_ sources \s -> do
    let path = fmt @"{dir}/{path}" { dir, path: s.path }
    FS.mkdir' (parentOf path) { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
    FS.writeTextFile UTF8 path s.text
  lib <- stellac [ "--workdir", dir <> "/lib" ]
  when (lib.status /= 0) (fail ("the library did not build: " <> lib.err))
  FS.mkdir' (dir <> "/store") { recursive: true, mode: Perms.mkPerms Perms.all Perms.all Perms.all }
  for_ libModules \m -> for_ [ "dmo", "dmi" ] \ext ->
    FS.copyFile (fmt @"{dir}/lib/output/_build/{m}.{ext}" { dir, m, ext }) (fmt @"{dir}/store/{m}.{ext}" { dir, m, ext })
  FS.rm' (dir <> "/lib") { force: false, maxRetries: 0, recursive: true, retryDelay: 0 }
  where
  parentOf path = maybe path (\i -> String.take i path) (String.lastIndexOf (Pattern "/") path)

bytesOf :: String -> Aff Bytes
bytesOf path = FS.readFile path >>= liftEffect <<< Buffer.toArray

-- | `App.Main` built through the map written as the file given, to the output
-- | directory given, both under the suite's directory.
buildApp :: String -> String -> Array String -> Aff Outcome
buildApp mapFile output modules = do
  FS.writeTextFile UTF8 (fmt @"{dir}/{mapFile}" { dir, mapFile }) (mapOf modules)
  stellac [ "--workdir", dir <> "/app", "--output", output, "--dependencies", "../" <> mapFile ]

builtPath :: String -> String -> String
builtPath output ext = fmt @"{dir}/app/{output}/_build/App.Main.{ext}" { dir, output, ext }

spec :: Spec Unit
spec = describe "stellac build --dependencies" do
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

  it "builds the same files whatever order the map lists the modules in" do
    reversed <- buildApp "reversed.json" "out-reversed" (Array.reverse libModules)
    reversed.status `shouldEqual` 0
    for_ [ "dmo", "dmi" ] \ext -> do
      a <- bytesOf (builtPath "out-in-order" ext)
      b <- bytesOf (builtPath "out-reversed" ext)
      a `shouldEqual` b

  it "fails, naming the import, where the map leaves out a module an interface imports" do
    outcome <- buildApp "partial.json" "out-partial" [ "Lib.Extra" ]
    outcome.status `shouldEqual` 1
    contains (Pattern "The interface of `Lib.Extra` imports `Lib.Core`, which the dependency map does not list") outcome.err
      `shouldEqual` true
    written <- liftEffect (Sync.exists (builtPath "out-partial" "dmo"))
    written `shouldEqual` false
