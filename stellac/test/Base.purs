-- | `Base.Int` built from its source of truth,
-- | `stella-packages/base/src/Base/Int.stel`, by `stellac build` run as a
-- | process, and a program over it run by `steam run`.
-- |
-- | The source is copied as it stands into a package of its own, which compiles
-- | the module the compiler carries anew; the files it writes are the
-- | compiler's `Base.Int` to the byte. `App` is an ordinary package importing
-- | `Base.Int`, compiled against the one the compiler carries, beside `Console`,
-- | whose foreign the host implements; it runs over the bytecode the first
-- | package wrote. The cases run in order: the first builds `Base.Int`.
module Test.Stellac.Base (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, split)
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
import Test.Stellac.Process (Outcome, removeTree, steamRun, stellac, writeFiles)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "stellac/.test-integration/base"

app :: Array { path :: String, text :: String }
app =
  [ { path: "app/src/Console.stel"
    , text:
        """module Console where

foreign logInt :: Int -> IO Unit
"""
    }
  , { path: "app/src/Main.stel"
    , text:
        """module Main where

import Base.Int (add)
import Console (logInt)

main :: IO Unit
main = logInt (add 1 2)
"""
    }
  , { path: "app/host/console.mjs"
    , text:
        """export const logInt = (n) => () => { console.log(String(n)); };
"""
    }
  , { path: "app/foreign.json"
    , text:
        """{ "formatVersion": 1, "target": "javascript", "modules": [
  { "module": "Console", "specifier": "./host/console.mjs",
    "foreigns": [ { "name": "logInt", "params": [ "int" ], "result": { "action": "unit" } } ] } ] }
"""
    }
  ]

-- | The file the package compiling `Base.Int` wrote, of the extension given.
baseFile :: String -> String
baseFile ext = dir <> "/base/output/_build/Base.Int." <> ext

bytesOf :: String -> Aff Bytes
bytesOf path = FS.readFile path >>= liftEffect <<< Buffer.toArray

-- | The lines a run printed, the development entry point's banner left out.
printed :: Outcome -> Array String
printed o = Array.filter (\l -> l /= "" && not (isBanner l)) (split (Pattern "\n") o.out)
  where
  isBanner = contains (Pattern "!!! This is development version of steam !!!")

spec :: Spec Unit
spec = describe "`Base.Int` from its source" do
  it "builds `Base.Int` from `stella-packages/base/src/Base/Int.stel`, compiled anew" do
    removeTree dir
    source <- FS.readTextFile UTF8 "stella-packages/base/src/Base/Int.stel"
    writeFiles dir [ { path: "base/src/Base/Int.stel", text: source } ]
    built <- stellac [ "--workdir", dir <> "/base", "--toolchain-rebuild", "Base.Int" ]
    when (built.status /= 0) (fail ("`Base.Int` did not build: " <> built.err))

  it "writes the interface and the bytecode of the `Base.Int` the compiler carries" do
    dmi <- bytesOf (baseFile "dmi")
    dmo <- bytesOf (baseFile "dmo")
    case compiled, Interface.decode dmi of
      Left why, _ -> fail why
      _, Left err -> fail (show err)
      Right carried, Right stored -> do
        Just stored.interface `shouldEqual` Map.lookup (ModuleName "Base.Int") carried.preloaded
        map encode (Array.head carried.modules) `shouldEqual` Just (Right dmo)

  it "runs a program over the bytecode it wrote, the package compiled against the `Base.Int` the compiler carries" do
    writeFiles dir app
    built <- stellac [ "--workdir", dir <> "/app" ]
    when (built.status /= 0) (fail ("the program did not build: " <> built.err))
    outcome <- steamRun
      { manifest: dir <> "/app/foreign.json"
      , entry: "Main"
      , modules: [ baseFile "dmo", dir <> "/app/output/_build/Console.dmo", dir <> "/app/output/_build/Main.dmo" ]
      }
    outcome.err `shouldEqual` ""
    outcome.status `shouldEqual` 0
    printed outcome `shouldEqual` [ "3" ]
