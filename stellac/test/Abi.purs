-- | A program whose `Base.IO` and `Base.Array` are written in source, built by
-- | `stellac build` and run by `steam run`, as processes.
-- |
-- | The package declares the two `Base` modules at the schemes the ABI declares
-- | their entries at, `Base.Array.Array` among them as a foreign type, beside
-- | `Console`, whose two foreigns the host implements. The foreign manifest
-- | names `Console` alone: an entry the runtime carries out has no host
-- | implementation to name. The cases run in order: the first builds the
-- | package.
module Test.Stellac.Abi (spec) where

import Prelude

import Data.Array as Array
import Data.String (Pattern(..), contains, split)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stellac.Process (Outcome, removeTree, steamRun, stellac, writeFiles)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "stellac/.test-integration/abi"

sources :: Array { path :: String, text :: String }
sources =
  [ { path: "src/Base/IO.stel"
    , text:
        """module Base.IO where

foreign pure :: forall a. a -> IO a
foreign bind :: forall a b. IO a -> (a -> IO b) -> IO b
"""
    }
  , { path: "src/Base/Array.stel"
    , text:
        """module Base.Array where

foreign type Array :: Type -> Type
foreign length :: forall a. Array a -> Int
foreign unsafeNew :: forall a. Int -> Array a
foreign unsafeSet :: forall a. Int -> a -> Array a -> Unit
foreign unsafeIndex :: forall a. Array a -> Int -> a
"""
    }
  , { path: "src/Console.stel"
    , text:
        """module Console where

foreign log :: String -> IO Unit
foreign logInt :: Int -> IO Unit
"""
    }
  , { path: "src/Main.stel"
    , text:
        """module Main where

import Base.IO (pure, bind)
import Base.Array (Array, length, unsafeNew, unsafeSet, unsafeIndex)
import Console (log, logInt)

words :: Array String
words = unsafeNew 2

main :: IO Unit
main = bind (pure (unsafeSet 0 "built" words)) (\_ -> bind (pure (unsafeSet 1 "from source" words)) (\_ -> bind (log (unsafeIndex words 1)) (\_ -> logInt (length words))))
"""
    }
  , { path: "host/console.mjs"
    , text:
        """export const log = (s) => () => { console.log(s); };
export const logInt = (n) => () => { console.log(String(n)); };
"""
    }
  , { path: "foreign.json"
    , text:
        """{ "formatVersion": 1, "target": "javascript", "modules": [
  { "module": "Console", "specifier": "./host/console.mjs",
    "foreigns": [ { "name": "log", "params": [ "string" ], "result": { "action": "unit" } },
                  { "name": "logInt", "params": [ "int" ], "result": { "action": "unit" } } ] } ] }
"""
    }
  ]

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
    writeFiles dir sources
    built <- stellac [ "--workdir", dir ]
    when (built.status /= 0) (fail ("the package did not build: " <> built.err))

  it "runs main, the runtime carrying out the `Base` entries the manifest does not name" do
    outcome <- steamRun { manifest: dir <> "/foreign.json", entry: "Main", modules: program [ "Base.IO", "Base.Array", "Console", "Main" ] }
    outcome.err `shouldEqual` ""
    outcome.status `shouldEqual` 0
    printed outcome `shouldEqual` [ "from source", "2" ]
