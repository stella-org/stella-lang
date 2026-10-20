-- | `Slow` and `Loud`, modules of one host foreign each, called as the module
-- | initializes, built from `fixtures/source/common-lib/slow-loud`; and the host
-- | modules and the foreign manifest that supply them. `slow.mjs` takes a while to
-- | reach, writing `slow reached` and then `slow ready`; `loud.mjs` writes
-- | `shouted` when it is called, which is what shows `Loud` was initialized.
module Test.E2E.SlowLoud (slowLoud, writeSlowLoud) where

import Prelude

import Data.Either (Either(..))
import Data.Foldable (for_)
import E2E.Build (Sources, builtFrom)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Stella.Compiler.Bytecode (Dmo, encode)
import Stella.Compiler.TypedCore (ModuleName(..))
import Test.Spec.Assertions (fail)

slowLoud :: Sources -> Either String (Array Dmo)
slowLoud sources = builtFrom sources [ "common-lib/slow-loud" ]

-- | The modules given, the host modules, and the manifest `slow-loud.json`,
-- | written into the directory given.
writeSlowLoud :: String -> Array Dmo -> Aff Unit
writeSlowLoud dir modules = do
  for_ modules \dmo -> case dmo.name, encode dmo of
    ModuleName name, Right bytes -> do
      buffer <- liftEffect (Buffer.fromArray bytes)
      FS.writeFile (dir <> "/" <> name <> ".dmo") buffer
    ModuleName name, Left err -> fail ("could not encode " <> name <> ": " <> show err)
  writeText (dir <> "/slow.mjs")
    """process.stderr.write("slow reached\n");
       await new Promise((resolve) => setTimeout(resolve, 800));
       process.stderr.write("slow ready\n");
       export const wait = (n) => { process.stderr.write("waited\n"); return n; };
    """
  writeText (dir <> "/loud.mjs")
    """export const shout = (n) => { process.stderr.write("shouted\n"); return n; };
    """
  writeText (dir <> "/slow-loud.json")
    """{ "formatVersion": 1, "target": "javascript",
         "modules": [ { "module": "Loud", "specifier": "./loud.mjs",
                        "foreigns": [ { "name": "shout", "params": [ "int" ], "result": "int" } ] },
                      { "module": "Slow", "specifier": "./slow.mjs",
                        "foreigns": [ { "name": "wait", "params": [ "int" ], "result": "int" } ] } ] }"""
  where
  writeText path content = do
    buffer <- liftEffect (Buffer.fromString content UTF8)
    FS.writeFile path buffer
