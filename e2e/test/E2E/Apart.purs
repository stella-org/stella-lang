-- | `stellac compile` of a package whose module calls a macro and names a
-- | synthesizer from a package built apart and listed in `dependencies`: files
-- | on disk, the session a process, and the result run on the machine.
-- |
-- | The library `lib` is built first, under `e2e/.test-build/apart/lib`:
-- | `Lib.Pass` writes a macro against `Stella.Syntax` and `Lib.Synth` a
-- | synthesizer against `Stella.Elab`, both importing `Lib.Support`. Then
-- | `Main` of `app`, with a macro call and a goal, is built with
-- | `dependencies` listing the three by the files the library's build wrote.
-- | The session refuses a module whose imports it has not loaded, and a second
-- | module of a name it holds, so the build succeeds only if `Lib.Support` is
-- | loaded once, before both modules that reach it.
module Test.E2E.Apart (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Traversable (for)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.CLI.Elaboration as Elaboration
import Steam.Foreign (emptyTable)
import Steam.Load (emptyStore, globalNamed, load, noIdentities)
import Steam.Value (Value(..))
import Stella.CLI.Effect.FS as FS
import Stella.Compiler.Bytecode (decode)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Test.E2E.StellaJson (Entry, compileAt, listedAt, settings, stellaJson)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.E2E.Process (copyTree, removeTree)
import Test.E2E.Synthesis (onDisk)

dir :: String
dir = "e2e/.test-build/apart"

libraryModules :: Array String
libraryModules = [ "Lib.Support", "Lib.Pass", "Lib.Synth" ]

-- | `stella.json` of a package, listing the files given and, as `dependencies`,
-- | the modules given.
configOf :: Array String -> Array Entry -> String
configOf paths dependencies = stellaJson ((settings (map listedAt paths)) { dependencies = dependencies })

-- | The library's modules, by the files its build wrote, from `app`.
libraryEntries :: Array Entry
libraryEntries = map (\m -> { module: m, interface: "../lib/output/" <> m <> ".dmi", object: "../lib/output/" <> m <> ".dmo" }) libraryModules

type Ran = { result :: Either String Unit, said :: Array String }

-- | The library built, then `app` against it.
building :: (Ran -> Aff Unit) -> Aff Unit
building k = do
  removeTree dir
  copyTree "fixtures/source/apart" dir
  said <- liftEffect (Ref.new [])
  result <- onDisk said do
    _ <- FS.writeText (dir <> "/lib/stella.json") (configOf [ "src/Lib/Support.stel", "src/Lib/Pass.stel", "src/Lib/Synth.stel" ] [])
    _ <- FS.writeText (dir <> "/app/stella.json") (configOf [ "src/Main.stel" ] libraryEntries)
    compileAt (dir <> "/lib/stella.json")
    compileAt (dir <> "/app/stella.json")
  lines <- liftEffect (Ref.read said)
  k { result, said: lines }

-- | The global of `Main` named, rendered once `Stella.Elab`, the modules the
-- | compiler carries, the library's modules, and `Main` are loaded.
valueOf :: String -> Aff String
valueOf global = do
  said <- liftEffect (Ref.new [])
  let paths = map (\m -> dir <> "/lib/output/" <> m <> ".dmo") libraryModules <> [ dir <> "/app/output/Main.dmo" ]
  read <- onDisk said (for paths FS.readBytes)
  case Elaboration.prepare, compiled, read of
    Left why, _, _ -> pure ("no Stella.Elab: " <> why)
    _, Left why, _ -> pure ("no carried modules: " <> why)
    _, _, Left why -> pure why
    Right elab, Right carried, Right files -> case for files (\f -> f >>= \bytes -> either' (decode bytes)) of
      Left why -> pure why
      Right dmos -> liftEffect do
        identities <- Ref.new noIdentities
        stored <- runBaseEffect (Except.runExcept (Array.foldM load (emptyStore emptyTable identities) ([ elab.dmo ] <> carried.modules <> dmos)))
        case stored of
          Left err -> pure ("load: " <> show err)
          Right store -> case globalNamed store (Qualified (ModuleName "Main") (Ident global)) of
            Nothing -> pure "absent"
            Just slot -> Ref.read slot <#> case _ of
              Just (VInt v) -> show v
              Just _ -> "not an Int"
              Nothing -> "uninitialized"
  where
  either' = case _ of
    Left err -> Left (show err)
    Right dmo -> Right dmo

spec :: Spec Unit
spec = describe "stellac compile of a package calling a macro and naming a synthesizer of a package built apart" do
  it "loads the modules `dependencies` lists from the bytecode it names, each after those it imports and once, and the program runs on the machine" do
    building \r -> do
      r.result `shouldEqual` Right unit
      Array.filter (\l -> l == "[1/1] Compiling Main (" <> dir <> "/app/src/Main.stel)") r.said `shouldEqual` [ "[1/1] Compiling Main (" <> dir <> "/app/src/Main.stel)" ]
      n <- valueOf "n"
      m <- valueOf "m"
      [ n, m ] `shouldEqual` [ "2", "7" ]
