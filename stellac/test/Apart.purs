-- | `stellac build --dependencies` of a package whose module calls a macro and
-- | names a synthesizer of a package built apart: the files on disk, the
-- | session a process, and the modules built then run on the machine.
-- |
-- | The library `lib` is built first, under `stellac/.test-build/apart/lib`:
-- | `Lib.Pass` writes a macro against `Stella.Syntax`, `Lib.Synth` a
-- | synthesizer against `Stella.Elab`, and both import `Lib.Support`. The map
-- | `deps.json` lists the three by the files that build wrote. `Main` of the
-- | package `app` is then built through the map, a macro call and a goal in
-- | it. The session refuses a module whose imports it has not loaded, and a
-- | second module of a name it holds, so the build succeeds only where
-- | `Lib.Support` is loaded before both modules reaching it, and once.
module Test.Stellac.Apart (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
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
import Stella.CLI.Effect.Log (LogLevel(..))
import Stella.Compiler.Bytecode (decode)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..))
import Stellac.Options (BuildOptions, Command(..))
import Stellac.Program (program)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Stellac.Synthesis (onDisk)

dir :: String
dir = "stellac/.test-build/apart"

library :: Array (Tuple String (Array String))
library =
  [ Tuple "src/Lib/Support.stel" [ "module Lib.Support where", "seed :: Int", "seed = 7" ]
  , Tuple "src/Lib/Pass.stel"
      [ "module Lib.Pass where"
      , "import Lib.Support"
      , "import Stella.Syntax (List, Parser, Syntax(..), Term, TokenTree, brackets, many, map, nodesOf, tree)"
      , "k :: Int"
      , "k = seed"
      , "asSyntax :: List TokenTree -> Syntax Term"
      , "asSyntax ts = Syntax (nodesOf ts)"
      , "@[macro]"
      , "pass :: Parser (Syntax Term)"
      , "pass = brackets (map asSyntax (many tree))"
      ]
  , Tuple "src/Lib/Synth.stel"
      [ "module Lib.Synth where"
      , "import Stella.Elab"
      , "import Lib.Support"
      , "one :: Handle -> Handle / {| Kernel |}"
      , "one = synthesizer (\\_ -> literal (rootScope ()) (LitInt seed))"
      ]
  ]

app :: Array (Tuple String (Array String))
app =
  [ Tuple "src/Main.stel"
      [ "module Main where"
      , "import Lib.Pass"
      , "import Lib.Synth"
      , "pick :: {{ d :: Int by one }} -> Int -> Int"
      , "pick d x = d"
      , "n :: Int"
      , "n = pass%[2]"
      , "m :: Int"
      , "m = pick 5"
      ]
  ]

libraryModules :: Array String
libraryModules = [ "Lib.Support", "Lib.Pass", "Lib.Synth" ]

-- | The map, beside both packages, listing the library's modules by the files
-- | its build wrote.
depsMap :: String
depsMap = "{ \"formatVersion\": 0, \"modules\": [ " <> joinWith ", " (map entry libraryModules) <> " ] }"
  where
  entry m = "{ \"module\": \"" <> m <> "\", \"interface\": \"lib/output/_build/" <> m <> ".dmi\", \"object\": \"lib/output/_build/" <> m <> ".dmo\" }"

options :: String -> Maybe String -> BuildOptions
options workdir dependencies =
  { output: "output"
  , workdir
  , src: []
  , traceOpt: Nothing
  , emitCore: false
  , steamCmd: "steam"
  , dependencies
  , toolchainRebuild: []
  }

type Ran = { result :: Either String Unit, said :: Array String }

-- | The library built, the map written, and `app` built through it.
building :: (Ran -> Aff Unit) -> Aff Unit
building k = do
  said <- liftEffect (Ref.new [])
  result <- onDisk said do
    for_ [ Tuple "lib" library, Tuple "app" app ] \(Tuple package files) ->
      for_ files \(Tuple path lines) -> do
        _ <- FS.makeDirectory (fmt package "src/Lib")
        FS.writeText (fmt package path) (joinWith "\n" lines)
    _ <- FS.writeText (dir <> "/deps.json") depsMap
    program { logLevel: Info, monochrome: true, command: Build (options (dir <> "/lib") Nothing) }
    program { logLevel: Info, monochrome: true, command: Build (options (dir <> "/app") (Just "../deps.json")) }
  lines <- liftEffect (Ref.read said)
  k { result, said: lines }
  where
  fmt package path = dir <> "/" <> package <> "/" <> path

-- | The global of `Main` named, rendered once `Stella.Elab`, the modules the
-- | compiler carries, the library's modules, and `Main` are loaded.
valueOf :: String -> Aff String
valueOf global = do
  said <- liftEffect (Ref.new [])
  let paths = map (\m -> dir <> "/lib/output/_build/" <> m <> ".dmo") libraryModules <> [ dir <> "/app/output/_build/Main.dmo" ]
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
spec = describe "stellac build of a package calling a macro and naming a synthesizer of a package built apart" do
  it "loads the modules the map lists from the bytecode it names, each after those it imports and once, and the program runs on the machine" do
    building \r -> do
      r.result `shouldEqual` Right unit
      Array.filter (\l -> l == "[1/1] Compiling Main (" <> dir <> "/app/src/Main.stel)") r.said `shouldEqual` [ "[1/1] Compiling Main (" <> dir <> "/app/src/Main.stel)" ]
      n <- valueOf "n"
      m <- valueOf "m"
      [ n, m ] `shouldEqual` [ "2", "7" ]
