-- | The `Base` package built from its sources, `stella-packages/base`, by the
-- | development script, and a program built against the dependency map the
-- | script writes and run by `steam run`, as processes.
-- |
-- | The map lists every module of the package, `Base.Int` among them, which the
-- | compiler carries and accepts as it carries it. `App` composes actions with
-- | `Base.IO`, over `Base.String` and `Base.Int`, beside `Console`, whose
-- | foreign the host implements, and handles an effect by a `reifiable full`
-- | clause, resuming with `Base.Continuation.continue`; it runs over the
-- | bytecode the map names. Maps
-- | listing a module the compiler carries with another interface, `Prim`, or a
-- | module twice are refused. The cases run in order: the first builds `Base`.
module Test.E2E.BasePackage (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, joinWith, split)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Fmt (DefaultConfig, SetOpenClose, fmtWith)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Stella.Compiler.Interface.Environment (initialEnvironment)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..))
import Stellac.Dependencies (parse)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.E2E.Process (Outcome, buildBase, copyTree, removeTree, steamRun, stellac, writeFiles)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/base-package"

-- | Where the script writes what the build of `Base` writes, and its map.
baseOutput :: String
baseOutput = dir <> "/base"

-- | A map under `maps`, listing each module given by the files of the name
-- | given that the build of `Base` wrote.
mapOf :: Array { module :: String, file :: String } -> String
mapOf entries = fmtWith @(SetOpenClose "<" ">" DefaultConfig) @"""{ "formatVersion": 0, "modules": [ <entries> ] }""" { entries: joinWith ", " (map entry entries) }
  where
  entry e = fmtWith @(SetOpenClose "<" ">" DefaultConfig) @"""{ "module": "<m>", "interface": "../base/_build/<f>.dmi", "object": "../base/_build/<f>.dmo" }""" { m: e.module, f: e.file }

-- | `App` built against the map of the path given, relative to the package.
buildApp :: String -> Aff Outcome
buildApp depsMap = stellac [ "--workdir", dir <> "/app", "--dependencies", depsMap ]

-- | The bytecode of the modules the map the script wrote lists, as it lists
-- | them.
listed :: Aff (Array String)
listed = do
  text <- FS.readTextFile UTF8 (baseOutput <> "/dependencies.json")
  case parse "dependencies.json" text of
    Left err -> fail (show err) *> pure []
    Right entries -> pure (map (\e -> baseOutput <> "/" <> e.object) entries)

bytesOf :: String -> Aff Bytes
bytesOf path = FS.readFile path >>= liftEffect <<< Buffer.toArray

writeBytes :: String -> Bytes -> Aff Unit
writeBytes path bytes = liftEffect (Buffer.fromArray bytes) >>= FS.writeFile path

-- | The lines a run printed, the development entry point's banner left out.
printed :: Outcome -> Array String
printed o = Array.filter (\l -> l /= "" && not (isBanner l)) (split (Pattern "\n") o.out)
  where
  isBanner = contains (Pattern "!!! This is development version of steam !!!")

-- | Whether a build failed, saying the line given.
refused :: String -> Outcome -> Aff Unit
refused line o = do
  o.status `shouldEqual` 1
  when (not (contains (Pattern line) o.err)) (fail ("the build did not say: " <> line <> "\n" <> o.err))

spec :: Spec Unit
spec = describe "the `Base` package, built from its sources and given by a map" do
  it "builds `Base` and writes a map listing every module of it" do
    removeTree dir
    built <- buildBase [ "--output", baseOutput ]
    when (built.status /= 0) (fail ("`Base` did not build: " <> built.err))
    modules <- listed
    modules `shouldEqual` map (\m -> baseOutput <> "/_build/Base." <> m <> ".dmo") [ "Array", "Char", "Continuation", "IO", "Int", "Number", "String" ]

  it "builds a program against the map, `Base.Int` accepted as the module the compiler carries" do
    copyTree "fixtures/source/base-package" dir
    built <- buildApp "../base/dependencies.json"
    when (built.status /= 0) (fail ("the program did not build: " <> built.err))

  it "runs the program over the bytecode the map names" do
    modules <- listed
    outcome <- steamRun
      { manifest: dir <> "/app/foreign.json"
      , entry: "Main"
      , modules: modules <> [ dir <> "/app/output/_build/Console.dmo", dir <> "/app/output/_build/Main.dmo" ]
      }
    outcome.err `shouldEqual` ""
    outcome.status `shouldEqual` 0
    printed outcome `shouldEqual` [ "built apart", "12", "6" ]

  it "refuses a map listing a module the compiler carries with another interface" do
    stored <- bytesOf (baseOutput <> "/_build/Base.Int.dmi")
    case Interface.decode stored of
      Left err -> fail (show err)
      Right file -> do
        let
          values = Map.delete (Ident "toString") file.interface.declarations.values
          other = file.interface { declarations { values = values } }
        case Interface.encode file { interface = other } of
          Left err -> fail (show err)
          Right bytes -> writeBytes (baseOutput <> "/_build/Other.Int.dmi") bytes
    writeFiles dir [ { path: "maps/other.json", text: mapOf [ { module: "Base.String", file: "Base.String" }, { module: "Base.Int", file: "Other.Int" } ] } ]
    buildApp "../maps/other.json" >>= refused "The dependency map lists `Base.Int` with an interface that differs from the one of the module the compiler carries"

  it "refuses a map listing `Prim`" do
    case Map.lookup (ModuleName "Prim") initialEnvironment.interfaces of
      Nothing -> fail "no `Prim`"
      Just prim -> case Interface.encode { interface: prim, buildHash: Nothing } of
        Left err -> fail (show err)
        Right bytes -> writeBytes (baseOutput <> "/_build/Prim.dmi") bytes
    writeFiles dir [ { path: "maps/prim.json", text: mapOf [ { module: "Base.String", file: "Base.String" }, { module: "Prim", file: "Prim" } ] } ]
    buildApp "../maps/prim.json" >>= refused "The dependency map lists `Prim`, which the compiler provides"

  it "refuses a map listing a module twice, whether or not the compiler carries it" do
    let
      twice = [ { module: "Base.String", file: "Base.String" }, { module: "Base.Int", file: "Base.Int" } ]
    writeFiles dir [ { path: "maps/twice.json", text: mapOf (twice <> twice) } ]
    outcome <- buildApp "../maps/twice.json"
    refused "The dependency map lists `Base.Int` more than once" outcome
    refused "The dependency map lists `Base.String` more than once" outcome
