-- | `stellac graph` run as a process, and the source dependencies it reports
-- | against what builds of the same files write.
-- |
-- | Three packages are built apart, each against a dependency map listing the
-- | files the builds before it wrote: `package-c` of `C.Core`; `package-b` of
-- | `B.Api`, which imports `C.Core`, re-exports it whole, and uses its type in
-- | its own; and `package-a`, whose `A.Main` imports `B.Api` alone, using a
-- | name and a type `C.Core` declares through it, and whose `A.Direct` imports
-- | `C.Core` itself. The map `package-a` is built against lists `C.Core` beside
-- | `B.Api`, and the build takes it as it takes any module listed: which
-- | packages a package may import from is no concern of the compiler's. For
-- | every module, the modules its header imports, as `graph` reports them, are
-- | the imports of the interface its build wrote, in the same order. The cases
-- | run in order: the first builds the packages.
module Test.E2E.Graph (spec) where

import Prelude

import Data.Argonaut.Core (Json, stringify, toArray, toObject, toString)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, indexOf, joinWith)
import Data.String as String
import Data.Traversable (for, traverse)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Fmt (DefaultConfig, SetOpenClose, fmtWith)
import Foreign.Object as Object
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.TypedCore (ModuleName(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.E2E.Process (Outcome, copyTree, graph, removeTree, stellac, writeFiles)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/graph"

-- | The dependency maps, each beside the package it is given to.
maps :: Array { path :: String, text :: String }
maps =
  [ { path: "package-b/deps.json", text: mapOf [ { module: "C.Core", package: "package-c" } ] }
  , { path: "package-a/deps.json", text: mapOf [ { module: "B.Api", package: "package-b" }, { module: "C.Core", package: "package-c" } ] }
  ]

-- | A dependency map, beside the package it is given to, listing each module
-- | given by the files the build of the package given wrote.
mapOf :: Array { module :: String, package :: String } -> String
mapOf entries = fmtWith @(SetOpenClose "<" ">" DefaultConfig) @"""{ "formatVersion": 0, "modules": [ <entries> ] }""" { entries: joinWith ", " (map entry entries) }
  where
  entry e = fmtWith @(SetOpenClose "<" ">" DefaultConfig) @"""{ "module": "<m>", "interface": "../<p>/output/_build/<m>.dmi", "object": "../<p>/output/_build/<m>.dmo" }""" { m: e.module, p: e.package }

-- | The package of the name given built, against its map where it has one.
built :: String -> Array String -> Aff Unit
built package args = do
  o <- stellac ([ "--workdir", dir <> "/" <> package ] <> args)
  when (o.status /= 0) (fail (package <> " did not build: " <> o.err))

-- | What `graph` printed, the development entry point's banner left out.
printed :: Outcome -> Either String Json
printed o = case indexOf (Pattern "{") o.out of
  Nothing -> Left ("`graph` printed no JSON: " <> o.out <> o.err)
  Just i -> jsonParser (String.drop i o.out)

-- | Each module a graph lists, with the modules it imports, in order.
importsIn :: Json -> Maybe (Array { module :: String, imports :: Array String })
importsIn json = do
  modules <- toObject json >>= Object.lookup "modules" >>= toArray
  for modules \m -> do
    fields <- toObject m
    name <- Object.lookup "module" fields >>= toString
    imports <- Object.lookup "imports" fields >>= toArray >>= traverse (\i -> toObject i >>= Object.lookup "module" >>= toString)
    pure { module: name, imports }

-- | The graph of the package of the name given.
graphOf :: String -> Aff (Array { module :: String, imports :: Array String })
graphOf package = do
  o <- graph [ "--workdir", dir <> "/" <> package ]
  o.status `shouldEqual` 0
  case printed o of
    Left why -> fail why *> pure []
    Right json -> case importsIn json of
      Nothing -> fail ("`graph` printed no graph: " <> stringify json) *> pure []
      Just modules -> pure modules

-- | The imports of the interface the build of the package given wrote for the
-- | module given.
interfaceImports :: String -> String -> Aff (Array String)
interfaceImports package m = do
  bytes <- FS.readFile (dir <> "/" <> package <> "/output/_build/" <> m <> ".dmi") >>= liftEffect <<< Buffer.toArray
  case Interface.decode bytes of
    Left err -> fail (show err) *> pure []
    Right file -> pure (map (\(ModuleName n) -> n) file.interface.imports)

spec :: Spec Unit
spec = describe "`stellac graph`, and the source dependencies it reports" do
  it "builds each package against a map listing what it imports, a transitive one among them" do
    removeTree dir
    copyTree "fixtures/source/graph" dir
    writeFiles dir maps
    built "package-c" []
    built "package-b" [ "--dependencies", "deps.json" ]
    built "package-a" [ "--dependencies", "deps.json" ]

  it "reports, for every module, the imports of the interface its build wrote, in order" do
    for_ [ "package-a", "package-b", "package-c" ] \package -> do
      modules <- graphOf package
      for_ modules \m -> do
        imports <- interfaceImports package m.module
        { module: m.module, imports: m.imports } `shouldEqual` { module: m.module, imports }

  it "reports what a header imports, not what the module reaches through it" do
    modules <- graphOf "package-a"
    modules `shouldEqual`
      [ { module: "A.Direct", imports: [ "C.Core", "A.Main", "B.Api" ] }
      , { module: "A.Main", imports: [ "B.Api" ] }
      ]

  it "prints each module, its path, and each module its header imports, where its name is written" do
    o <- graph [ "--workdir", dir <> "/loose" ]
    o.status `shouldEqual` 0
    map stringify (printed o) `shouldEqual` map stringify
      ( jsonParser
          """{ "formatVersion": 0,
  "modules": [
    { "module": "L.Main", "path": "src/L/Main.stel",
      "imports": [
        { "module": "Elsewhere.Thing", "start": { "line": 4, "column": 8 }, "end": { "line": 4, "column": 23 } },
        { "module": "L.Util", "start": { "line": 5, "column": 8 }, "end": { "line": 5, "column": 14 } } ] },
    { "module": "L.Util", "path": "src/L/Util.stel",
      "imports": [ { "module": "L.Main", "start": { "line": 2, "column": 8 }, "end": { "line": 2, "column": 14 } } ] } ] }"""
      )

  it "reads the files `--src` names alone" do
    o <- graph [ "--workdir", dir <> "/loose", "--src", "src/L/Util.stel" ]
    map (map (map _.module) <<< importsIn) (printed o) `shouldEqual` Right (Just [ "L.Util" ])

  it "refuses a header naming another module than its path does, printing no graph" do
    writeFiles dir [ { path: "loose/src/L/Util.stel", text: "module L.Other where\n" } ]
    o <- graph [ "--workdir", dir <> "/loose" ]
    o.status `shouldEqual` 1
    when (contains (Pattern "{") o.out) (fail ("`graph` printed: " <> o.out))
    for_ [ "This module is named `L.Other`, and its path names it `L.Util`", "The module graph could not be read" ] \line ->
      when (not (contains (Pattern line) o.err)) (fail ("`graph` did not say: " <> line <> "\n" <> o.err))
