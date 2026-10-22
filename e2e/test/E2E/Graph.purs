-- | `stellac graph` run as a process, checked against what builds of the same
-- | files write.
-- |
-- | Three packages are built apart, each listing in `dependencies` what the
-- | builds before it wrote: `package-c` with `C.Core`; `package-b` with
-- | `B.Api`, which imports `C.Core`, re-exports it, and uses its type; and
-- | `package-a`, whose `A.Main` imports only `B.Api` but uses a name and a type
-- | of `C.Core` through it, and whose `A.Direct` imports `C.Core` itself.
-- | `package-a` lists `C.Core` beside `B.Api`, and the build accepts it like
-- | any listed module: which packages a package may import from is not the
-- | compiler's concern. For every module, the imports `graph` reports are the
-- | imports of the interface its build wrote, in the same order. The cases run
-- | in order: the first builds the packages.
module Test.E2E.Graph (spec) where

import Prelude

import Data.Argonaut.Core (Json, stringify, toArray, toObject, toString)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, indexOf)
import Data.String as String
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Fmt (fmt)
import Foreign.Object as Object
import Node.Buffer as Buffer
import Node.FS.Aff as FS
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.TypedCore (ModuleName(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.E2E.Process (Outcome, compile, copyTree, graph, removeTree, writeFiles)
import Test.E2E.StellaJson (Entry, listedAt, settings, stellaJson)

-- | Where this suite's files stand, written afresh for each run.
dir :: String
dir = "e2e/.test-integration/graph"

-- | `stella.json` of each package.
configs :: Array { path :: String, text :: String }
configs =
  [ { path: "package-c/stella.json", text: stellaJson (settings [ listedAt "src/C/Core.stel" ]) }
  , { path: "package-b/stella.json", text: stellaJson ((settings [ listedAt "src/B/Api.stel" ]) { dependencies = [ builtIn "package-c" "C.Core" ] }) }
  , { path: "package-a/stella.json", text: stellaJson ((settings (map listedAt [ "src/A/Main.stel", "src/A/Direct.stel" ])) { dependencies = [ builtIn "package-b" "B.Api", builtIn "package-c" "C.Core" ] }) }
  ]

-- | The module given, by the files the build of the package given wrote, from
-- | the package beside it.
builtIn :: String -> String -> Entry
builtIn package m = { module: m, interface: fmt @"../{package}/output/{m}.dmi" { package, m }, object: fmt @"../{package}/output/{m}.dmo" { package, m } }

-- | The package of the name given built by its `stella.json`.
built :: String -> Aff Unit
built package = do
  o <- compile (dir <> "/" <> package <> "/stella.json")
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
  o <- graph (dir <> "/" <> package <> "/stella.json")
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
  bytes <- FS.readFile (dir <> "/" <> package <> "/output/" <> m <> ".dmi") >>= liftEffect <<< Buffer.toArray
  case Interface.decode bytes of
    Left err -> fail (show err) *> pure []
    Right file -> pure (map (\(ModuleName n) -> n) file.interface.imports)

-- | The seed modules, each with its source from the repository's root.
seedSources :: Array (Tuple String String)
seedSources =
  [ Tuple "Base.Int" "stella-packages/base/src/Base/Int.stel"
  , Tuple "Stella.Syntax" "stella-packages/compiler-lib/src/Stella/Syntax.stel"
  , Tuple "Stella.Elab" "stella-packages/compiler-lib/src/Stella/Elab.stel"
  ]

-- | `stella.json` files of a package only `graph` is run on.
loose :: Array { path :: String, text :: String }
loose =
  [ { path: "loose/stella.json", text: stellaJson (settings (map listedAt [ "src/L/Main.stel", "src/L/Util.stel" ])) }
  , { path: "loose/util.json", text: stellaJson ((settings [ listedAt "src/L/Util.stel" ]) { dependencies = [ { module: "Gone", interface: "gone/Gone.dmi", object: "gone/Gone.dmo" } ] }) }
  , { path: "loose/seeds.json", text: stellaJson (settings (map (\(Tuple m p) -> { module: m, path: "../../../../" <> p }) seedSources)) }
  , { path: "loose/prim.json", text: stellaJson (settings [ { module: "Prim", path: "src/L/Util.stel" } ]) }
  ]

spec :: Spec Unit
spec = describe "`stellac graph`, and the source dependencies it reports" do
  it "builds each package, its `dependencies` listing what it imports, a transitive one among them" do
    removeTree dir
    copyTree "fixtures/source/graph" dir
    writeFiles dir configs
    built "package-c"
    built "package-b"
    built "package-a"

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

  it "prints each module, its path as `stella.json` writes it, and each module its header imports, where its name is written" do
    writeFiles dir loose
    o <- graph (dir <> "/loose/stella.json")
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

  it "reads the files of `modules` alone, none `dependencies` lists" do
    o <- graph (dir <> "/loose/util.json")
    o.status `shouldEqual` 0
    map (map (map _.module) <<< importsIn) (printed o) `shouldEqual` Right (Just [ "L.Util" ])

  it "takes the seed modules' own sources, which `stellac compile` refuses" do
    o <- graph (dir <> "/loose/seeds.json")
    o.status `shouldEqual` 0
    map importsIn (printed o) `shouldEqual` Right
      ( Just
          [ { module: "Base.Int", imports: [] }
          , { module: "Stella.Elab", imports: [] }
          , { module: "Stella.Syntax", imports: [ "Base.Int" ] }
          ]
      )
    refusing <- compile (dir <> "/loose/seeds.json")
    refusing.status `shouldEqual` 1

  it "refuses what the rules of the file refuse, as `stellac compile` does, printing no graph" do
    o <- graph (dir <> "/loose/prim.json")
    o.status `shouldEqual` 1
    when (contains (Pattern "{") o.out) (fail ("`graph` printed: " <> o.out))
    when (not (contains (Pattern "`modules[0].module` is `Prim`, which the compiler provides") o.err)) (fail ("`graph` did not refuse `Prim`:\n" <> o.err))

  it "refuses a header naming another module than its file is listed as, printing no graph" do
    writeFiles dir [ { path: "loose/src/L/Util.stel", text: "module L.Other where\n" } ]
    o <- graph (dir <> "/loose/stella.json")
    o.status `shouldEqual` 1
    when (contains (Pattern "{") o.out) (fail ("`graph` printed: " <> o.out))
    for_ [ "This module is named `L.Other`, and its file is given as `L.Util`", "The module graph could not be read" ] \line ->
      when (not (contains (Pattern line) o.err)) (fail ("`graph` did not say: " <> line <> "\n" <> o.err))
