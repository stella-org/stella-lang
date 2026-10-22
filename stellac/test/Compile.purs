-- | `stellac compile` over a package held in memory, `stella.json` among its
-- | files: what it writes where, what it says, and how it fails on a refused
-- | file, a module that does not compile, or a file it cannot write.
-- |
-- | The files are a map from path to text or bytes, and writing a path listed
-- | as unwritable fails. The command runs in `/work`. No build here runs a
-- | macro, so none opens a session.
module Test.Stellac.Compile (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, joinWith)
import Data.String as String
import Data.Tuple (Tuple(..))
import Dodo as Dodo
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (error, throwException)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run, runBaseAff')
import Run as Run
import Run.Except (EXCEPT)
import Run.Except as Except
import Stella.CLI.Effect.FS (FS, FileSystem(..))
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LOG, Log(..), LogLevel(..))
import Stella.CLI.Effect.Log as Log
import Stella.CLI.Effect.Process (PROCESS)
import Stella.CLI.Effect.Process as Process
import Stella.Compiler.TypedCore (ModuleName(..))
import Stellac.Config (load, normalize)
import Stellac.Config as Config
import Stellac.Options (Command(..))
import Stellac.Options as Options
import Stellac.Program (loaded, program)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stellac.StellaJson (Settings, settings, stellaJson)
import Type.Row (type (+))

data File = Text String | Binary (Array Int)

-- | Paths whose writing fails.
type Faults = { unwritable :: Array String }

noFaults :: Faults
noFaults = { unwritable: [] }

type Ran = { result :: Either String Unit, files :: Map String File, said :: Array String }

-- | `stellac compile` given the `stella.json` at the path given, against the
-- | files given and the faults given.
compilingAt :: String -> Faults -> Array (Tuple String File) -> (Ran -> Aff Unit) -> Aff Unit
compilingAt file faults existing k = do
  files <- liftEffect (Ref.new (Map.fromFoldable existing))
  said <- liftEffect (Ref.new [])
  result <- inMemory files faults said (loaded file >>= program (Compile file))
  after <- liftEffect (Ref.read files)
  lines <- liftEffect (Ref.read said)
  k { result, files: after, said: lines }

-- | `compilingAt`, the file `stella.json` written from the settings given.
compiling :: Settings -> Faults -> Array (Tuple String File) -> (Ran -> Aff Unit) -> Aff Unit
compiling s faults existing = compilingAt "stella.json" faults (existing <> [ Tuple "stella.json" (Text (stellaJson s)) ])

inMemory :: forall a. Ref (Map String File) -> Faults -> Ref (Array String) -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF + ()) a -> Aff (Either String a)
inMemory files faults log p = p
  # FS.interpret (handler files faults)
  # Log.interpret collect
  # Process.interpret (\_ -> Run.liftEffect (throwException (error "no session is opened in these tests")))
  # Except.runExcept
  # runBaseAff'
  where
  collect :: forall r. Log ~> Run (EFFECT + r)
  collect (Log _ doc next) = next <$ Run.liftEffect (Ref.modify_ (\l -> Array.snoc l (Dodo.print Dodo.plainText Dodo.twoSpaces doc)) log)

handler :: forall r. Ref (Map String File) -> Faults -> FileSystem ~> Run (EFFECT + r)
handler files faults = case _ of
  ReadBytes path reply -> Run.liftEffect (Ref.read files) <#> \fs -> reply case Map.lookup path fs of
    Just (Binary bytes) -> Right bytes
    _ -> Left "no such file"
  ReadText path reply -> Run.liftEffect (Ref.read files) <#> \fs -> reply case Map.lookup path fs of
    Just (Text text) -> Right text
    _ -> Left "no such file"
  WriteBytes path bytes reply -> writing path (Binary bytes) reply
  WriteText path text reply -> writing path (Text text) reply
  MakeDirectory _ reply -> pure (reply (Right unit))
  Remove path reply -> reply (Right unit) <$ Run.liftEffect (Ref.modify_ (Map.delete path) files)
  IsAbsolute path reply -> pure (reply (String.take 1 path == "/"))
  Resolve path reply -> pure (reply (normalize (if String.take 1 path == "/" then path else "/work/" <> path)))
  Glob _ _ reply -> pure (reply (Left "no pattern is listed in these tests"))
  where
  writing :: forall a. String -> File -> (Either String Unit -> a) -> Run (EFFECT + r) a
  writing path file reply
    | Array.elem path faults.unwritable = pure (reply (Left "the disk is full"))
    | otherwise = reply (Right unit) <$ Run.liftEffect (Ref.modify_ (Map.insert path file) files)

-- | The files written under `output`.
written :: Ran -> Array String
written r = Array.fromFoldable (Map.keys (Map.filterKeys (contains (Pattern "output/")) r.files))

saying :: Ran -> String -> Boolean
saying r line = Array.elem line r.said

source :: String -> Array String -> Tuple String File
source path lines = Tuple path (Text (joinWith "\n" lines))

listed :: String -> String -> { module :: String, path :: String }
listed m path = { module: m, path }

-- | What an earlier build left of `Main`.
staleDmo :: Tuple String File
staleDmo = Tuple "output/Main.dmo" (Binary [ 1, 2, 3 ])

staleDmi :: Tuple String File
staleDmi = Tuple "output/Main.dmi" (Binary [ 4, 5, 6 ])

mainModule :: Tuple String File
mainModule = source "src/Main.stel" [ "module Main where", "n :: Int", "n = 1" ]

mainOnly :: Settings
mainOnly = settings [ listed "Main" "src/Main.stel" ]

util :: Tuple String File
util = source "src/Data/Util.stel" [ "module Data.Util where", "data Box a = Box a", "k :: Int", "k = 2" ]

mainOverUtil :: Tuple String File
mainOverUtil = source "src/Main.stel" [ "module Main where", "import Data.Util", "n :: Box Int", "n = Box k" ]

spec :: Spec Unit
spec = describe "stellac compile" do
  it "writes each module's bytecode and interface to the output directory, in the order listed" do
    compiling (settings [ listed "Main" "src/Main.stel", listed "Data.Util" "src/Data/Util.stel" ]) noFaults [ mainModule, util ] \r -> do
      r.result `shouldEqual` Right unit
      written r `shouldEqual` [ "output/Data.Util.dmi", "output/Data.Util.dmo", "output/Main.dmi", "output/Main.dmo" ]
      Array.take 2 r.said `shouldEqual` [ "[1/2] Compiling Main (src/Main.stel)", "[2/2] Compiling Data.Util (src/Data/Util.stel)" ]

  it "compiles a module against the modules listed before it that it imports, their data types among them" do
    compiling (settings [ listed "Data.Util" "src/Data/Util.stel", listed "Main" "src/Main.stel" ]) noFaults [ mainOverUtil, util ] \r -> do
      r.result `shouldEqual` Right unit
      written r `shouldEqual` [ "output/Data.Util.dmi", "output/Data.Util.dmo", "output/Main.dmi", "output/Main.dmo" ]

  it "refuses a module listed before a module of the build it imports, before compiling any" do
    compiling (settings [ listed "Main" "src/Main.stel", listed "Data.Util" "src/Data/Util.stel" ]) noFaults [ mainOverUtil, util ] \r -> do
      r.result `shouldEqual` Left "The build failed"
      saying r "src/Main.stel:2:8: This module imports `Data.Util`, which is given after it" `shouldEqual` true
      Array.filter (contains (Pattern "Compiling")) r.said `shouldEqual` []
      written r `shouldEqual` []

  it "refuses a header naming another module than its file is listed as, compiling nothing" do
    compiling (settings [ listed "Other" "src/Main.stel" ]) noFaults [ mainModule ] \r -> do
      r.result `shouldEqual` Left "The build failed"
      saying r "src/Main.stel:1:8: This module is named `Main`, and its file is given as `Other`" `shouldEqual` true
      written r `shouldEqual` []

  it "writes the optimizer's trace of each module `traceOptimizer` names, and of none where it names none" do
    compiling ((settings [ listed "Data.Util" "src/Data/Util.stel", listed "Main" "src/Main.stel" ]) { traceOptimizer = [ "Main", "Data.Util" ] }) noFaults [ mainOverUtil, util ] \r -> do
      r.result `shouldEqual` Right unit
      for_ [ "output/Main.mir", "output/Data.Util.mir" ] \path -> case Map.lookup path r.files of
        Just (Text text) -> text `shouldEqual` "=== pre-optimised (fixpoint input) ===\n=== converged ===\n(no optimizer rounds)\n"
        _ -> fail ("no trace at " <> path)
    compiling mainOnly noFaults [ mainModule ] \r ->
      Array.filter (contains (Pattern ".mir")) (written r) `shouldEqual` []

  it "resolves each relative path against the directory `stella.json` stands in" do
    compilingAt "pkg/stella.json" noFaults
      [ Tuple "pkg/src/Main.stel" (Text "module Main where\nn :: Int\nn = 1"), Tuple "pkg/stella.json" (Text (stellaJson (mainOnly { output = "./out/../output" }))) ]
      \r -> do
        r.result `shouldEqual` Right unit
        written r `shouldEqual` [ "pkg/output/Main.dmi", "pkg/output/Main.dmo" ]
        Array.take 1 r.said `shouldEqual` [ "[1/1] Compiling Main (pkg/src/Main.stel)" ]

  it "writes where an absolute `output` names, wherever `stella.json` stands" do
    compilingAt "pkg/stella.json" noFaults [ Tuple "pkg/src/Main.stel" (Text "module Main where\nn :: Int\nn = 1"), Tuple "pkg/stella.json" (Text (stellaJson (mainOnly { output = "/out" }))) ] \r -> do
      r.result `shouldEqual` Right unit
      Map.member "/out/Main.dmo" r.files `shouldEqual` true

  it "refuses a seed module among `modules`, which it has no way to compile anew" do
    compiling (settings [ listed "Base.Int" "src/Base/Int.stel" ]) noFaults [ source "src/Base/Int.stel" [ "module Base.Int where", "foreign add :: Int -> Int -> Int" ] ] \r -> do
      r.result `shouldEqual` Left "The build failed"
      saying r "src/Base/Int.stel: This file holds `Base.Int`, which names a module the build is compiled against" `shouldEqual` true
      written r `shouldEqual` []

  describe "against `dependencies`" do
    let
      -- `Data.Util` built from source, its interface kept as `lib/Data.Util.dmi`
      withLibrary k = compiling (settings [ listed "Data.Util" "src/Data/Util.stel" ]) noFaults [ util ] \lib -> case Map.lookup "output/Data.Util.dmi" lib.files of
        Just dmi -> k (Tuple "lib/Data.Util.dmi" dmi)
        Nothing -> liftEffect (throwException (error "the library was not built"))
      depending s = s { dependencies = [ { module: "Data.Util", interface: "lib/Data.Util.dmi", object: "lib/Data.Util.dmo" } ] }

    it "compiles a module against the interfaces it lists" do
      withLibrary \dmi ->
        compiling (depending mainOnly) noFaults [ dmi, mainOverUtil ] \r -> do
          r.result `shouldEqual` Right unit
          written r `shouldEqual` [ "output/Main.dmi", "output/Main.dmo" ]

    it "reports an interface it cannot use, and builds nothing" do
      compiling (depending mainOnly) noFaults [ mainOverUtil ] \r -> do
        r.result `shouldEqual` Left "The build failed"
        saying r "The interface of `Data.Util`, `lib/Data.Util.dmi`, could not be read: no such file" `shouldEqual` true
        written r `shouldEqual` []

    it "checks it where `modules` is empty, then writes nothing and succeeds" do
      compiling (depending (settings [])) noFaults [] \r -> do
        r.result `shouldEqual` Left "The build failed"
        saying r "The interface of `Data.Util`, `lib/Data.Util.dmi`, could not be read: no such file" `shouldEqual` true
      withLibrary \dmi ->
        compiling (depending (settings [])) noFaults [ dmi ] \r -> do
          r.result `shouldEqual` Right unit
          r.said `shouldEqual` [ "Nothing to build" ]
          written r `shouldEqual` []

  describe "a build that fails" do
    it "reports a module that does not compile where it stands" do
      compiling mainOnly noFaults [ source "src/Main.stel" [ "module Main where", "n :: Int", "n = nope" ] ] \r -> do
        r.result `shouldEqual` Left "The build failed"
        saying r "src/Main.stel:3:5: There is no value `nope` in scope" `shouldEqual` true
        written r `shouldEqual` []

    it "is one whose bytecode could not be written, which leaves neither file of the module's pair" do
      compiling mainOnly noFaults { unwritable = [ "output/Main.dmo" ] } [ mainModule, staleDmo, staleDmi ] \r -> do
        r.result `shouldEqual` Left "The build failed"
        saying r "`output/Main.dmo` could not be written: the disk is full" `shouldEqual` true
        written r `shouldEqual` []

    it "is one whose interface could not be written, which leaves neither file of the module's pair" do
      compiling mainOnly noFaults { unwritable = [ "output/Main.dmi" ] } [ mainModule, staleDmo, staleDmi ] \r -> do
        r.result `shouldEqual` Left "The build failed"
        saying r "`output/Main.dmi` could not be written: the disk is full" `shouldEqual` true
        written r `shouldEqual` []

  describe "`stella.json`" do
    let
      refusedSaying lines r = do
        r.result `shouldEqual` Left "`stella.json` was refused"
        r.said `shouldEqual` lines
        written r `shouldEqual` []
      raw text = compilingAt "stella.json" noFaults [ mainModule, Tuple "stella.json" (Text text) ]

    it "reads the file it writes" do
      let
        config =
          { options: { output: "out", emitCore: true, traceOptimizer: [ ModuleName "Main" ], steamCmd: "./steam", logLevel: Debug, monochrome: false }
          , modules: [ { module: ModuleName "Main", path: "src/Main.stel", written: "src/Main.stel" } ]
          , dependencies: [ { module: ModuleName "Lib", interface: "lib/Lib.dmi", object: "lib/Lib.dmo" } ]
          }
      Config.decode (Config.encode config) `shouldEqual` Right config

    it "refuses a file lacking a field, in the file and in `options`" do
      raw """{ "formatVersion": 0, "options": { "output": "o", "emitCore": false, "traceOptimizer": [], "steamCmd": "steam", "logLevel": "info", "monochrome": true }, "modules": [] }"""
        $ refusedSaying [ "stella.json: `dependencies` is missing" ]
      raw """{ "formatVersion": 0, "options": { "output": "o", "emitCore": false, "traceOptimizer": [], "steamCmd": "steam", "logLevel": "info" }, "modules": [], "dependencies": [] }"""
        $ refusedSaying [ "stella.json: `options.monochrome` is missing" ]

    it "refuses a field no rule names, in the file, in `options`, and in an entry" do
      raw (String.replace (Pattern "\"formatVersion\": 0") (String.Replacement "\"formatVersion\": 0, \"version\": 1") (stellaJson mainOnly))
        $ refusedSaying [ "stella.json: `version` is no field this compiler takes" ]
      raw (String.replace (Pattern "\"monochrome\": true") (String.Replacement "\"monochrome\": true, \"colour\": true") (stellaJson mainOnly))
        $ refusedSaying [ "stella.json: `options.colour` is no field this compiler takes" ]
      raw (String.replace (Pattern "\"path\": \"src/Main.stel\"") (String.Replacement "\"path\": \"src/Main.stel\", \"test\": false") (stellaJson mainOnly))
        $ refusedSaying [ "stella.json: `modules[0].test` is no field this compiler takes" ]

    it "refuses another format version, a field of another kind, an empty string, and a log level of no name" do
      raw (String.replace (Pattern "\"formatVersion\": 0") (String.Replacement "\"formatVersion\": 1") (stellaJson mainOnly))
        $ refusedSaying [ "stella.json: `formatVersion`, `1`, is not 0, the version this compiler reads" ]
      raw (String.replace (Pattern "\"emitCore\": false") (String.Replacement "\"emitCore\": \"no\"") (stellaJson mainOnly))
        $ refusedSaying [ "stella.json: `options.emitCore` is not a boolean" ]
      raw (stellaJson (mainOnly { output = "" }))
        $ refusedSaying [ "stella.json: `options.output` is empty" ]
      raw (String.replace (Pattern "\"logLevel\": \"info\"") (String.Replacement "\"logLevel\": \"loud\"") (stellaJson mainOnly))
        $ refusedSaying [ "stella.json: `options.logLevel`, `loud`, is not one of `debug`, `info`, `warn`, and `error`" ]
      raw "[]"
        $ refusedSaying [ "stella.json: the file is not an object" ]

    it "refuses a module listed twice, a file listed twice once paths are normalized, `Prim`, and a name no module may have" do
      compiling (settings [ listed "Main" "src/Main.stel", listed "Other" "src/./Data/../Main.stel", listed "Main" "src/B.stel", listed "Prim" "src/Prim.stel", listed "a.B" "src/C.stel" ]) noFaults [ mainModule ]
        $ refusedSaying
            [ "stella.json: `modules[4].module`, `a.B`, is not a module's name" ]
      compiling (settings [ listed "Main" "src/Main.stel", listed "Other" "src/./Data/../Main.stel", listed "Main" "src/B.stel", listed "Prim" "src/Prim.stel" ]) noFaults [ mainModule ]
        $ refusedSaying
            [ "stella.json: `modules` lists `Main` more than once"
            , "stella.json: `modules[1].path`, `src/./Data/../Main.stel`, is a file `modules` lists before it"
            , "stella.json: `modules[3].module` is `Prim`, which the compiler provides"
            ]

    it "refuses a module both `modules` and `dependencies` list, and `traceOptimizer` naming a module unlisted or twice" do
      compiling ((mainOnly { traceOptimizer = [ "Main", "Gone", "Main" ] }) { dependencies = [ { module: "Main", interface: "M.dmi", object: "M.dmo" } ] }) noFaults [ mainModule ]
        $ refusedSaying
            [ "stella.json: `Main` is listed by both `modules` and `dependencies`"
            , "stella.json: `options.traceOptimizer[1]`, `Gone`, is no module `modules` lists"
            , "stella.json: `options.traceOptimizer` names `Main` more than once"
            ]

    it "looks a bare `steamCmd` up on `PATH`, resolves another relative one against its directory to a path from the root, and keeps an absolute one" do
      for_
        [ { file: "pkg/stella.json", given: "steam", resolved: "steam" }
        , { file: "pkg/stella.json", given: "./bin/steam", resolved: "/work/pkg/bin/steam" }
        , { file: "pkg/stella.json", given: "/opt/steam", resolved: "/opt/steam" }
        -- a path still where normalizing leaves no `/` of it
        , { file: "stella.json", given: "./steam", resolved: "/work/steam" }
        ]
        \{ file, given, resolved } -> do
          files <- liftEffect (Ref.new (Map.singleton file (Text (stellaJson (mainOnly { steamCmd = given })))))
          lines <- liftEffect (Ref.new [])
          result <- inMemory files noFaults lines (load file)
          map (map _.options.steamCmd) result `shouldEqual` Right (Right resolved)

  describe "the command line" do
    it "takes one `stella.json` and nothing else, and has no `build`" do
      case Options.parse [ "compile", "a.json" ] of
        Right (Compile file) -> file `shouldEqual` "a.json"
        _ -> fail "not taken"
      for_ [ [ "compile" ], [ "compile", "a.json", "b.json" ], [ "build", "a.json" ], [ "compile", "a.json", "--log-level", "error" ] ] \args ->
        case Options.parse args of
          Left _ -> pure unit
          Right command -> fail ("taken: " <> show command)
