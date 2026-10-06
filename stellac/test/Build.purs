-- | `stellac build` over a package held in memory: what it writes where, what
-- | it says as it goes, and how it fails — a module that does not compile,
-- | and a file that cannot be written.
-- |
-- | The files are a map from path to text or bytes, and the paths given as
-- | unwritable fail to be written. Listing them gives every `.stel` file of
-- | the package whatever the patterns, which is all these packages hold; no
-- | build here runs a macro, so none opens a session.
module Test.Stellac.Build (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains, joinWith, stripPrefix)
import Data.String as String
import Data.Tuple (Tuple(..), snd)
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
import Stellac.Options (BuildOptions, Command(..))
import Stellac.Program (program)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Row (type (+))

data File = Text String | Binary (Array Int)

-- | Paths whose writing fails.
type Faults = { unwritable :: Array String }

noFaults :: Faults
noFaults = { unwritable: [] }

type Ran = { result :: Either String Unit, files :: Map String File, said :: Array String }

-- | The package of the files given, built with the options given, against the
-- | files already there and the faults given.
building :: (BuildOptions -> BuildOptions) -> Faults -> Array (Tuple String File) -> (Ran -> Aff Unit) -> Aff Unit
building options faults existing k = do
  files <- liftEffect (Ref.new (Map.fromFoldable existing))
  said <- liftEffect (Ref.new [])
  result <- runBuild files faults said
    (program { logLevel: Info, monochrome: true, command: Build (options defaults) })
  after <- liftEffect (Ref.read files)
  lines <- liftEffect (Ref.read said)
  k { result, files: after, said: lines }

defaults :: BuildOptions
defaults =
  { output: "output"
  , workdir: "."
  , src: []
  , traceOpt: Nothing
  , emitCore: false
  , steamCmd: "steam"
  }

runBuild :: Ref (Map String File) -> Faults -> Ref (Array String) -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF + ()) Unit -> Aff (Either String Unit)
runBuild files faults said p = p
  # FS.interpret (inMemory files faults)
  # Log.interpret (collect said)
  # Process.interpret (\_ -> Run.liftEffect (throwException (error "no session is opened in these tests")))
  # Except.runExcept
  # runBaseAff'

inMemory :: forall r. Ref (Map String File) -> Faults -> FileSystem ~> Run (EFFECT + r)
inMemory files faults = case _ of
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
  Glob root _ reply -> Run.liftEffect (Ref.read files) <#> \fs ->
    reply (Right (Array.sort (Array.mapMaybe (fromRoot root) (Array.filter (contains (Pattern ".stel")) (Array.fromFoldable (Map.keys fs))))))
  where
  writing :: forall a. String -> File -> (Either String Unit -> a) -> Run (EFFECT + r) a
  writing path file reply
    | Array.elem path faults.unwritable = pure (reply (Left "the disk is full"))
    | otherwise = reply (Right unit) <$ Run.liftEffect (Ref.modify_ (Map.insert path file) files)

-- | A path of the file system as its path from the root given, where it is
-- | under the root.
fromRoot :: String -> String -> Maybe String
fromRoot root path
  | root == "." = Just path
  | otherwise = stripPrefix (Pattern (root <> "/")) path

collect :: forall r. Ref (Array String) -> Log ~> Run (EFFECT + r)
collect said (Log _ doc next) = next <$ Run.liftEffect (Ref.modify_ (\l -> Array.snoc l (Dodo.print Dodo.plainText Dodo.twoSpaces doc)) said)

written :: Ran -> Array String
written r = Array.fromFoldable (Map.keys (Map.filterKeys (contains (Pattern "output/")) r.files))

source :: String -> Array String -> Tuple String File
source path lines = Tuple path (Text (joinWith "\n" lines))

-- | What an earlier build left of `Main`.
staleDmo :: Tuple String File
staleDmo = Tuple "output/_build/Main.dmo" (Binary [ 1, 2, 3 ])

staleDmi :: Tuple String File
staleDmi = Tuple "output/_build/Main.dmi" (Binary [ 4, 5, 6 ])

mainModule :: Tuple String File
mainModule = source "src/Main.stel" [ "module Main where", "n :: Int", "n = 1" ]

spec :: Spec Unit
spec = describe "stellac build" do
  it "writes each module's bytecode and interface under _build, modules none of which imports another in a stable order" do
    building identity noFaults
      [ source "src/Main.stel" [ "module Main where", "n :: Int", "n = 1" ]
      , source "src/Data/Util.stel" [ "module Data.Util where", "k :: Int", "k = 2" ]
      ]
      \r -> do
        r.result `shouldEqual` Right unit
        written r `shouldEqual` [ "output/_build/Data.Util.dmi", "output/_build/Data.Util.dmo", "output/_build/Main.dmi", "output/_build/Main.dmo" ]
        Array.take 2 r.said `shouldEqual` [ "[1/2] Compiling Data.Util (src/Data/Util.stel)", "[2/2] Compiling Main (src/Main.stel)" ]

  it "compiles a module against the modules of the package it imports" do
    building identity noFaults
      [ source "src/Main.stel" [ "module Main where", "import Data.Util", "n :: Int", "n = k" ]
      , source "src/Data/Util.stel" [ "module Data.Util where", "k :: Int", "k = 2" ]
      ]
      \r -> do
        r.result `shouldEqual` Right unit
        Array.take 2 r.said `shouldEqual` [ "[1/2] Compiling Data.Util (src/Data/Util.stel)", "[2/2] Compiling Main (src/Main.stel)" ]

  it "writes the optimizer's trace of the module --trace-opt names" do
    building (_ { traceOpt = Just (ModuleName "Main") }) noFaults [ mainModule ] \r ->
      case Map.lookup "output/_build/Main.mir" r.files of
        Just (Text text) -> text `shouldEqual` "=== pre-optimised (fixpoint input) ===\n=== converged ===\n(no optimizer rounds)\n"
        _ -> r.result `shouldEqual` Left "no trace"

  it "takes the source files, and writes its output, under --workdir" do
    building (_ { workdir = "pkg" }) noFaults [ Tuple "pkg/src/Main.stel" (snd mainModule) ] \r -> do
      r.result `shouldEqual` Right unit
      written r `shouldEqual` [ "pkg/output/_build/Main.dmi", "pkg/output/_build/Main.dmo" ]
      Array.take 1 r.said `shouldEqual` [ "[1/1] Compiling Main (pkg/src/Main.stel)" ]

  it "writes its output where an absolute --output names, whatever --workdir is" do
    building (_ { workdir = "pkg", output = "/out" }) noFaults [ Tuple "pkg/src/Main.stel" (snd mainModule) ] \r -> do
      r.result `shouldEqual` Right unit
      Map.member "/out/_build/Main.dmo" r.files `shouldEqual` true

  describe "a build that fails" do
    it "reports a module that does not compile where it stands" do
      building identity noFaults [ source "src/Main.stel" [ "module Main where", "n :: Int", "n = nope" ] ] \r -> do
        r.result `shouldEqual` Left "The build failed"
        Array.elem "src/Main.stel:3:5: There is no value `nope` in scope" r.said `shouldEqual` true
        written r `shouldEqual` []

    it "is one whose bytecode could not be written, which leaves neither file of the module's pair" do
      building identity noFaults { unwritable = [ "output/_build/Main.dmo" ] } [ mainModule, staleDmo, staleDmi ] \r -> do
        r.result `shouldEqual` Left "The build failed"
        Array.elem "`output/_build/Main.dmo` could not be written: the disk is full" r.said `shouldEqual` true
        written r `shouldEqual` []

    it "is one whose interface could not be written, which leaves neither file of the module's pair" do
      building identity noFaults { unwritable = [ "output/_build/Main.dmi" ] } [ mainModule, staleDmo, staleDmi ] \r -> do
        r.result `shouldEqual` Left "The build failed"
        Array.elem "`output/_build/Main.dmi` could not be written: the disk is full" r.said `shouldEqual` true
        written r `shouldEqual` []

