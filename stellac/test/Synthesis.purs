-- | `stellac build` of a package whose module names a synthesizer another of
-- | its modules writes: the files on disk, the session a process, and the
-- | modules built then run on the machine.
-- |
-- | Each case builds in a directory of its own under `stellac/.test-build`, the
-- | session started as `node steam/index.dev.js session`. `A` writes the
-- | synthesizers against `Stella.Elab`, over `Support`, a module of the package
-- | the session loads before `A`; `Main` names one by a synthesized parameter,
-- | at two goals.
module Test.Stellac.Synthesis (spec, onDisk, development) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String (Pattern(..), contains, joinWith, split)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Dodo as Dodo
import Effect.Aff (Aff, Milliseconds(..))
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run, runBaseAff', runBaseEffect)
import Run as Run
import Run.Except (EXCEPT)
import Run.Except as Except
import Steam.CLI.Elaboration as Elaboration
import Steam.Foreign (emptyTable)
import Steam.Load (emptyStore, globalNamed, load, noIdentities)
import Steam.Value (Value(..))
import Stella.CLI.Effect.FS (FS)
import Stella.CLI.Effect.FS as FS
import Stella.CLI.Effect.Log (LOG, Log(..), LogLevel(..))
import Stella.CLI.Effect.Log as Log
import Stella.CLI.Effect.Process (Output(..), PROCESS, Process(..))
import Stella.CLI.Effect.Process as Process
import Stella.CLI.Runner.Node as Node
import Stella.CLI.Session.Broker (SessionHealth(..), newCancellation)
import Stella.CLI.Session.Client as Client
import Stella.CLI.Session.CompileTime (CompileTimeError)
import Stella.CLI.Session.RunParser (openingParser)
import Stella.CLI.Session.Synthesis (Synthesizing, defaultSynthesisSettings, openingSynthesis)
import Stella.Compiler.Build (BuiltModules, CompilerAction, build, ordinary, buildMessages, defaultHooks, defaultSourceRoots, printBuildMessage)
import Stella.Compiler.Bytecode (decode, encode)
import Stella.Compiler.Elaborate.Driver.Loop (AttempterM)
import Stella.Compiler.Elaborate.Driver.Synthesis (attemptJob)
import Stella.Compiler.Elaborate.Kernel.Elab (SessionEnv)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.Macro.Run (defaultSettings)
import Stella.Compiler.TypedCore (Decl(..), Ident(..), ModuleName(..), Qualified(..))
import Stella.Compiler.TypedCore.Term (Literal(..))
import Stellac.Options (BuildOptions, Command(..))
import Stellac.Program (program)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Type.Row (type (+))

-- | `Support`: what `A` fills a goal with.
support :: Array String
support = [ "module Support where", "seed :: Int", "seed = 1" ]

-- | `A`: the synthesizers, one filling a goal with `Support.seed`, one
-- | refusing, one faulting, and one that never returns.
synthesizers :: Array String
synthesizers =
  [ "module A where"
  , "import Stella.Elab"
  , "import Base.Int (quot)"
  , "import Support"
  , "one :: Handle -> Handle / {| Kernel |}"
  , "one = synthesizer (\\_ -> literal (rootScope ()) (LitInt seed))"
  , "refusing :: Handle -> Handle / {| Kernel |}"
  , "refusing = synthesizer (\\_ -> throw (Cons (TextPart \"nothing fits\") Nil))"
  , "faulty :: Handle -> Handle / {| Kernel |}"
  , "faulty = synthesizer (\\_ -> literal (rootScope ()) (LitInt (quot 1 0)))"
  , "spin :: Int -> Int"
  , "spin n = spin n"
  , "looping :: Handle -> Handle / {| Kernel |}"
  , "looping = synthesizer (\\_ -> literal (rootScope ()) (LitInt (spin 0)))"
  ]

-- | `Main`, naming the synthesizer given for the parameter of `pick`, and `n`
-- | and `m` the values `pick` gives, a goal each.
mainNaming :: String -> Array String
mainNaming synthesizer =
  [ "module Main where"
  , "import A"
  , "pick :: {{ d :: Int by " <> synthesizer <> " }} -> Int -> Int"
  , "pick d x = d"
  , "n :: Int"
  , "n = pick 5"
  , "m :: Int"
  , "m = pick 6"
  ]

type Ran = { result :: Either String Unit, said :: Array String, dir :: String }

-- | The package `Support`, `A`, and `Main` naming the synthesizer given, built with
-- | `stellac build` in the directory given.
building :: String -> String -> (Ran -> Aff Unit) -> Aff Unit
building name synthesizer k = do
  let dir = "stellac/.test-build/" <> name
  said <- liftEffect (Ref.new [])
  result <- onDisk said do
    for_ [ Tuple "src/Support.stel" support, Tuple "src/A.stel" synthesizers, Tuple "src/Main.stel" (mainNaming synthesizer) ] \(Tuple path lines) -> do
      _ <- FS.makeDirectory (dir <> "/src")
      FS.writeText (dir <> "/" <> path) (joinWith "\n" lines)
    program { logLevel: Info, monochrome: true, command: Build (options dir) }
  lines <- liftEffect (Ref.read said)
  k { result, said: lines, dir }

options :: String -> BuildOptions
options dir =
  { output: "output"
  , workdir: dir
  , src: []
  , traceOpt: Nothing
  , emitCore: false
  , steamCmd: "steam"
  , dependencies: Nothing
  , toolchainRebuild: []
  }

-- | Run on the disk and on real processes, `steam` started as the development
-- | entry point, the log collected.
onDisk :: forall a. Ref (Array String) -> Run (FS + LOG + PROCESS + EXCEPT String + EFFECT + AFF + ()) a -> Aff (Either String a)
onDisk said p = p
  # FS.interpret Node.nodeFsHandler
  # Log.interpret (\(Log _ doc next) -> next <$ Run.liftEffect (Ref.modify_ (\l -> Array.snoc l (Dodo.print Dodo.plainText Dodo.twoSpaces doc)) said))
  # Process.interpret development
  # Except.runExcept
  # runBaseAff'

-- | `steam` as `node steam/index.dev.js`.
development :: forall r. Process ~> Run (EFFECT + r)
development (SpawnSession launch reply) = Node.nodeProcessHandler
  (SpawnSession (if launch.command == "steam" then launch { command = "node", args = [ "steam/index.dev.js" ] <> launch.args } else launch) reply)

-- | The global of `Main` named, rendered once the modules built are loaded, in
-- | the order given, after `Stella.Elab` and the modules the compiler carries.
valueOf :: String -> Array String -> String -> Aff String
valueOf dir modules global = do
  read <- onDisk' (for modules \m -> FS.readBytes (dir <> "/output/_build/" <> m <> ".dmo"))
  case Elaboration.prepare, compiled, traverse' read of
    Left why, _, _ -> pure ("no Stella.Elab: " <> why)
    _, Left why, _ -> pure ("no carried modules: " <> why)
    _, _, Left why -> pure why
    Right elab, Right carried, Right dmos -> liftEffect do
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
  onDisk' p = do
    said <- liftEffect (Ref.new [])
    onDisk said p <#> case _ of
      Left why -> [ Left why ]
      Right files -> files
  traverse' read = for read case _ of
    Left why -> Left why
    Right bytes -> case decode bytes of
      Left err -> Left (show err)
      Right dmo -> Right dmo

-- | A Core module's declarations with every annotation dropped.
erased :: forall a. Array (Decl a) -> Array (Decl Unit)
erased = map case _ of
  DeclData _ d -> DeclData unit d
  DeclEffect _ e -> DeclEffect unit e
  DeclForeign _ f -> DeclForeign unit f
  DeclNonRec _ b -> DeclNonRec unit (bound b)
  DeclRec _ bs -> DeclRec unit (map bound bs)
  DeclAttribute _ a -> DeclAttribute unit a
  where
  bound b = b { value = map (const unit) b.value }

-- | `Support`, `A`, and `Main` naming `A.one`, built in the directory given with the
-- | synthesis given, and the declarations of `Main`'s Core, annotations
-- | dropped.
coreOfMain
  :: String
  -> (Synthesizing (FS + ()) -> BuiltModules -> SessionEnv -> AttempterM (Run (EXCEPT CompileTimeError + FS + PROCESS + AFF + EFFECT + ())))
  -> Aff (Either String (Array (Decl Unit)))
coreOfMain name synthesis = case compiled of
  Left why -> pure (Left why)
  Right syntax -> case Array.foldM (flip addInterface) initialEnvironment syntax.moduleInterfaces of
    Left err -> pure (Left (show err))
    Right env -> do
      let dir = "stellac/.test-build/" <> name
      held <- liftEffect (Ref.new Nothing)
      written <- liftEffect (Ref.new Set.empty)
      loaded <- liftEffect (Ref.new Set.empty)
      core <- liftEffect (Ref.new Nothing)
      cancellation <- liftEffect (newCancellation (Milliseconds 1000.0))
      attempts <- liftEffect (Ref.new 0)
      health <- liftEffect (Ref.new Reusable)
      let
        sources = [ Tuple "src/Support.stel" support, Tuple "src/A.stel" synthesizers, Tuple "src/Main.stel" (mainNaming "one") ]
        launch = { command: "steam", args: [ "session" ], output: Inherit, hello: { protocol: 1, profile: "elaboration", offers: [ "modules", "parse", "invoke", "kernel" ], requires: [] } }
        loading =
          { seed: syntax.preloaded
          , importsOf: const Nothing
          , loaded
          , locate: \m -> liftEffect (Ref.read written) <#> \names ->
              if Set.member m names then Just (dir <> "/" <> moduleText m <> ".dmo") else Nothing
          }
        running = { held, launch, descriptor: syntax.elaboration.descriptor, loading, budget: defaultSynthesisSettings.budget, cancellation, attempts, health }

        action :: CompilerAction (Run (EXCEPT CompileTimeError + FS + PROCESS + AFF + EFFECT + ()))
        action =
          { readSource: \path -> pure case Array.find (\(Tuple p _) -> p == path) sources of
              Just (Tuple _ lines) -> Right (joinWith "\n" lines)
              Nothing -> Left "no such file"
          , runParser: openingParser held launch syntax.descriptor loading
          , synthesis: synthesis running
          , hooks: defaultHooks
              { onElaborated = \c -> when (c.name == ModuleName "Main") (liftEffect (Ref.write (Just (erased c.decls)) core))
              , onLowered = \made -> case encode made.dmo of
                  Left _ -> pure unit
                  Right bytes -> do
                    _ <- FS.makeDirectory dir
                    _ <- FS.writeBytes (dir <> "/" <> moduleText made.dmo.name <> ".dmo") bytes
                    liftEffect (Ref.modify_ (Set.insert made.dmo.name) written)
              }
          }
      outcome <- runOnDisk (Except.runExcept (build action defaultSettings (ordinary env) defaultSourceRoots (map (\(Tuple path _) -> { path, within: split (Pattern "/") path }) sources)))
      opened <- liftEffect (Ref.read held)
      for_ opened \session -> runOnDisk (void (Client.close session))
      made <- liftEffect (Ref.read core)
      pure case outcome, made of
        Left failure, _ -> Left (show failure)
        Right (Left err), _ -> Left (joinWith "; " (map printBuildMessage (Array.fromFoldable (buildMessages err))))
        Right (Right _), Nothing -> Left "no Core of Main"
        Right (Right _), Just decls -> Right decls
  where
  runOnDisk :: forall a. Run (FS + PROCESS + AFF + EFFECT + ()) a -> Aff a
  runOnDisk p = p
    # FS.interpret Node.nodeFsHandler
    # Process.interpret development
    # runBaseAff'

moduleText :: ModuleName -> String
moduleText (ModuleName m) = m

-- | `A.one` as the host writes it: a goal filled with `1`.
hostRegistry :: Map.Map (Qualified Ident) F.Synthesizer
hostRegistry = Map.singleton (Qualified (ModuleName "A") (Ident "one")) \_ -> F.rootScope >>= \root -> F.literal root (LitInt 1)

said' :: Ran -> String -> Boolean
said' r text = Array.any (contains (Pattern text)) r.said

spec :: Spec Unit
spec = describe "stellac build of a synthesizer of the package" do
  -- `A` loads only after `Support`, which it imports, and a second load of
  -- either is refused by the session: two goals reaching `A.one` build only
  -- where each module is loaded in dependency order, and once
  it "runs it on the session for each goal of a module after it, its module and what it imports loaded in order, each once, and the program runs on the machine" do
    building "solved" "one" \r -> do
      r.result `shouldEqual` Right unit
      Array.take 3 r.said `shouldEqual`
        [ "[1/3] Compiling Support (stellac/.test-build/solved/src/Support.stel)"
        , "[2/3] Compiling A (stellac/.test-build/solved/src/A.stel)"
        , "[3/3] Compiling Main (stellac/.test-build/solved/src/Main.stel)"
        ]
      n <- valueOf r.dir [ "Support", "A", "Main" ] "n"
      m <- valueOf r.dir [ "Support", "A", "Main" ] "m"
      [ n, m ] `shouldEqual` [ "1", "1" ]

  it "gives the goal the term the host's synthesizer of the same policy gives it" do
    guest <- coreOfMain "guest" openingSynthesis
    host <- coreOfMain "host" \_ _ env id s -> pure (attemptJob env hostRegistry id s)
    case guest, host of
      Right g, Right h -> g `shouldEqual` h
      Left why, _ -> fail ("guest: " <> why)
      _, Left why -> fail ("host: " <> why)

  describe "fails" do
    it "where the synthesizer throws, as the program's error where the goal stands" do
      building "refused" "refusing" \r -> do
        r.result `shouldEqual` Left "The build failed"
        said' r "src/Main.stel:6:5: A synthesizer failed here" `shouldEqual` true

    it "where the synthesizer faults, against the synthesizer, neither the program's error nor the compiler's" do
      building "faulted" "faulty" \r -> do
        r.result `shouldEqual` Left "The build failed"
        said' r "src/Main.stel:6:5: The synthesizer `A.faulty` faulted while solving this goal: " `shouldEqual` true
        said' r "Internal compiler error" `shouldEqual` false

    it "where the synthesizer uses up its budget, against the synthesizer" do
      building "exhausted" "looping" \r -> do
        r.result `shouldEqual` Left "The build failed"
        said' r "src/Main.stel:6:5: The synthesizer `A.looping` exhausted its execution budget of 1,000,000 steps while solving this goal" `shouldEqual` true
        said' r "Internal compiler error" `shouldEqual` false
