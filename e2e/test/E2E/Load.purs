-- | `load`, over modules a compiler produced.
-- |
-- | Three modules are built from `fixtures/source/load`, `Base.Int` the one of
-- | `stella-packages/base`, and loaded. What the last step leaves in a global slot
-- | is the assertion — `Lib.add2 1 2`, initialized to `3` by the interpreter
-- | running the bytecode the build wrote.
-- |
-- | | Module | What it holds |
-- | | --- | --- |
-- | | `Base.Int` | `add`, which the interpreter carries out itself |
-- | | `Lib` | `add2`, a function of two; `one`, a value; and a data type |
-- | | `Main` | `result`, a saturated call to `Lib.add2` |
-- |
-- | The cases after that are refusals, each the same modules with one thing changed.
module Test.E2E.Load (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..), note)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Foreign (emptyTable)
import Steam.Load (LoadError(..), Store, emptyStore, globalNamed, load, moduleNamed, noIdentities)
import Steam.Value (Value(..))
import Stella.Compiler.Bytecode (Dmo)
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ConstIx(..), CtorIx(..), ForeignIx(..), Function, Instr(..), Reg(..), Tail(..))
import Stella.Compiler.Bytecode.Module (CalleeEntry(..), GlobalInit(..))
import Stella.Compiler.MiddleEnd.Rep (Rep(..))
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Stella.Compiler.TypedCore.Prim (primModule)
import E2E.Build (Sources, builtFrom)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- Names ------------------------------------------------------------------------------

intModuleName :: ModuleName
intModuleName = ModuleName "Base.Int"

libModuleName :: ModuleName
libModuleName = ModuleName "Lib"

mainModuleName :: ModuleName
mainModuleName = ModuleName "Main"

intAdd :: Qualified Ident
intAdd = Qualified intModuleName (Ident "add")

libAdd2 :: Qualified Ident
libAdd2 = Qualified libModuleName (Ident "add2")

libPair :: Qualified Ident
libPair = Qualified libModuleName (Ident "Pair")

libNothing :: Qualified Ident
libNothing = Qualified libModuleName (Ident "nothing")

libOne :: Qualified Ident
libOne = Qualified libModuleName (Ident "one")

mainResult :: Qualified Ident
mainResult = Qualified mainModuleName (Ident "result")

-- Building them --------------------------------------------------------------------

-- | The three modules built from their source, each picked out by its name.
compiled :: Sources -> Either P.String { int :: Dmo, lib :: Dmo, main :: Dmo }
compiled sources = do
  built <- builtFrom sources [ "load" ]
  let named n = note (show n <> " was not built") (Array.find (\d -> d.name == n) built)
  int <- named intModuleName
  lib <- named libModuleName
  main <- named mainModuleName
  pure { int, lib, main }

-- Loading them ----------------------------------------------------------------------

-- | A store nothing has been loaded into, with identity tables of its own.
fresh :: Effect Store
fresh = map (emptyStore emptyTable) (Ref.new noIdentities)

-- | Load the modules in the order given, or what refused one.
loading :: P.Array Dmo -> Aff (Either LoadError Store)
loading modules = liftEffect do
  store <- fresh
  runBaseEffect (Except.runExcept (Array.foldM load store modules))

-- | What a global of a loaded module holds.
valueOf :: Store -> Qualified Ident -> Aff (Maybe Value)
valueOf store name = liftEffect case globalNamed store name of
  Nothing -> pure Nothing
  Just slot -> Ref.read slot

spec :: Sources -> Spec Unit
spec sources = describe "Steam.Load" do

  describe "modules a compiler produced" do
    it "loads them in the order they are given, and initializes what they hold" do
      case compiled sources of
        Left err -> fail err
        Right dmos -> do
          outcome <- loading [ dmos.int, dmos.lib, dmos.main ]
          case outcome of
            Left err -> fail (show err)
            Right store -> do
              -- `Lib.add2 1 2`, run by the interpreter as the module loaded: the
              -- call reached Lib's function, which carried out `Base.Int.add`
              held <- valueOf store mainResult
              map holds held `shouldEqual` Just (AnInt 3)

    it "leaves a function global holding the closure it installs" do
      case compiled sources of
        Left err -> fail err
        Right dmos -> do
          outcome <- loading [ dmos.int, dmos.lib ]
          case outcome of
            Left err -> fail (show err)
            Right store -> do
              function <- valueOf store libAdd2
              value <- valueOf store libOne
              map holds function `shouldEqual` Just AClosure
              map holds value `shouldEqual` Just (AnInt 1)

    it "resolves `Prim.Unit`, which stands in no header" do
      case compiled sources of
        Left err -> fail err
        Right dmos -> do
          outcome <- loading [ dmos.int, dmos.lib ]
          case outcome of
            Left err -> fail (show err)
            Right store -> do
              value <- valueOf store libNothing
              map holds value `shouldEqual` Just (AData 0)

    it "holds each module under an identity of its own" do
      case compiled sources of
        Left err -> fail err
        Right dmos -> do
          outcome <- loading [ dmos.int, dmos.lib, dmos.main ]
          case outcome of
            Left err -> fail (show err)
            Right store -> do
              map (const unit) (moduleNamed store intModuleName) `shouldEqual` Just unit
              map (const unit) (moduleNamed store libModuleName) `shouldEqual` Just unit
              map (const unit) (moduleNamed store mainModuleName) `shouldEqual` Just unit

  describe "what loading refuses" do
    it "a module whose name is already loaded" do
      refusedBy sources (\dmos -> [ dmos.int, dmos.int ]) (ModuleTwice intModuleName)

    it "a module under the name the implicit environment holds" do
      -- `Prim` is Core's own vocabulary and no file declares it
      refusedBy sources (\dmos -> [ dmos.int { name = primModule } ])
        (ReservedModuleName primModule)

    it "an import that is not loaded" do
      -- Steam resolves no module: the order is the front end's
      refusedBy sources (\dmos -> [ dmos.int, dmos.main ]) (ImportNotLoaded libModuleName)

    it "a declaration whose name belongs to another module" do
      refusedBy sources
        ( \dmos ->
            [ dmos.int
            , dmos.lib
                { globals = map (\g -> g { name = Qualified mainModuleName (Ident "elsewhere") })
                    dmos.lib.globals
                }
            ]
        )
        (NotThisModule libModuleName (Qualified mainModuleName (Ident "elsewhere")))

    it "a constructor whose owner type belongs to another module" do
      refusedBy sources
        ( \dmos ->
            [ dmos.int
            , dmos.lib
                { ctors = map (\c -> c { owner = Qualified mainModuleName (TyName "Pair") })
                    dmos.lib.ctors
                }
            ]
        )
        (OwnerNotThisModule libModuleName (Qualified libModuleName (Ident "Pair")))

    it "two declarations of one name" do
      refusedBy sources
        ( \dmos ->
            [ dmos.int
            , dmos.lib { globals = dmos.lib.globals <> dmos.lib.globals }
            ]
        )
        (DeclaredTwice libAdd2)

    it "an exported name the module does not declare" do
      refusedBy sources
        ( \dmos ->
            [ dmos.int
            , dmos.lib { exports = dmos.lib.exports <> [ Qualified libModuleName (Ident "absent") ] }
            ]
        )
        (ExportNotDeclared (Qualified libModuleName (Ident "absent")))

    it "a reference to a name the declaring module does not export" do
      refusedBy sources
        ( \dmos ->
            [ dmos.int
            , dmos.lib { exports = [] }
            , dmos.main
            ]
        )
        (NotExported libAdd2)

    it "a known call whose arity the declaring module does not state" do
      -- `Lib.one` is evaluated at initialization and has no definitional arity, so
      -- a `CALLK` to it is a call no lowering produces
      refusedBy sources
        ( \dmos ->
            [ dmos.int
            , dmos.lib
            , dmos.main { globalRefs = map (const libOne) dmos.main.globalRefs }
            ]
        )
        (WrongCallArity libOne Nothing 2)

    it "a foreign nothing implements" do
      refusedBy sources
        ( \dmos ->
            [ dmos.int
                { foreigns = dmos.int.foreigns <>
                    [ { name: Qualified intModuleName (Ident "mystery"), arity: 1 } ]
                }
            ]
        )
        (ForeignWithoutImplementation (Qualified intModuleName (Ident "mystery")))

    -- **the refusal stands and cannot be reached from here.** This interpreter
    -- carries out every operation of `stella-base-0.1`, and a code outside the
    -- version is rejected where the file is decoded rather than here, so what is
    -- left to assert is the positive: naming one is not what refuses a module
    it "accepts an operation it does carry out, there being no other kind" do
      accepts sources (\dmos -> [ dmos.int, dmos.lib { prims = dmos.lib.prims <> [ ArrayUnsafeIndex ] } ])

    it "a global installed as a function whose function expects captures" do
      -- a `func` entry installs a closure over an empty capture list, so a function
      -- a global names captures nothing
      refusedBy sources
        ( \dmos ->
            [ dmos.int
            , dmos.lib
                { functions = map (\f -> f { captures = [ RepVal ] }) dmos.lib.functions }
            ]
        )
        (GlobalExpectsCaptures libAdd2 1)

  describe "what a header says a term may name" do
    it "refuses a reference to a module this one does not import" do
      -- the order modules were loaded in adds nothing to the header: `Base.Int` is
      -- loaded, and `Main` does not import it
      refusedBy sources
        ( \dmos ->
            [ dmos.int
            , dmos.lib
            , dmos.main { globalRefs = map (const intAdd) dmos.main.globalRefs }
            ]
        )
        (NotImported mainModuleName intAdd)

  describe "the arity a declaration states" do
    it "refuses a partial application that is not below it" do
      -- what a stale interface would produce, caught where the modules are together
      refusedBy sources (papFixture 2) (PapNotBelowArity libAdd2 2 2)

    it "admits one that is" do
      case compiled sources of
        Left err -> fail err
        Right dmos -> do
          outcome <- loading (papFixture 1 dmos)
          case outcome of
            Left err -> fail (show err)
            Right _ -> pure unit

    it "refuses a constructor applied to a count it does not take" do
      refusedBy sources
        ( \dmos ->
            [ dmos.int
            , dmos.lib
                { ctorRefs = [ libPair ]
                , functions = map (bodyOf (CTOR (Reg 1) (CtorIx 0) [ Reg 0, Reg 0 ])) dmos.lib.functions
                }
            ]
        )
        (WrongCtorArity libPair 1 2)

    it "refuses a foreign applied to a count it does not take" do
      refusedBy sources
        ( \dmos ->
            [ dmos.int
            , dmos.lib
                { foreignRefs = [ intAdd ]
                , functions = map (bodyOf (FFI (Reg 1) (ForeignIx 0) [ Reg 0 ])) dmos.lib.functions
                }
            ]
        )
        (WrongForeignArity intAdd 2 1)

  describe "how a global is installed" do
    it "refuses a function of no parameters installed as one" do
      -- a definitional arity counts leading lambdas and is at least one, so a value
      -- with none is evaluated at initialization instead
      refusedBy sources
        (\dmos -> [ dmos.int, dmos.lib { globals = map asFunction dmos.lib.globals } ])
        (FunctionGlobalWithoutParameters libOne)

  describe "what a refusal leaves behind" do
    it "nothing of the module it refused" do
      case compiled sources of
        Left err -> fail err
        Right dmos -> do
          outcome <- loading [ dmos.int, dmos.main ]
          case outcome of
            Right _ -> fail "the load was refused"
            Left _ -> pure unit

    it "a store the next module can be loaded against" do
      case compiled sources of
        Left err -> fail err
        Right dmos -> do
          result <- liftEffect do
            store <- fresh
            runBaseEffect
              ( Except.runExcept do
                  loaded <- load store dmos.int
                  -- Main cannot be loaded yet, and what that leaves is a store Lib
                  -- can be loaded against
                  refused <- Except.catch (\_ -> pure loaded) (load loaded dmos.main)
                  load refused dmos.lib
              )
          case result of
            Left err -> fail (show err)
            Right store -> do
              value <- valueOf store libOne
              map holds value `shouldEqual` Just (AnInt 1)

-- | Every function of a module with its body replaced by one instruction and a
-- | return, which is how a case puts one call under the loader's eye.
bodyOf :: Instr -> Function -> Function
bodyOf instruction function = function
  { body =
      { code: [ LOADK (Reg 0) (ConstIx 0), instruction ]
      , tail: RET (Reg 1)
      }
  }

-- | `Main` with its call replaced by a partial application of that many arguments
-- | over `Lib.add2`, whose arity is two.
papFixture :: P.Int -> { int :: Dmo, lib :: Dmo, main :: Dmo } -> P.Array Dmo
papFixture count dmos =
  [ dmos.int
  , dmos.lib
  , dmos.main
      { callees = [ CalleeValue libAdd2 ]
      , functions = map (bodyOf (PAP (Reg 1) (CalleeIx 0) (Array.replicate count (Reg 0))))
          dmos.main.functions
      }
  ]

-- | A global installed as a function, whichever it was.
asFunction :: forall a. { init :: GlobalInit | a } -> { init :: GlobalInit | a }
asFunction entry = entry { init = GFunc (funcOf entry.init) }
  where
  funcOf = case _ of
    GFunc ix -> ix
    GRun ix -> ix

-- | What a slot holds, as far as a test needs it.
data Held
  = AnInt P.Int
  | AClosure
  | AData P.Int
  | Elsewhere

holds :: Value -> Held
holds = case _ of
  VInt n -> AnInt n
  VClos _ -> AClosure
  VData _ fields -> AData (Array.length fields)
  _ -> Elsewhere

-- | That loading the modules a change produces is refused for that reason.
refusedBy
  :: Sources
  -> ({ int :: Dmo, lib :: Dmo, main :: Dmo } -> P.Array Dmo)
  -> LoadError
  -> Aff Unit
refusedBy sources change expected = case compiled sources of
  Left err -> fail err
  Right dmos -> do
    outcome <- loading (change dmos)
    map (const unit) outcome `shouldEqual` Left expected

-- | The same modules, changed the same way, and loaded rather than refused.
accepts :: Sources -> ({ int :: Dmo, lib :: Dmo, main :: Dmo } -> P.Array Dmo) -> Aff Unit
accepts sources change = case compiled sources of
  Left err -> fail err
  Right dmos -> do
    outcome <- loading (change dmos)
    map (const unit) outcome `shouldEqual` Right unit

derive instance Eq Held

instance Show Held where
  show = case _ of
    AnInt n -> "AnInt " <> show n
    AClosure -> "AClosure"
    AData n -> "AData " <> show n
    Elsewhere -> "Elsewhere"
