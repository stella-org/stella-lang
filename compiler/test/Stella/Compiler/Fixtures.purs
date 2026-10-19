-- | The bytecode fixtures: lowered modules every consumer of a `.dmo` runs, and
-- | what running them must give.
-- |
-- | A fixture is a directory of `fixtures/bytecode`, holding one `.dmo` per module
-- | and a `manifest.json` saying which modules load and in what order, whether they
-- | load or are refused where they load, what the named globals hold, and, for a
-- | fixture with an entry point, how running it ends and what effects the host saw.
-- | One whose modules declare a foreign a host supplies also holds the foreign
-- | manifest and the implementation module it points at. Steam and the JavaScript
-- | backend each read the bytes and check the manifest; neither lowers Core, which
-- | is the compiler's work.
-- |
-- | **The bytes are built from the sources under `fixtures/source` and the
-- | library packages they import, and must be what the compiler produces now.**
-- | The few fixtures the surface language cannot write are compiled from the Core
-- | in [Programs](Fixtures/Programs.purs), [Effects](Fixtures/Effects.purs),
-- | [Regions](Fixtures/Regions.purs), and [Foreigns](Fixtures/Foreigns.purs). The
-- | `.dmo` format is not frozen, so the check below fails wherever a fixture
-- | differs from what building its source gives today, and running the suite
-- | with `STELLA_UPDATE_FIXTURES=1` writes every fixture afresh instead.
module Test.Stella.Compiler.Fixtures
  ( spec
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldM, for_)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Stella.Compiler.Bytecode (Dmo, decode, encode, lower)
import Stella.Compiler.Interface (aritiesOf, importsOf)
import Data.Map (Map)
import Data.Set (Set)
import Data.Set as Set
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.Primitive (primTable)
import Stella.Compiler.TypedCore (Ident(..), Module, ModuleName(..), Qualified(..), declareAnnotated)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Stella.Compiler.Bytecode.Instr (CalleeIx(..), ForeignIx(..), Instr(..), KeyIx(..), Node, OpIx(..), PrimIx(..), Reg, Tail(..))
import Stella.Compiler.Bytecode.Module (CalleeEntry(..), HandlerEntry, RegionEntry)
import Stella.Compiler.MiddleEnd.IR (ClauseForm(..))
import Test.Stella.Compiler.Fixtures.Effects (effectsCoreExpected, effectsCoreModule, effectsSourceExpected)
import Test.Stella.Compiler.Fixtures.Regions (regionsCoreExpected, regionsCoreModule, regionsSourceExpected)
import Test.Stella.Compiler.Fixtures.Foreigns (ManifestModule, Result(..), RunCase, RunFault(..), addShrunkManifest, addShrunkSource, greetManifest, greetSource, deepIoResult, ioEffects, ioHostSource, ioManifest, ioName, hostName, ioModuleBindArity, ioModulePureArity, ioResult, runCases, runEffects, runHostSource, runManifest)
import Test.Stella.Compiler.Fixtures.Build (Sources, builtFrom, packageModules, readSources)
import Test.Stella.Compiler.Fixtures.Programs (abiSignature, coreOnlyExpected, coreOnlyModule, faultCases, sourceDeepExpected, sourceExpected, inInt, intModule, mainName, opsExpected)
import Test.Stella.Compiler.Fixtures.Value (Expected(..), jsonString, toJson)

-- Reading and writing --------------------------------------------------------------

foreign import fixturesRoot :: P.String
foreign import updating :: Effect P.Boolean
foreign import caseNames :: P.String -> Effect (P.Array P.String)
foreign import fileNames :: P.String -> Effect (P.Array P.String)
foreign import exists :: P.String -> Effect P.Boolean
foreign import readText :: P.String -> Effect P.String
foreign import readBytes :: P.String -> Effect (P.Array P.Int)
foreign import writeText :: P.String -> P.String -> Effect Unit
foreign import writeBytes :: P.String -> P.Array P.Int -> Effect Unit
foreign import removeTree :: P.String -> Effect Unit

-- Compiling ---------------------------------------------------------------------------

-- | A compiled module: its `.dmo`, and the arities its interface carries.
type Compiled = { dmo :: Dmo, dmi :: { name :: ModuleName, imports :: P.Array ModuleName, arities :: Map Ident P.Int } }

-- | Each module checked against the signatures before it and translated against
-- | the interfaces of those it imports, then carried through the container.
compileAll :: P.Array (Module P.Int) -> Either P.String (P.Array Compiled)
compileAll modules = _.out <$> foldM step { signature: abiSignature, dmis: [], out: [] } modules
  where
  step acc m = do
    declared <- stage "declare" (declareAnnotated acc.signature m)
    imports <- stage "interfaces" (importsOf acc.dmis)
    mid <- stage "translate" (translate imports m declared)
    lowered <- stage "lower" (lower mid)
    bytes <- stage "encode" (encode lowered.dmo)
    dmo <- stage "decode" (decode bytes)
    let dmi = { name: mid.module.name, imports: mid.module.imports, arities: aritiesOf mid.module }
    pure { signature: declared.signature, dmis: Array.snoc acc.dmis dmi, out: Array.snoc acc.out { dmo, dmi } }

stage :: forall e a. Show e => P.String -> Either e a -> Either P.String a
stage name = case _ of
  Left e -> Left (name <> ": " <> show e)
  Right a -> Right a

-- The fixtures -------------------------------------------------------------------------

data Outcome
  = Loads
  -- | Refused where the modules load, naming what is given.
  | RefusedAtLoad P.String
  -- | Faulting where the modules load, as the named global is initialized.
  | FaultsAtLoad P.String
  -- | Loading, and executing the action the entry global holds to the value it
  -- | produces, with the effects the host saw in order.
  | Runs { entry :: P.String, result :: Expected, effects :: P.Array P.String }
  -- | Loading, and executing the entry's action to a fault, with the effects the
  -- | host saw before it.
  | FaultsAtRun { entry :: P.String, fault :: RunFault, effects :: P.Array P.String }
  -- | Loading, and not starting: the entry names no global, or one holding no action.
  | StartFails { entry :: P.String, reason :: StartFailure }

data StartFailure
  = NoSuchGlobal
  | NotAnAction

-- | A foreign manifest, which generation checks against the modules' declarations
-- | unless it is one written to disagree with them.
data ForeignManifest
  = Checked (P.Array ManifestModule)
  | Unchecked (P.Array ManifestModule)

type Fixture =
  { name :: P.String
  , description :: P.String
  , modules :: Either P.String (P.Array Dmo)
  , outcome :: Outcome
  , observe :: P.Array (Tuple P.String Expected)
  , foreignManifest :: Maybe ForeignManifest
  -- | `host.mjs`, the implementation module the manifest points at.
  , host :: Maybe P.String
  }

-- | A fixture of no foreigns the host supplies.
plain
  :: { name :: P.String
     , description :: P.String
     , modules :: Either P.String (P.Array Dmo)
     , outcome :: Outcome
     , observe :: P.Array (Tuple P.String Expected)
     }
  -> Fixture
plain f =
  { name: f.name
  , description: f.description
  , modules: f.modules
  , outcome: f.outcome
  , observe: f.observe
  , foreignManifest: Nothing
  , host: Nothing
  }

fixtures :: Sources -> P.Array Fixture
fixtures sources =
  [ plain
      { name: "programs"
      , description: "Calls, tail calls, partial and over-application, closures, records, variants, literal dispatch on strings and characters, recursive groups, and references into another module"
      , modules: builtFrom sources [ "programs", "common-lib/lib", "common-lib/programs-main" ]
      , outcome: Loads
      , observe: sourceExpected
      }
  , plain
      { name: "programs-deep"
      , description: "The programs at the depths stack safety is tested at: a non-tail recursion 100000 deep, a self tail call a million times over, and a group of closures tail calling 100001 deep"
      , modules: builtFrom sources [ "programs-deep", "common-lib/lib", "common-lib/programs-main" ]
      , outcome: Loads
      , observe: sourceDeepExpected
      }
  , plain
      { name: "programs-core"
      , description: "What no source writes, in Core: a join point two leaves share and one jumping to itself, 100000 times over among them; restrict and merge; and a Number dispatch by literal identity"
      , modules: map (map _.dmo) (compileAll [ intModule, coreOnlyModule ])
      , outcome: Loads
      , observe: coreOnlyExpected
      }
  , plain
      { name: "stale-arity-call"
      , description: "Main calls Lib.addTo with the two arguments Lib's interface gave it, and is loaded beside a Lib whose addTo takes one"
      , modules: twoVersions sources [ "stale-arity-call/compiled", "common-lib/lib" ] [ "common-lib/lib-shrunk" ]
      , outcome: RefusedAtLoad "addTo"
      , observe: []
      }
  , plain
      { name: "stale-arity-partial"
      , description: "Main applies Lib.addTo to one argument, a partial application under the interface it was compiled against, beside a Lib whose addTo takes one"
      , modules: twoVersions sources [ "stale-arity-partial/compiled", "common-lib/lib" ] [ "common-lib/lib-shrunk" ]
      , outcome: RefusedAtLoad "addTo"
      , observe: []
      }
  , plain
      { name: "unexported-global"
      , description: "Main reads Lib.unbox as a value, beside a Lib that does not export it"
      , modules: twoVersions sources [ "common-lib/refs-main", "common-lib/lib" ] [ "unexported-global/loaded" ]
      , outcome: RefusedAtLoad "unbox"
      , observe: []
      }
  , plain
      { name: "undeclared-ctor"
      , description: "Main dispatches on Lib.Box, beside a Lib whose constructor is called Crate"
      , modules: twoVersions sources [ "common-lib/refs-main", "common-lib/lib" ] [ "undeclared-ctor/loaded" ]
      , outcome: RefusedAtLoad "Box"
      , observe: []
      }
  , plain
      { name: "operations"
      , description: "Every operation of stella-base-0.1, including inputs where a host's own operator gives another answer, and operations applied short of their arity and saturated later"
      , modules: builtFrom sources [ "operations" ]
      , outcome: Loads
      , observe: opsExpected
      }
  , plain
      { name: "effects"
      , description: "Handlers, perform in both clause forms, continuations resumed once and twice, cells carried in a continuation, and where a fast clause's body runs"
      , modules: builtFrom sources [ "effects" ]
      , outcome: Loads
      , observe: effectsSourceExpected
      }
  , plain
      { name: "effects-core"
      , description: "What no source writes, in Core: a continuation applied to two arguments, and one held captured while a second resumption runs through the same activation"
      , modules: map (map _.dmo) (compileAll [ intModule, effectsCoreModule ])
      , outcome: Loads
      , observe: effectsCoreExpected
      }
  , plain
      { name: "regions"
      , description: "Which region a cell reaches: two groups sharing the cells of one handling expression, a clause building a function over a cell, and a function opening a region of its own applied inside another declaring the same name"
      , modules: builtFrom sources [ "regions" ]
      , outcome: Loads
      , observe: regionsSourceExpected
      }
  , plain
      { name: "regions-core"
      , description: "What no source writes, in Core: which cells a resumption shares or copies, a computation reading the region around it inside and outside a handler resuming twice, a continuation resumed while a copy runs, and a closure made before a capture or carried through an operation; and a function opening a region applied inside its own clause, whose polymorphic recursion needs a written constraint"
      , modules: map (map _.dmo) (compileAll [ intModule, regionsCoreModule ])
      , outcome: Loads
      , observe: regionsCoreExpected
      }
  , meterRefusal sources "region-cell-twice"
      "the second cell of Main's region entry changed to the first, at the same KEYS index"
      (onRegions secondCellRepeats)
      "reading"
  , meterRefusal sources "region-cell-aliased"
      "the second cell of Main's region entry changed to the first, at a KEYS index of its own holding the same key"
      secondCellAliased
      "reading"
  , meterRefusal sources "handler-clause-twice"
      "the second clause of Main's handler entry changed to answer the first clause's operation, at the same OPS index"
      (onHandlers secondClauseRepeats)
      "bump"
  , meterRefusal sources "handler-clause-aliased"
      "the second clause of Main's handler entry changed to answer the first clause's operation, at an OPS index of its own holding the same name"
      secondClauseAliased
      "bump"
  , meterRefusal sources "handler-hndl-clauses"
      "a HNDL of Main given one clause fewer than its handler entry holds"
      (everyNode (onInstrs (onHndl dropClause)))
      "Meter"
  , meterRefusal sources "region-rgn-cells"
      "a RGN of Main given one initial cell value fewer than its region entry's cells"
      (everyNode (onInstrs (onRgn dropCell)))
      "reading"
  , meterRefusal sources "handler-tailhndl-clauses"
      "a TAILHNDL inside a branch of Main given one clause fewer than its handler entry holds"
      (everyNode (onTail (onTailHndl dropClause)))
      "Meter"
  , meterRefusal sources "region-tailrgn-cells"
      "a TAILRGN inside a branch of Main given one initial cell value fewer than its region entry's cells"
      (everyNode (onTail (onTailRgn dropCell)))
      "reading"
  ]
    <> map faultFixture faultCases
    <> foreignFixtures sources
  where
  faultFixture c = plain
    { name: c.name
    , description: c.description <> ", which faults as Main.faulted is initialized"
    , modules: builtFrom sources [ c.name ]
    , outcome: FaultsAtLoad "Main.faulted"
    , observe: []
    }

-- | The modules built from the first directories given, loaded beside those
-- | built from the second instead: a module of both is the second's alone,
-- | standing where the second build puts it.
twoVersions :: Sources -> P.Array P.String -> P.Array P.String -> Either P.String (P.Array Dmo)
twoVersions sources compiledFrom loadedFrom = do
  written <- builtFrom sources compiledFrom
  loaded <- builtFrom sources loadedFrom
  pure (loaded <> Array.filter (\d -> not (Array.elem d.name (map _.name loaded))) written)

-- Foreigns and running ---------------------------------------------------------------------

foreignFixtures :: Sources -> P.Array Fixture
foreignFixtures sources =
  [ { name: "io"
    , description: "An entry point run to the value it produces: actions a foreign returns, performed in order; a left-nested chain of bind 200 deep; every value kind crossing in and out, and an action of each kind; an opaque value handed back; a partial application of a foreign another module declares, and a foreign the entry module declares"
    , modules: builtFrom sources [ "io", "common-lib/io-host", "common-lib/io-main" ]
    , outcome: Runs { entry: "Main.main", result: ioResult, effects: ioEffects }
    , observe: []
    , foreignManifest: Just (Checked ioManifest)
    , host: Just ioHostSource
    }
  , { name: "io-deep"
    , description: "The entry point of io with its left-nested chain of bind 20000 deep, the depth stack safety is tested at"
    , modules: builtFrom sources [ "io-deep", "common-lib/io-host", "common-lib/io-main" ]
    , outcome: Runs { entry: "Main.main", result: deepIoResult, effects: ioEffects }
    , observe: []
    , foreignManifest: Just (Checked ioManifest)
    , host: Just ioHostSource
    }
  , plain
      { name: "io-pure"
      , description: "An entry point that is Base.IO.bind applied to pure 7 alone, and then to Base.IO.pure handed over unapplied, reaching no host"
      , modules: builtFrom sources [ "common-lib/io-pure" ]
      , outcome: Runs { entry: "Main.main", result: EInt 7, effects: [] }
      , observe: []
      }
  , plain
      { name: "start-no-global"
      , description: "An entry point naming a global Main does not declare"
      , modules: builtFrom sources [ "common-lib/start-main" ]
      , outcome: StartFails { entry: "Main.missing", reason: NoSuchGlobal }
      , observe: []
      }
  , plain
      { name: "start-not-an-action"
      , description: "An entry point naming a global of Main that holds an Int and no action"
      , modules: builtFrom sources [ "common-lib/start-main" ]
      , outcome: StartFails { entry: "Main.answer", reason: NotAnAction }
      , observe: []
      }
  , greetRefusal "foreign-unreachable" "a manifest pointing Host at a module that is not there"
      (Checked (greetManifest "./missing.mjs" [ greet ]))
      Nothing
      "missing.mjs"
  , greetRefusal "foreign-no-export" "an implementation module holding no export named greet"
      (Checked (greetManifest "./host.mjs" [ greet ]))
      (Just (greetSource [ Tuple "hello" "(n) => n" ]))
      "greet"
  , greetRefusal "foreign-not-callable" "an implementation module whose export greet is a number"
      (Checked (greetManifest "./host.mjs" [ greet ]))
      (Just (greetSource [ Tuple "greet" "41" ]))
      "greet"
  , greetRefusal "foreign-no-signature" "a manifest entry for Host that gives greet no signature"
      (Unchecked (greetManifest "./host.mjs" []))
      (Just greetImplementation)
      "greet"
  , greetRefusal "foreign-params-length" "a manifest giving greet two params where it is declared at arity one"
      (Unchecked (greetManifest "./host.mjs" [ greet { params = [ "int", "int" ] } ]))
      (Just greetImplementation)
      "greet"
  , plain
      { name: "foreign-no-entry"
      , description: "Host declares greet, and no manifest names Host"
      , modules: builtFrom sources [ "common-lib/greet" ]
      , outcome: RefusedAtLoad "greet"
      , observe: []
      }
  , plain
      { name: "io-entry-arity-pure"
      , description: "Base.IO declaring pure at arity two, where the runtime carries it out at arity one"
      , modules: map (map _.dmo) (compileAll [ ioModulePureArity ])
      , outcome: RefusedAtLoad "pure"
      , observe: []
      }
  , plain
      { name: "io-entry-arity-bind"
      , description: "Base.IO declaring bind at arity three, where the runtime carries it out at arity two"
      , modules: map (map _.dmo) (compileAll [ ioModuleBindArity ])
      , outcome: RefusedAtLoad "bind"
      , observe: []
      }
  , staleForeign "stale-foreign-call" "Main calls Host.add with the two arguments Host's interface gave it"
  , staleForeign "stale-foreign-call-inner" "Main calls Host.add with the two arguments Host's interface gave it, and puts what it gives in a record"
  , staleForeign "stale-foreign-partial" "Main applies Host.add to one argument, a partial application under the interface it was compiled against"
  , unexportedAfter sources "io-pure-unexported" "pure" "Main calls it, and stands over it unapplied in a partial application"
  , unexportedAfter sources "io-bind-unexported" "bind" "Main applies it short of its arity"
  , { name: "foreign-unexported"
    , description: "Main calls Host.greet, beside a Host changed after it was compiled to export nothing"
    , modules: map (map (unexporting (Qualified hostName (Ident "greet")))) (builtFrom sources [ "common-lib/greet" ])
    , outcome: RefusedAtLoad "greet"
    , observe: []
    , foreignManifest: Just (Checked (greetManifest "./host.mjs" [ greet ]))
    , host: Just greetImplementation
    }
  , plain
      { name: "operation-by-foreign"
      , description: "Main built from source and then changed to carry out Base.Int.add by calling the foreign Base.Int.add, where it used the operation"
      , modules: map (map callingOperation) (builtFrom sources [ "common-lib/op-call" ])
      , outcome: Loads
      , observe: [ Tuple "added" (EInt 3) ]
      }
  , plain
      { name: "operation-by-foreign-unexported"
      , description: "Main built from source and then changed to call the foreign Base.Int.add, beside a Base.Int changed to export nothing called add"
      , modules: map (map (unexporting (inInt "add") <<< callingOperation)) (builtFrom sources [ "common-lib/op-call" ])
      , outcome: RefusedAtLoad "add"
      , observe: []
      }
  ]
    <> map (runFixture sources) runCases
  where
  greet = { name: "greet", params: [ "int" ], result: Value "int" }

  greetImplementation = greetSource [ Tuple "greet" "(n) => n" ]

  greetRefusal name description manifest host mentions =
    { name
    , description: "Main calls Host.greet, beside " <> description
    , modules: builtFrom sources [ "common-lib/greet" ]
    , outcome: RefusedAtLoad mentions
    , observe: []
    , foreignManifest: Just manifest
    , host
    }

  staleForeign name description =
    { name
    , description: description <> ", and is loaded beside a Host whose add takes one"
    , modules: twoVersions sources [ name <> "/compiled", "common-lib/add-host" ] [ "common-lib/add-host-shrunk" ]
    , outcome: RefusedAtLoad "add"
    , observe: []
    , foreignManifest: Just (Checked addShrunkManifest)
    , host: Just addShrunkSource
    }

-- | The modules of `io-pure` with the named entry of `Base.IO` taken out of what it
-- | exports after `Main` was compiled against it: a foreign the runtime carries out
-- | is still a declaration of the module declaring it.
unexportedAfter :: Sources -> P.String -> P.String -> P.String -> Fixture
unexportedAfter sources name entry uses = plain
  { name
  , description: "Main compiled against Base.IO, beside a Base.IO changed to export nothing called " <> entry <> ", where " <> uses
  , modules: map (map (unexporting (Qualified ioName (Ident entry)))) (builtFrom sources [ "common-lib/io-pure" ])
  , outcome: RefusedAtLoad entry
  , observe: []
  }

-- | A module with the name taken out of what it exports.
unexporting :: Qualified Ident -> Dmo -> Dmo
unexporting q dmo = dmo { exports = Array.filter (_ /= q) dmo.exports }

-- | `Main` carrying out `Base.Int.add`, its one operation, by calling the foreign of
-- | that name instead.
callingOperation :: Dmo -> Dmo
callingOperation dmo =
  if dmo.name == mainName then (everyNode (onInstrs asCall) dmo) { prims = [], foreignRefs = [ inInt "add" ] }
  else dmo
  where
  asCall = case _ of
    PRIM d (PrimIx 0) args -> FFI d (ForeignIx 0) args
    other -> other

runFixture :: Sources -> RunCase -> Fixture
runFixture sources c =
  { name: c.name
  , description: "An entry point that runs Host.say and then reaches " <> c.description
  , modules: builtFrom sources [ "common-lib/run-" <> kind ]
  , outcome: FaultsAtRun { entry: "Main.main", fault: c.fault, effects: runEffects }
  , observe: []
  , foreignManifest: Just (Checked (runManifest c))
  , host: Just (runHostSource c)
  }
  where
  -- the kind of what the culprit owes, which names the sources its fixture shares
  kind = case c.culprit.result of
    Value k -> k
    Action _ -> "action"

-- | Where a checked manifest and the modules it describes disagree: a foreign one of
-- | the named modules declares without a signature, a signature whose `params` are
-- | not the declared arity long, or a signature naming nothing declared.
manifestDisagreements :: P.Array Dmo -> P.Array ManifestModule -> P.Array P.String
manifestDisagreements dmos = Array.concatMap perModule
  where
  perModule m = case Array.find (\d -> d.name == m.module) dmos of
    Nothing -> [ moduleText m.module <> " is not among the modules" ]
    Just dmo ->
      map (declared m) dmo.foreigns # Array.catMaybes
        # (_ <> Array.mapMaybe (undeclared dmo) m.foreigns)

  declared m entry =
    let
      Qualified (ModuleName mn) (Ident x) = entry.name
    in
      case Array.find (\s -> s.name == x) m.foreigns of
        Nothing -> Just (mn <> "." <> x <> " has no signature")
        Just s
          | Array.length s.params /= entry.arity -> Just (mn <> "." <> x <> " has params of another length than its arity")
          | otherwise -> Nothing

  undeclared dmo s =
    if Array.any (\entry -> entry.name == Qualified dmo.name (Ident s.name)) dmo.foreigns then Nothing
    else Just (moduleText dmo.name <> "." <> s.name <> " is declared nowhere")

foreignManifestText :: P.Array ManifestModule -> P.String
foreignManifestText modules = String.joinWith "\n"
  ( [ "{"
    , "  \"formatVersion\": 1,"
    , "  \"target\": \"javascript\","
    , "  \"modules\": ["
    ]
      <> Array.mapWithIndex entry modules
      <> [ "  ]", "}", "" ]
  )
  where
  entry i m =
    String.joinWith "\n"
      ( [ "    {\"module\": " <> jsonString (moduleText m.module) <> ", \"specifier\": " <> jsonString m.specifier <> ", \"foreigns\": [" ]
          <> Array.mapWithIndex (signature (Array.length m.foreigns)) m.foreigns
          <> [ "    ]}" <> comma i (Array.length modules) ]
      )

  signature n i s =
    "      {\"name\": " <> jsonString s.name
      <> ", \"params\": ["
      <> String.joinWith ", " (map jsonString s.params)
      <> "], \"result\": "
      <> resultJson s.result
      <> "}"
      <> comma i n

  resultJson = case _ of
    Value k -> jsonString k
    Action k -> "{\"action\": " <> jsonString k <> "}"

  comma i n = if i + 1 < n then "," else ""

-- Handler refusals -----------------------------------------------------------------------

-- | A module no Core compiles to, refused where it loads: `Meter` lowered, and then
-- | changed as `change` says. What is refused is a property of the module alone.
meterRefusal :: Sources -> P.String -> P.String -> (Dmo -> Dmo) -> P.String -> Fixture
meterRefusal sources name description change mentions = plain
  { name
  , description: "Main built from source and then " <> description
  , modules: map (map (\d -> if d.name == mainName then change d else d)) (builtFrom sources [ "common-lib/meter" ])
  , outcome: RefusedAtLoad mentions
  , observe: []
  }

onHandlers :: (HandlerEntry -> HandlerEntry) -> Dmo -> Dmo
onHandlers f dmo = dmo { handlers = map f dmo.handlers }

onRegions :: (RegionEntry -> RegionEntry) -> Dmo -> Dmo
onRegions f dmo = dmo { regions = map f dmo.regions }

-- | The first cell standing for the second, at its own index.
secondCellRepeats :: RegionEntry -> RegionEntry
secondCellRepeats r = r { cells = Array.take 1 r.cells <> Array.take 1 r.cells }

-- | The first cell standing for the second, at a new index of `KEYS` holding the
-- | same key. Two indices of one key are one identity.
secondCellAliased :: Dmo -> Dmo
secondCellAliased dmo = case Array.head dmo.regions >>= \r -> Array.head r.cells of
  Just (KeyIx i) | Just key <- Array.index dmo.keys i ->
    onRegions (\r -> r { cells = Array.take 1 r.cells <> [ KeyIx (Array.length dmo.keys) ] })
      (dmo { keys = Array.snoc dmo.keys key })
  _ -> dmo

secondClauseRepeats :: HandlerEntry -> HandlerEntry
secondClauseRepeats h = h { opClauses = Array.take 1 h.opClauses <> map (\c -> c { form = form }) (Array.take 1 h.opClauses) }
  where
  form = maybe ClauseFast _.form (Array.index h.opClauses 1)

secondClauseAliased :: Dmo -> Dmo
secondClauseAliased dmo = case Array.head dmo.handlers >>= \h -> Array.head h.opClauses of
  Just { op: OpIx i } | Just name <- Array.index dmo.ops i ->
    onHandlers
      (\h -> h { opClauses = Array.take 1 h.opClauses <> map (_ { op = OpIx (Array.length dmo.ops) }) (Array.slice 1 2 h.opClauses) })
      (dmo { ops = Array.snoc dmo.ops name })
  _ -> dmo

-- | Every node of every function changed by `f`: a function's body, each join
-- | point's, and each a branch holds inline.
everyNode :: (Node -> Node) -> Dmo -> Dmo
everyNode f dmo = dmo { functions = map function dmo.functions }
  where
  function fn = fn { body = node fn.body, joins = map (\j -> j { body = node j.body }) fn.joins }

  node n = f (n { tail = inline n.tail })

  inline = case _ of
    BRIF s a b -> BRIF s (node a) (node b)
    BRC s cases fallback -> BRC s (map (\c -> c { body = node c.body }) cases) (map node fallback)
    BRL s cases fallback -> BRL s (map (\c -> c { body = node c.body }) cases) (node fallback)
    BRK s cases fallback -> BRK s (map (\c -> c { body = node c.body }) cases) (map node fallback)
    other -> other

onInstrs :: (Instr -> Instr) -> Node -> Node
onInstrs f n = n { code = map f n.code }

onTail :: (Tail -> Tail) -> Node -> Node
onTail f n = n { tail = f n.tail }

onHndl :: (P.Array Reg -> P.Array Reg) -> Instr -> Instr
onHndl f = case _ of
  HNDL d ix body ret clauses -> HNDL d ix body ret (f clauses)
  other -> other

onTailHndl :: (P.Array Reg -> P.Array Reg) -> Tail -> Tail
onTailHndl f = case _ of
  TAILHNDL ix body ret clauses -> TAILHNDL ix body ret (f clauses)
  other -> other

onRgn :: (P.Array Reg -> P.Array Reg) -> Instr -> Instr
onRgn f = case _ of
  RGN d ix body initial -> RGN d ix body (f initial)
  other -> other

onTailRgn :: (P.Array Reg -> P.Array Reg) -> Tail -> Tail
onTailRgn f = case _ of
  TAILRGN ix body initial -> TAILRGN ix body (f initial)
  other -> other

-- | The last clause, or the last initial value, left out.
dropClause :: P.Array Reg -> P.Array Reg
dropClause = Array.dropEnd 1

dropCell :: P.Array Reg -> P.Array Reg
dropCell = Array.dropEnd 1

-- | The foreign and the count of each partial application over a foreign that a
-- | module makes.
foreignPartials :: Dmo -> P.Array (Tuple P.String P.Int)
foreignPartials dmo = Array.mapMaybe partial (instructionsOf dmo)
  where
  partial = case _ of
    PAP _ (CalleeIx i) args | Just (CalleeForeign (Qualified (ModuleName m) (Ident x))) <- Array.index dmo.callees i ->
      Just (Tuple (m <> "." <> x) (Array.length args))
    _ -> Nothing

-- | Every instruction of every function of a module.
instructionsOf :: Dmo -> P.Array Instr
instructionsOf dmo = Array.concatMap _.code (nodesOf dmo)

-- | The name of every kind of instruction and of tail a module's functions hold,
-- | as `LOADK` and `RET`.
kindsOf :: Dmo -> Set P.String
kindsOf dmo = Set.fromFoldable (map (nameOf <<< show) (instructionsOf dmo) <> map (nameOf <<< show <<< _.tail) (nodesOf dmo))
  where
  nameOf s = fromMaybe s (Array.head (String.split (String.Pattern " ") (fromMaybe s (String.stripPrefix (String.Pattern "(") s))))

-- | Every node of every function of a module: a function's body, each join
-- | point's, and each node a branch holds inline.
nodesOf :: Dmo -> P.Array Node
nodesOf dmo = Array.concatMap function dmo.functions
  where
  function fn = node fn.body <> Array.concatMap (\j -> node j.body) fn.joins

  node n = [ n ] <> inline n.tail

  inline = case _ of
    BRIF _ a b -> node a <> node b
    BRC _ cases fallback -> Array.concatMap (\c -> node c.body) cases <> maybe [] node fallback
    BRL _ cases fallback -> Array.concatMap (\c -> node c.body) cases <> node fallback
    BRK _ cases fallback -> Array.concatMap (\c -> node c.body) cases <> maybe [] node fallback
    _ -> []

-- The manifest -----------------------------------------------------------------------------

manifestText :: Fixture -> P.Array Dmo -> P.String
manifestText f dmos = String.joinWith "\n"
  ( [ "{"
    , "  \"description\": " <> jsonString f.description <> ","
    , "  \"modules\": [" <> String.joinWith ", " (map (\d -> jsonString (moduleText d.name)) dmos) <> "],"
    , "  \"outcome\": " <> outcomeJson <> ","
    ]
      <> observeLines
      <> [ "}", "" ]
  )
  where
  -- one observed global per line, so a changed value is a changed line
  observeLines =
    if Array.null f.observe then [ "  \"observe\": []" ]
    else [ "  \"observe\": [" ] <> Array.mapWithIndex observed f.observe <> [ "  ]" ]

  outcomeJson = case f.outcome of
    Loads -> "{\"loads\": true}"
    RefusedAtLoad name -> "{\"refusedAtLoad\": {\"mentions\": " <> jsonString name <> "}}"
    FaultsAtLoad global -> "{\"faultsAtLoad\": {\"global\": " <> jsonString global <> "}}"
    Runs r ->
      "{\"runs\": {\"entry\": " <> jsonString r.entry
        <> ", \"result\": "
        <> toJson r.result
        <> ", \"effects\": "
        <> effectsJson r.effects
        <> "}}"
    FaultsAtRun r ->
      "{\"faultsAtRun\": {\"entry\": " <> jsonString r.entry
        <> ", "
        <> faultJson r.fault
        <> ", \"effects\": "
        <> effectsJson r.effects
        <> "}}"
    StartFails r ->
      "{\"startFails\": {\"entry\": " <> jsonString r.entry <> ", \"reason\": "
        <> jsonString case r.reason of
          NoSuchGlobal -> "noSuchGlobal"
          NotAnAction -> "notAnAction"
        <> "}}"

  -- one effect per line, so a changed sequence is a changed line
  effectsJson effects =
    if Array.null effects then "[]"
    else "[\n" <> String.joinWith ",\n" (map (\e -> "    " <> jsonString e) effects) <> "\n  ]"

  -- the kind, and what both runtimes observe of a fault of that kind
  faultJson = case _ of
    Refused culprit reason -> kind "refused" <> ", \"foreign\": " <> jsonString culprit <> ", \"reason\": " <> jsonString reason
    Threw culprit message -> kind "threw" <> ", \"foreign\": " <> jsonString culprit <> ", \"message\": " <> jsonString message
    Breached culprit -> kind "breached" <> ", \"foreign\": " <> jsonString culprit
    ActionRefused reason -> kind "actionRefused" <> ", \"reason\": " <> jsonString reason
    ActionThrew message -> kind "actionThrew" <> ", \"message\": " <> jsonString message
    ActionBreached culprit -> kind "actionBreached" <> ", \"foreign\": " <> jsonString culprit

  kind k = "\"kind\": " <> jsonString k

  observed i (Tuple name value) =
    let
      Qualified (ModuleName m) (Ident x) = Qualified mainName (Ident name)
      comma = if i + 1 < Array.length f.observe then "," else ""
    in
      "    {\"global\": " <> jsonString (m <> "." <> x) <> ", \"value\": " <> toJson value <> "}" <> comma

moduleText :: ModuleName -> P.String
moduleText (ModuleName m) = m

-- | Every file a fixture's directory holds, by name, as it is written.
data Content
  = Text P.String
  | Bytes (P.Array P.Int)

filesOf :: Fixture -> Either P.String (P.Array (Tuple P.String Content))
filesOf f = do
  dmos <- f.modules
  encoded <- traverse (\d -> stage "encode" (encode d) <#> \bytes -> Tuple (moduleText d.name <> ".dmo") (Bytes bytes)) dmos
  foreignManifest <- case f.foreignManifest of
    Nothing -> pure []
    Just (Unchecked modules) -> pure [ Tuple "foreign-manifest.json" (Text (foreignManifestText modules)) ]
    Just (Checked modules) -> case manifestDisagreements dmos modules of
      [] -> pure [ Tuple "foreign-manifest.json" (Text (foreignManifestText modules)) ]
      disagreements -> Left (f.name <> ": the foreign manifest disagrees with the modules: " <> String.joinWith "; " disagreements)
  pure
    ( encoded
        <> [ Tuple "manifest.json" (Text (manifestText f dmos)) ]
        <> foreignManifest
        <> maybe [] (\source -> [ Tuple "host.mjs" (Text source) ]) f.host
    )

-- The check ------------------------------------------------------------------------------

-- | What source-built fixtures lower to: of the modules the directories given
-- | build, the one named holds every kind of instruction and tail listed. A
-- | fixture exercises the bytecode it holds, so a change to lowering that keeps
-- | its values and drops one of these is caught here, and not regenerated away.
lowersTo :: P.Array { dirs :: P.Array P.String, module :: P.String, kinds :: P.Array P.String }
lowersTo =
  -- known, unknown, and partial calls; closures, and recursive groups of them;
  -- by-need cells; dispatches on constructors, literals, and keys; records,
  -- a pattern's rest among them, and variants
  [ { dirs: [ "programs", "common-lib/lib", "common-lib/programs-main" ]
    , module: "Main"
    , kinds: [ "CALLK", "TAILK", "CALLU", "TAILU", "PAP", "CLOS", "CAPT", "CLOSN", "SETCAP", "NEED", "FORCE", "BRC", "BRL", "BRK", "CTOR", "FIELD", "RNEW", "REXT", "RSEL", "RRES", "RUPD", "VINJ", "VPAY" ]
    }
  -- an operation applied short of its arity
  , { dirs: [ "operations" ], module: "Main", kinds: [ "PRIM", "PAP" ] }
  -- operations performed, handlers and regions in tail position, and cells
  , { dirs: [ "effects" ], module: "Main", kinds: [ "PERF", "TAILHNDL", "TAILRGN", "CGET", "CSET" ] }
  , { dirs: [ "regions" ], module: "Main", kinds: [ "PERF", "TAILHNDL", "TAILRGN", "CGET", "CSET" ] }
  -- what the handler and region refusals change: an entry of each consumed and
  -- of each in tail position
  , { dirs: [ "common-lib/meter" ], module: "Main", kinds: [ "HNDL", "RGN", "TAILHNDL", "TAILRGN" ] }
  -- foreigns called, in tail position and not, and applied short of their arity
  , { dirs: [ "io", "common-lib/io-host", "common-lib/io-main" ], module: "Main", kinds: [ "FFI", "TAILFFI", "PAP" ] }
  , { dirs: [ "common-lib/io-pure" ], module: "Main", kinds: [ "FFI", "PAP" ] }
  -- the calls the stale fixtures load against an interface that has changed
  , { dirs: [ "stale-arity-call/compiled", "common-lib/lib" ], module: "Main", kinds: [ "TAILK" ] }
  , { dirs: [ "stale-arity-partial/compiled", "common-lib/lib" ], module: "Main", kinds: [ "PAP" ] }
  , { dirs: [ "stale-foreign-call/compiled", "common-lib/add-host" ], module: "Main", kinds: [ "TAILFFI" ] }
  , { dirs: [ "stale-foreign-call-inner/compiled", "common-lib/add-host" ], module: "Main", kinds: [ "FFI" ] }
  , { dirs: [ "stale-foreign-partial/compiled", "common-lib/add-host" ], module: "Main", kinds: [ "PAP" ] }
  ]

-- | The sources read and prepared, given to `k`, or a failure saying why they
-- | could not be.
withSources :: (Sources -> Aff Unit) -> Aff Unit
withSources k = liftEffect readSources >>= either fail k

spec :: Spec Unit
spec = describe "the bytecode fixtures" do
  -- `PRIMS` is the set of operations a module carries out, so an operation the
  -- version holds and the fixture never uses is one no backend is checked on
  it "carry out every operation of the version in the operations fixture" do
    withSources \sources -> case builtFrom sources [ "operations" ] of
      Left err -> fail err
      Right built -> case Array.last built of
        Nothing -> fail "nothing compiled"
        Just main ->
          Array.filter (\entry -> not (Array.elem entry.op main.prims)) primTable
            <#> (\entry -> show entry.op)
            # (_ `shouldEqual` [])

  -- the two `Base.IO` entries are carried out by the runtime and not by a host, so a
  -- partial application over one is of its own kind: `bind` short of its arity, and
  -- `pure` as a value, which is a partial application of no arguments
  it "apply both Base.IO entries short of their arity in the io-pure fixture" do
    withSources \sources -> case builtFrom sources [ "common-lib/io-pure" ] of
      Left err -> fail err
      Right built -> map foreignPartials (Array.last built)
        `shouldEqual` Just [ Tuple "Base.IO.bind" 1, Tuple "Base.IO.pure" 0 ]

  it "lower to the instructions each is to exercise" do
    withSources \sources -> for_ lowersTo \l -> case builtFrom sources l.dirs of
      Left err -> fail err
      Right built -> case Array.find (\d -> d.name == ModuleName l.module) built of
        Nothing -> fail (l.module <> " is not built from " <> String.joinWith ", " l.dirs)
        Just dmo -> Tuple l.dirs (Array.filter (\k -> not (Set.member k (kindsOf dmo))) l.kinds) `shouldEqual` Tuple l.dirs []

  -- a package's module is built only where a fixture reaches it, so one no
  -- fixture reaches could be missing or broken unseen
  it "reach every module of the lists and maybe packages" do
    withSources \sources -> case traverse _.modules (fixtures sources) of
      Left err -> fail err
      Right built -> do
        let reached = Set.fromFoldable (map _.name (Array.concat built))
        Array.filter (\m -> not (Set.member m reached)) (Array.concatMap (packageModules sources) [ "lists", "maybe" ]) `shouldEqual` []

  it "are what compiling their source gives now" do
    update <- liftEffect updating
    withSources \sources -> case traverse (\f -> map (Tuple f.name) (filesOf f)) (fixtures sources) of
      Left err -> fail err
      Right wanted ->
        if update then liftEffect (write wanted)
        else do
          stale <- liftEffect (differences wanted)
          when (not (Array.null stale))
            (fail ("stale fixtures, regenerate with STELLA_UPDATE_FIXTURES=1: " <> String.joinWith ", " stale))
          stale `shouldEqual` []

write :: P.Array (Tuple P.String (P.Array (Tuple P.String Content))) -> Effect Unit
write wanted = do
  present <- caseNames fixturesRoot
  for_ present \name -> when (not (Array.elem name (map fst' wanted))) (removeTree (fixturesRoot <> name))
  for_ wanted \(Tuple name files) -> do
    removeTree (fixturesRoot <> name)
    for_ files \(Tuple file content) -> case content of
      Text t -> writeText (fixturesRoot <> name <> "/" <> file) t
      Bytes b -> writeBytes (fixturesRoot <> name <> "/" <> file) b
  where
  fst' (Tuple a _) = a

-- | Every fixture, and every file of one, that is missing, surplus, or other than
-- | what compiling its source gives.
differences :: P.Array (Tuple P.String (P.Array (Tuple P.String Content))) -> Effect (P.Array P.String)
differences wanted = do
  present <- caseNames fixturesRoot
  let
    surplus = Array.filter (\name -> not (Array.elem name (map (\(Tuple n _) -> n) wanted))) present
  perCase <- traverse caseDifferences wanted
  pure (map (_ <> " (surplus)") surplus <> Array.concat perCase)
  where
  caseDifferences (Tuple name files) = do
    let dir = fixturesRoot <> name <> "/"
    onDisk <- fileNames dir
    let
      extra = Array.filter (\file -> not (Array.elem file (map (\(Tuple n _) -> n) files))) onDisk
    changed <- traverse (fileDifference dir name) files
    pure (map (\file -> name <> "/" <> file <> " (surplus)") extra <> Array.catMaybes changed)

  fileDifference dir name (Tuple file content) = do
    let path = dir <> file
    present <- exists path
    if not present then pure (Just (name <> "/" <> file <> " (missing)"))
    else case content of
      Text t -> do
        onDisk <- readText path
        pure if onDisk == t then Nothing else Just (name <> "/" <> file)
      Bytes b -> do
        onDisk <- readBytes path
        pure if onDisk == b then Nothing else Just (name <> "/" <> file)
