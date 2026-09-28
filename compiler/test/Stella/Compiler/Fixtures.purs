-- | The bytecode fixtures: lowered modules every consumer of a `.dmo` runs, and
-- | what running them must give.
-- |
-- | A fixture is a directory of `fixtures/bytecode`, holding one `.dmo` per module
-- | and a `manifest.json` saying which modules load and in what order, whether they
-- | load or are refused where they load, and what the named globals hold. Steam and
-- | the JavaScript backend each read the bytes and check the manifest; neither
-- | lowers Core, which is the compiler's work.
-- |
-- | **The bytes are compiled from the Core in [Programs](Fixtures/Programs.purs)
-- | and must be what the compiler produces now.** The `.dmo` format is not frozen,
-- | so the check below fails wherever a fixture differs from what compiling its
-- | source gives today, and running the suite with `STELLA_UPDATE_FIXTURES=1`
-- | writes every fixture afresh instead.
module Test.Stella.Compiler.Fixtures
  ( Compiled
  , Manifest
  , compileAll
  , fixturesRoot
  , caseNames
  , readManifest
  , readBytes
  , spec
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, for_)
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Stella.Compiler.Bytecode (Dmo, decode, encode, lower)
import Stella.Compiler.Interface (Dmi, importsOf, interfaceOf)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.Primitive (primTable)
import Stella.Compiler.TypedCore (Ident(..), Module, ModuleName(..), Qualified(..), declareAnnotated)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.Fixtures.Programs (abiSignature, baseModules, expected, faultCases, faultModule, intModule, libModule, libRenamed, libShrunk, libUnexported, mainModule, mainName, opsExpected, opsModule, refsOnly, without)
import Test.Stella.Compiler.Fixtures.Value (Expected(..), ExpectedKey(..), jsonString, toJson)

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

foreign import parseManifestImpl
  :: { int :: P.Int -> Expected
     , number :: P.Number -> Expected
     , char :: P.Int -> Expected
     , string :: P.String -> Expected
     , boolean :: P.Boolean -> Expected
     , data :: P.String -> P.Array Expected -> Expected
     , record :: P.Array { key :: ExpectedKey, value :: Expected } -> Expected
     , variant :: ExpectedKey -> Expected -> Expected
     , fn :: Expected
     , field :: P.String -> ExpectedKey
     , tag :: P.String -> ExpectedKey
     , position :: P.Int -> ExpectedKey
     , effect :: P.String -> ExpectedKey
     }
  -> P.String
  -> Manifest

-- | A fixture's manifest. `mentions` is what a refusal names where `loads` is
-- | false.
type Manifest =
  { description :: P.String
  , modules :: P.Array P.String
  , loads :: P.Boolean
  , mentions :: P.String
  , faults :: P.String
  , observe :: P.Array { global :: P.String, value :: Expected }
  }

readManifest :: P.String -> Effect Manifest
readManifest name = map (parseManifestImpl constructors) (readText (fixturesRoot <> name <> "/manifest.json"))
  where
  constructors =
    { int: EInt
    , number: ENumber
    , char: EChar
    , string: EString
    , boolean: EBoolean
    , data: EData
    , record: ERecord
    , variant: EVariant
    , fn: EFunction
    , field: KField
    , tag: KTag
    , position: KPosition
    , effect: KEffect
    }

-- Compiling ---------------------------------------------------------------------------

type Compiled = { dmo :: Dmo, dmi :: Dmi }

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
    let dmi = interfaceOf mid.module
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

type Fixture =
  { name :: P.String
  , description :: P.String
  , modules :: Either P.String (P.Array Dmo)
  , outcome :: Outcome
  , observe :: P.Array (Tuple P.String Expected)
  }

fixtures :: P.Array Fixture
fixtures =
  [ { name: "programs"
    , description: "Calls, tail calls, partial and over-application, closures, join points, records, variants, literal dispatch, and references into another module"
    , modules: map (map _.dmo) (compileAll [ intModule, libModule, mainModule ])
    , outcome: Loads
    , observe: expected
    }
  , { name: "stale-arity-call"
    , description: "Main calls Lib.addTo with the two arguments Lib's interface gave it, and is loaded beside a Lib whose addTo takes one"
    , modules: against (without "addPartial") libShrunk
    , outcome: RefusedAtLoad "addTo"
    , observe: []
    }
  , { name: "stale-arity-partial"
    , description: "Main applies Lib.addTo to one argument, a partial application under the interface it was compiled against, beside a Lib whose addTo takes one"
    , modules: against (without "addCalled") libShrunk
    , outcome: RefusedAtLoad "addTo"
    , observe: []
    }
  , { name: "unexported-global"
    , description: "Main reads Lib.unbox as a value, beside a Lib that does not export it"
    , modules: against refsOnly libUnexported
    , outcome: RefusedAtLoad "unbox"
    , observe: []
    }
  , { name: "undeclared-ctor"
    , description: "Main dispatches on Lib.Box, beside a Lib whose constructor is called Crate"
    , modules: against refsOnly libRenamed
    , outcome: RefusedAtLoad "Box"
    , observe: []
    }
  , { name: "operations"
    , description: "Every operation of stella-base-0.1, including inputs where a host's own operator gives another answer, and operations applied short of their arity and saturated later"
    , modules: map (map _.dmo) (compileAll (baseModules <> [ opsModule ]))
    , outcome: Loads
    , observe: opsExpected
    }
  ]
    <> map faultFixture faultCases
  where
  faultFixture c =
    { name: c.name
    , description: c.description <> ", which faults as Main.faulted is initialized"
    , modules: map (map _.dmo) (compileAll (baseModules <> [ faultModule c ]))
    , outcome: FaultsAtLoad "Main.faulted"
    , observe: []
    }

-- | `main` compiled against `Lib` as written, loaded beside `lib` instead.
against :: Module P.Int -> Module P.Int -> Either P.String (P.Array Dmo)
against main lib = do
  written <- compileAll [ intModule, libModule, main ]
  changed <- compileAll [ intModule, lib ]
  pure (map _.dmo changed <> map _.dmo (Array.drop 2 written))

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
  pure (encoded <> [ Tuple "manifest.json" (Text (manifestText f dmos)) ])

-- The check ------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "the bytecode fixtures" do
  -- `PRIMS` is the set of operations a module carries out, so an operation the
  -- version holds and the fixture never uses is one no backend is checked on
  it "carry out every operation of the version in the operations fixture" do
    case compileAll (baseModules <> [ opsModule ]) of
      Left err -> fail err
      Right compiled -> case Array.last compiled of
        Nothing -> fail "nothing compiled"
        Just main ->
          Array.filter (\entry -> not (Array.elem entry.op main.dmo.prims)) primTable
            <#> (\entry -> show entry.op)
            # (_ `shouldEqual` [])

  it "are what compiling their source gives now" do
    update <- liftEffect updating
    case traverse (\f -> map (Tuple f.name) (filesOf f)) fixtures of
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
