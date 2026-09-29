-- | The JavaScript backend: the bytecode fixtures generated and run in Node, and
-- | what only this backend does — the code it generates, what it refuses before
-- | generating, and the preconditions its runtime checks.
-- |
-- | **Everything here starts from a `.dmo`**, read from `fixtures/bytecode` as a
-- | backend outside this compiler would read one
-- | ([Fixtures](../../../../fixtures/bytecode/README.md)). A fixture's modules are
-- | generated one ES module each, written out, and the last imported; what its
-- | exports hold, or how loading ended, is checked against the fixture's manifest.
-- | For a fixture with an entry point, the module holding it exports it, and that
-- | module is imported and the action executed as a host starting the program
-- | does; how that ends, and the effects the fixture's host saw, are checked. Each
-- | module declaring a foreign a host implements is given its entry in the fixture's
-- | foreign manifest, the specifier resolved against the fixture's directory.
-- | Steam checks the same manifests, so the two agree wherever both pass. The cases
-- | only this backend has are made by changing a decoded fixture, so no test here
-- | reaches above the `.dmo`.
-- |
-- | JavaScript holds an `Int`, a `Number`, and a `Char` alike as a number, so each is
-- | compared by the number it is; a function is compared as being one.
module Test.Stella.Backend.JavaScript (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (and)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Effect.Class (liftEffect)
import Stella.Backend.JavaScript (JsError(..), Options, fileName, generate)
import Stella.Compiler.ForeignManifest as ForeignManifest
import Stella.Compiler.Bytecode (Dmo, EncodeError(..), FuncIx(..), GlobalInit(..), Instr(..), decode, encode)
import Stella.Compiler.Bytecode as B
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- Reading the fixtures -------------------------------------------------------------------

foreign import fixturesRoot :: P.String
foreign import caseNames :: P.String -> Effect (P.Array P.String)
foreign import readText :: P.String -> Effect P.String
foreign import exists :: P.String -> Effect P.Boolean
foreign import readBytes :: P.String -> Effect (P.Array P.Int)
foreign import resolveSpecifier :: P.String -> P.String -> P.String

-- | The `specifier` of the named module's entry in the foreign manifest at that
-- | path, as written, or `""`.
foreign import specifierIn :: P.String -> P.String -> P.String

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
     , produces :: Expected -> P.Array P.String -> RunEnd
     , faultsWith :: ExpectedFault -> P.Array P.String -> RunEnd
     , failsToStart :: P.String -> RunEnd
     , just :: Run -> Maybe Run
     , nothing :: Maybe Run
     }
  -> P.String
  -> Manifest

-- | A fixture's manifest. `loads` holds for a fixture whose modules all load,
-- | whether or not it goes on to run an entry point; `mentions` is what a refusal
-- | names, and `faults` the global whose initialization a fault ends, each `""`
-- | where it does not apply.
type Manifest =
  { description :: P.String
  , modules :: P.Array P.String
  , loads :: P.Boolean
  , mentions :: P.String
  , faults :: P.String
  , observe :: P.Array { global :: P.String, value :: Expected }
  , run :: Maybe Run
  }

-- | An entry point, as `Mod.name`, and how running it ends.
type Run = { entry :: P.String, end :: RunEnd }

data RunEnd
  -- | Producing the value, with the effects in order.
  = Produces Expected (P.Array P.String)
  -- | Faulting, with the effects before the fault.
  | FaultsWith ExpectedFault (P.Array P.String)
  -- | Not starting, as `noSuchGlobal` or `notAnAction`.
  | FailsToStart P.String

-- | A fault's kind and what is observed of it; a field the kind does not carry is
-- | `""`.
type ExpectedFault = { kind :: P.String, foreign :: P.String, reason :: P.String, message :: P.String }

-- | What a manifest says a value is.
data Expected
  = EInt P.Int
  | ENumber P.Number
  | EChar P.Int
  | EString P.String
  | EBoolean P.Boolean
  | EData P.String (P.Array Expected)
  | ERecord (P.Array { key :: ExpectedKey, value :: Expected })
  | EVariant ExpectedKey Expected
  | EFunction

data ExpectedKey
  = KField P.String
  | KTag P.String
  | KPosition P.Int
  | KEffect P.String

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
    , produces: Produces
    , faultsWith: FaultsWith
    , failsToStart: FailsToStart
    , just: Just
    , nothing: Nothing
    }

-- | A fixture's modules, decoded, in the order its manifest loads them.
fixtureModules :: P.String -> Aff (Either P.String (P.Array Dmo))
fixtureModules name = liftEffect do
  manifest <- readManifest name
  bytes <- traverse (\m -> readBytes (fixturesRoot <> name <> "/" <> m <> ".dmo")) manifest.modules
  pure case traverse decode bytes of
    Left err -> Left (name <> ": does not decode: " <> show err)
    Right dmos -> Right dmos

inMain :: P.String -> Qualified Ident
inMain = Qualified (ModuleName "Main") <<< Ident

inInt :: P.String -> Qualified Ident
inInt = Qualified (ModuleName "Base.Int") <<< Ident

-- Running generated code ---------------------------------------------------------------

-- | The namespace of an imported module, which only the functions below read.
foreign import data Namespace :: P.Type

foreign import runtimeSpecifier :: P.String

foreign import importGeneratedImpl
  :: P.Array { name :: P.String, source :: P.String } -> P.String -> EffectFnAff Namespace

foreign import importFailureImpl
  :: P.Array { name :: P.String, source :: P.String }
  -> P.String
  -> EffectFnAff { loaded :: P.Boolean, message :: P.String, fault :: P.Boolean, global :: P.String }

-- | How executing an entry point ended — `produced`, `faulted`, `failedToStart`,
-- | `threw`, or `notLoaded` — with what it produced, held as `holder`'s `value`, or
-- | what ended it, and the effects the host saw.
foreign import runEntryImpl
  :: P.Array { name :: P.String, source :: P.String }
  -> P.String
  -> P.String
  -> P.String
  -> EffectFnAff
       { ended :: P.String
       , holder :: Namespace
       , kind :: P.String
       , foreign :: P.String
       , detail :: P.String
       , message :: P.String
       , effects :: P.Array P.String
       }

foreign import shapeOfImpl
  :: { number :: P.Number -> Shape
     , string :: P.String -> Shape
     , boolean :: P.Boolean -> Shape
     , data :: P.String -> P.Array Shape -> Shape
     , variant :: P.String -> Shape -> Shape
     , record :: P.Array { key :: P.String, value :: Shape } -> Shape
     , fn :: Shape
     , other :: P.String -> Shape
     }
  -> Namespace
  -> P.String
  -> Shape

-- | What a value is, as either side can say it. Every number is one kind here,
-- | JavaScript holding an `Int`, a `Number`, and a `Char` alike; they compare by
-- | literal identity, so a negative zero is not a zero.
data Shape
  = SNum P.Number
  | SStr P.String
  | SBool P.Boolean
  | SDat P.String (P.Array Shape)
  | SVar P.String Shape
  | SRec (P.Array (Tuple P.String Shape))
  | SFn
  | SOther P.String

instance Eq Shape where
  eq a b = case a, b of
    SNum x, SNum y -> if x /= x then y /= y else x == y && (1.0 / x) == (1.0 / y)
    SStr x, SStr y -> x == y
    SBool x, SBool y -> x == y
    SDat c xs, SDat d ys -> c == d && xs == ys
    SVar k x, SVar l y -> k == l && x == y
    SRec xs, SRec ys -> xs == ys
    SFn, SFn -> true
    SOther x, SOther y -> x == y
    _, _ -> false

instance Show Shape where
  show = case _ of
    SNum x -> show x
    SStr s -> show s
    SBool b -> show b
    SDat c xs -> "(" <> c <> String.joinWith "" (map (\x -> " " <> show x) xs) <> ")"
    SVar k x -> "<" <> k <> " " <> show x <> ">"
    SRec xs -> "{" <> String.joinWith ", " (map (\(Tuple k v) -> k <> ": " <> show v) xs) <> "}"
    SFn -> "<function>"
    SOther s -> "<" <> s <> ">"

jsShape :: Namespace -> P.String -> Shape
jsShape = shapeOfImpl
  { number: SNum
  , string: SStr
  , boolean: SBool
  , data: SDat
  , variant: SVar
  , record: \fields -> SRec (sortFields (map (\f -> Tuple f.key f.value) fields))
  , fn: SFn
  , other: SOther
  }

sortFields :: P.Array (Tuple P.String Shape) -> P.Array (Tuple P.String Shape)
sortFields = Array.sortWith (\(Tuple k _) -> k)

-- | Whether a fault is the one a manifest expects, as far as every runtime observes
-- | one of its kind.
faultMatches :: forall r. ExpectedFault -> { kind :: P.String, foreign :: P.String, detail :: P.String | r } -> P.Boolean
faultMatches e f = e.kind == f.kind && case e.kind of
  "refused" -> f.foreign == e.foreign && f.detail == e.reason
  "threw" -> f.foreign == e.foreign && f.detail == e.message
  "breached" -> f.foreign == e.foreign
  "actionRefused" -> f.detail == e.reason
  "actionThrew" -> f.detail == e.message
  "actionBreached" -> f.foreign == e.foreign
  _ -> false

-- | `Mod.Sub.name` as the global `name` of the module `Mod.Sub`.
qualified :: P.String -> Qualified Ident
qualified g = case String.lastIndexOf (String.Pattern ".") g of
  Just i -> Qualified (ModuleName (String.take i g)) (Ident (String.drop (i + 1) g))
  Nothing -> Qualified (ModuleName "") (Ident g)

-- | Whether what an export holds is the value a manifest expects, as JavaScript
-- | can tell.
matches :: Expected -> Shape -> P.Boolean
matches e s = case e, s of
  EInt n, SNum x -> x == toNumber n
  ENumber y, SNum x -> if y /= y then x /= x else y == x && 1.0 / y == 1.0 / x
  EChar c, SNum x -> x == toNumber c
  EString a, SStr b -> a == b
  EBoolean a, SBool b -> a == b
  EData c fields, SDat d xs -> c == d && Array.length fields == Array.length xs && and (Array.zipWith matches fields xs)
  ERecord fields, SRec xs ->
    let
      wanted = Array.sortWith _.key (map (\f -> { key: keyText f.key, value: f.value }) fields)
    in
      Array.length wanted == Array.length xs
        && and (Array.zipWith (\w (Tuple k v) -> w.key == k && matches w.value v) wanted xs)
  EVariant k v, SVar l x -> keyText k == l && matches v x
  EFunction, SFn -> true
  _, _ -> false

-- | A key as the backend writes it.
keyText :: ExpectedKey -> P.String
keyText = case _ of
  KField s -> "s:" <> s
  KTag t -> "t:" <> t
  KPosition n -> "p:" <> show n
  KEffect e -> "e:" <> effectText e
  where
  -- `Mod.Sub.Eff` names the effect `Eff` of the module `Mod.Sub`, which the backend
  -- writes `Mod.Sub:Eff`: only the last `.` separates the two
  effectText e = case String.lastIndexOf (String.Pattern ".") e of
    Just i -> String.take i e <> ":" <> String.drop (i + 1) e
    Nothing -> e

-- | Options for a module that declares no foreign a host implements and exports no
-- | entry point.
plainOptions :: Options
plainOptions = { runtime: runtimeSpecifier, hosted: Nothing, entry: Nothing }

generated :: P.Array Dmo -> Either P.String (P.Array { name :: P.String, source :: P.String })
generated dmos = case generatedOrRefused (const plainOptions) dmos of
  Left e -> Left (show e)
  Right files -> Right files

generatedOrRefused :: (Dmo -> Options) -> P.Array Dmo -> Either JsError (P.Array { name :: P.String, source :: P.String })
generatedOrRefused optionsFor = traverse \dmo -> case generate (optionsFor dmo) dmo of
  Left e -> Left e
  Right source -> Right { name: fileName dmo.name, source }

-- | The options each module of a fixture is generated with: its entry in the
-- | fixture's foreign manifest, the specifier resolved against the fixture's
-- | directory as a build resolves it, and the entry point where the module holds
-- | the one the manifest names.
fixtureOptions :: P.String -> Maybe ForeignManifest.Manifest -> Maybe P.String -> Dmo -> Options
fixtureOptions dir foreignManifest entry dmo =
  { runtime: runtimeSpecifier
  , hosted: do
      held <- foreignManifest
      found <- ForeignManifest.entryFor held dmo.name
      let ModuleName m = dmo.name
      pure { specifier: resolveSpecifier dir (specifierIn (dir <> "/foreign-manifest.json") m), signatures: found.foreigns }
  , entry: do
      Qualified m x <- map qualified entry
      if m == dmo.name then Just x else Nothing
  }

-- What a fixture's generation may end at ------------------------------------------------

-- | The fixtures whose manifest says they are refused where they load, or fail to
-- | start for want of the entry global, and which this backend refuses where it
-- | generates, with the refusal each must be. Any other refusal at generation fails,
-- | and so does such a fixture generating.
-- |
-- | Each refusal is pinned whole, since the manifest's `mentions` does not tell
-- | them apart: every shape refusal names the same effect, and a report naming a
-- | foreign says nothing of what was wrong with it.
generationRefusals :: P.Array { name :: P.String, refusal :: JsError -> P.Boolean }
generationRefusals =
  [ { name: "handler-cell-twice", refusal: (_ == CellKeyTwice "s:reading") }
  , { name: "handler-cell-aliased", refusal: (_ == CellKeyTwice "s:reading") }
  , { name: "handler-clause-twice", refusal: (_ == ClauseTwice "bump") }
  , { name: "handler-clause-aliased", refusal: (_ == ClauseTwice "bump") }
  -- the handler entry holds two of each and the instruction supplies one
  , { name: "handler-hndl-clauses", refusal: (_ == HandlerClausesDisagree meter 2 1) }
  , { name: "handler-tailhndl-clauses", refusal: (_ == HandlerClausesDisagree meter 2 1) }
  , { name: "handler-hndl-cells", refusal: (_ == HandlerCellsDisagree meter 2 1) }
  , { name: "handler-tailhndl-cells", refusal: (_ == HandlerCellsDisagree meter 2 1) }
  , { name: "foreign-no-entry", refusal: (_ == ForeignWithoutImplementation (inHost "greet")) }
  , { name: "foreign-no-signature", refusal: (_ == NoSignature (inHost "greet")) }
  -- `greet` is declared at arity one and its signature has two params
  , { name: "foreign-params-length", refusal: (_ == SignatureDisagrees (inHost "greet") 1 2) }
  , { name: "io-entry-arity-pure", refusal: (_ == EntryDeclaredAtWrongArity (inIO "pure") 1 2) }
  , { name: "io-entry-arity-bind", refusal: (_ == EntryDeclaredAtWrongArity (inIO "bind") 2 3) }
  , { name: "start-no-global", refusal: (_ == NoEntryGlobal (inMain "missing")) }
  ]
  where
  meter = "e:Main:Meter"
  inHost = Qualified (ModuleName "Host") <<< Ident
  inIO = Qualified (ModuleName "Base.IO") <<< Ident

spec :: Spec Unit
spec = describe "the JavaScript backend" do
  it "runs every bytecode fixture as its manifest says" do
    names <- liftEffect (caseNames fixturesRoot)
    when (Array.null names) (fail "no fixtures found")
    mismatches <- traverse fixtureMismatches names
    Array.concat mismatches `shouldEqual` []

  -- a name left behind when its fixture is renamed or removed would check nothing
  it "lists only fixtures that exist as refused at generation" do
    names <- liftEffect (caseNames fixturesRoot)
    Array.filter (\n -> not (Array.elem n names)) (map _.name generationRefusals)
      `shouldEqual` []

  describe "what the generated code holds" do
    it "captures a computed local, and the closure reads it through CAPT" do
      programs <- fixtureModules "programs"
      case programs of
        Left err -> fail err
        Right dmos -> case Array.last dmos of
          Nothing -> fail "no modules"
          Just main -> case capturingClosure main "captured" of
            Nothing -> fail "the value builds no closure with a capture"
            Just f -> do
              -- the closure's function takes a capture and reads it
              readsCapture main f `shouldEqual` true
              -- and the segment generated for it reads the frame's capture slot
              case generated [ main ] of
                Left err -> fail err
                Right files -> case Array.head files of
                  Nothing -> fail "nothing generated"
                  Just file -> String.contains (String.Pattern "f.caps[0]") (segmentOf f file.source) `shouldEqual` true

  describe "what a loader establishes, before code is generated" do
    it "refuses each module a loader refuses, for the reason a loader gives" do
      programs <- fixtureModules "programs"
      case programs of
        Right [ int, _, main ] -> Array.mapMaybe (unrefused int main) loaderRefusals `shouldEqual` []
        Right _ -> fail "not three modules"
        Left err -> fail err

    -- a foreign the runtime carries out is resolved as a declaration before its name
    -- selects the runtime entry
    it "resolves a foreign the runtime carries out as a declaration, before binding it" do
      ioPure <- fixtureModules "io-pure"
      byForeign <- fixtureModules "operation-by-foreign"
      case ioPure, byForeign of
        Right [ _, main ], Right [ int, _ ] -> do
          let
            -- Main names Base.IO.pure without importing Base.IO
            unimported = main { imports = Array.filter (_ /= ModuleName "Base.IO") main.imports }
            -- Base.Int names its own add without declaring it
            undeclared = int
              { foreigns = Array.filter (\f -> f.name /= inInt "add") int.foreigns
              , exports = Array.filter (_ /= inInt "add") int.exports
              , foreignRefs = int.foreignRefs <> [ inInt "add" ]
              }
          refusalOf unimported `shouldEqual` Just (NotImported (Qualified (ModuleName "Base.IO") (Ident "pure")))
          refusalOf undeclared `shouldEqual` Just (NoSuchDeclaration (inInt "add"))
        _, _ -> fail "not the modules of io-pure and operation-by-foreign"

  describe "what the runtime checks" do
    it "refuses, as a bug, each structural operation handed what its precondition excludes" do
      map _.name (Array.filter (not <<< _.refused) runtimeRefusals) `shouldEqual` []

  describe "what the encoder refuses" do
    it "refuses a module whose name the encoder would not write, as the encoder does" do
      programs <- fixtureModules "programs"
      case programs of
        Right [ _, _, main ] -> do
          let
            -- `sum` is exported nowhere, so nothing but its spelling changes
            lone = main { globals = map (\g -> if g.name == inMain "sum" then g { name = inMain "s\xD800um" } else g) main.globals }
          case encode lone, generate plainOptions lone of
            Left (NotScalarText _), Left (NotEncodable (NotScalarText _)) -> pure unit
            byEncoder, byBackend -> fail ("the encoder gave " <> show (map (const unit) byEncoder) <> " and the backend " <> show (map (const unit) byBackend))
        Right _ -> fail "not three modules"
        Left err -> fail err

-- | The function of the first closure with a capture that the initializer of the
-- | named global builds.
capturingClosure :: Dmo -> P.String -> Maybe P.Int
capturingClosure dmo name = do
  g <- Array.find (\g -> g.name == inMain name) dmo.globals
  f <- case g.init of
    GRun (FuncIx i) -> Array.index dmo.functions i
    GFunc (FuncIx i) -> Array.index dmo.functions i
  Array.findMap
    ( case _ of
        CLOS _ (FuncIx c) captures | not (Array.null captures) -> Just c
        _ -> Nothing
    )
    f.body.code

-- | Whether a function takes a capture and its entry node reads one with `CAPT`.
readsCapture :: Dmo -> P.Int -> P.Boolean
readsCapture dmo index = case Array.index dmo.functions index of
  Nothing -> false
  Just f ->
    not (Array.null f.captures)
      && Array.any
        ( case _ of
            CAPT _ _ -> true
            _ -> false
        )
        f.body.code

-- | The entry segment of a function, as the generated source writes it.
segmentOf :: P.Int -> P.String -> P.String
segmentOf index source =
  case String.indexOf (String.Pattern ("function f" <> show index <> "_s0(")) source of
    Nothing -> ""
    Just start ->
      let
        rest = String.drop start source
      in
        case String.indexOf (String.Pattern "\n}\n") rest of
          Just end -> String.take end rest
          Nothing -> rest

foreign import runtimeRefusals :: P.Array { name :: P.String, refused :: P.Boolean }

-- | Why the backend refuses a module, where it does.
refusalOf :: Dmo -> Maybe JsError
refusalOf dmo = case generate plainOptions dmo of
  Left e -> Just e
  Right _ -> Nothing

-- | One thing a loader refuses, as a change to one module, and the refusal it gives.
type LoaderRefusal =
  { name :: P.String
  , change :: { int :: Dmo, main :: Dmo } -> Dmo
  , refusal :: JsError -> P.Boolean
  }

-- | Where the changed module is generated anyway, or refused for another reason,
-- | what happened.
unrefused :: Dmo -> Dmo -> LoaderRefusal -> Maybe P.String
unrefused intDmo mainDmo r = case generate plainOptions (r.change { int: intDmo, main: mainDmo }) of
  Left e | r.refusal e -> Nothing
  Left e -> Just (r.name <> ": refused as " <> show e)
  Right _ -> Just (r.name <> ": generated")

loaderRefusals :: P.Array LoaderRefusal
loaderRefusals =
  [ { name: "a module named Prim"
    , change: \m -> m.main { name = ModuleName "Prim" }
    , refusal: case _ of
        ReservedModuleName _ -> true
        _ -> false
    }
  , { name: "a constructor another module declares"
    , change: \m -> m.main { ctors = Array.modifyAtIndices [ 0 ] (\c -> c { name = Qualified (ModuleName "Other") (Ident "Nil") }) m.main.ctors }
    , refusal: case _ of
        NotThisModule _ -> true
        _ -> false
    }
  , { name: "a constructor whose owner another module declares"
    , change: \m -> m.main { ctors = Array.modifyAtIndices [ 0 ] (\c -> c { owner = Qualified (ModuleName "Other") (TyName "List") }) m.main.ctors }
    , refusal: case _ of
        OwnerNotThisModule _ -> true
        _ -> false
    }
  , { name: "a global declared twice"
    , change: \m -> m.main { globals = m.main.globals <> Array.take 1 m.main.globals }
    , refusal: case _ of
        DeclaredTwice _ -> true
        _ -> false
    }
  , { name: "an export naming no declaration"
    , change: \m -> m.main { exports = m.main.exports <> [ inMain "nowhere" ] }
    , refusal: case _ of
        ExportNotDeclared _ -> true
        _ -> false
    }
  , { name: "a run global over a function of parameters"
    , change: \m -> installing "summed" (GRun <<< FuncIx) (\f -> f.nparams > 0) m.main
    , refusal: case _ of
        RunGlobalWithParameters _ _ -> true
        _ -> false
    }
  , { name: "a function global over a function of no parameters"
    , change: \m -> installing "sum" (GFunc <<< FuncIx) (\f -> f.nparams == 0) m.main
    , refusal: case _ of
        FunctionGlobalWithoutParameters _ -> true
        _ -> false
    }
  , { name: "a global over a function expecting captures"
    , change: \m -> installing "sum" (GFunc <<< FuncIx) (\f -> f.nparams > 0 && not (Array.null f.captures)) m.main
    , refusal: case _ of
        GlobalExpectsCaptures _ _ -> true
        _ -> false
    }
  , { name: "an operation declared at another arity"
    , change: \m -> m.int { foreigns = map (\f -> if f.name == inInt "add" then f { arity = 3 } else f) m.int.foreigns }
    , refusal: case _ of
        EntryDeclaredAtWrongArity _ 2 3 -> true
        _ -> false
    }
  ]

-- | The module with the named global installed over the first function `which`
-- | admits, as `how` installs one.
installing :: P.String -> (P.Int -> GlobalInit) -> (B.Function -> P.Boolean) -> Dmo -> Dmo
installing name how which dmo = case Array.findIndex which dmo.functions of
  Nothing -> dmo
  Just i -> dmo { globals = map (\g -> if g.name == inMain name then g { init = how i } else g) dmo.globals }

-- The fixtures ----------------------------------------------------------------------------

-- | What running a fixture gave where the manifest says otherwise, one line each.
fixtureMismatches :: P.String -> Aff (P.Array P.String)
fixtureMismatches name = do
  manifest <- liftEffect (readManifest name)
  modules <- fixtureModules name
  foreignManifest <- liftEffect readForeignManifest
  case modules, foreignManifest of
    Left err, _ -> pure [ err ]
    _, Left err -> pure [ name <> ": " <> err ]
    Right dmos, Right held -> case generatedOrRefused (fixtureOptions dir held (map _.entry manifest.run)) dmos of
      Left err
        | Just r <- refusedAtGeneration -> pure
            if refusedHere manifest err && r.refusal err then []
            else [ name <> ": refused as " <> show err <> ", not as the refusal it is listed for" ]
        | otherwise -> pure [ name <> ": not generated: " <> show err ]
      Right files
        | Just _ <- refusedAtGeneration -> pure [ name <> ": generated, where it is listed as refused" ]
        | Just r <- manifest.run -> running r files
        | otherwise -> case Array.last manifest.modules of
            Nothing -> pure [ name <> ": no modules" ]
            Just entry -> run manifest files (entry <> ".js")
  where
  dir = fixturesRoot <> name

  refusedAtGeneration = Array.find (\r -> r.name == name) generationRefusals

  -- a refusal where the modules load, naming what the manifest says, or an entry
  -- point naming no global, which is known before anything is generated
  refusedHere m err = case m.run of
    Just { end: FailsToStart "noSuchGlobal" } -> true
    Just _ -> false
    Nothing -> not m.loads && m.faults == "" && String.contains (String.Pattern m.mentions) (show err)

  readForeignManifest = do
    let path = dir <> "/foreign-manifest.json"
    present <- exists path
    if not present then pure (Right Nothing)
    else do
      source <- readText path
      pure case ForeignManifest.parse "javascript" source of
        Left err -> Left ("the foreign manifest does not parse: " <> show err)
        Right parsed -> Right (Just parsed)

  -- the entry point imported from the module holding it and executed, as a host
  -- starting the program does
  running :: Run -> P.Array { name :: P.String, source :: P.String } -> Aff (P.Array P.String)
  running r files = do
    let Qualified m _ = qualified r.entry
    ended <- fromEffectFnAff (runEntryImpl files (fileName m) r.entry dir)
    pure case r.end, ended.ended of
      Produces wanted wantedEffects, "produced" ->
        (if matches wanted (jsShape ended.holder "value") then [] else [ name <> ": produced " <> show (jsShape ended.holder "value") ])
          <> sameEffects wantedEffects ended.effects
      FaultsWith wanted wantedEffects, "faulted" ->
        (if faultMatches wanted ended then [] else [ name <> ": faulted as \"" <> ended.message <> "\", not as " <> wanted.kind ])
          <> sameEffects wantedEffects ended.effects
      FailsToStart "notAnAction", "failedToStart" -> []
      _, _ -> [ name <> ": ended as " <> ended.ended <> " \"" <> ended.message <> "\"" ]

  sameEffects wanted seen =
    if wanted == seen then []
    else [ name <> ": saw the effects " <> show seen <> ", not " <> show wanted ]

  run :: Manifest -> P.Array { name :: P.String, source :: P.String } -> P.String -> Aff (P.Array P.String)
  run manifest files entry =
    if manifest.loads then do
      namespace <- fromEffectFnAff (importGeneratedImpl files entry)
      pure $ Array.mapMaybe
        ( \o ->
            let
              shape = jsShape namespace (unqualified o.global)
            in
              if matches o.value shape then Nothing
              else Just (name <> ": " <> o.global <> " holds " <> show shape)
        )
        manifest.observe
    else do
      ended <- fromEffectFnAff (importFailureImpl files entry)
      pure
        if ended.loaded then [ name <> ": loaded, where the manifest says it does not" ]
        -- a fault the manifest expects is one the named global's initialization ended at
        else if manifest.faults /= "" then
          if ended.fault && ended.global == manifest.faults then []
          else [ name <> ": ended as \"" <> ended.message <> "\", not as a fault initializing " <> manifest.faults ]
        else if not ended.fault && String.contains (String.Pattern manifest.mentions) ended.message then []
        else [ name <> ": refused as \"" <> ended.message <> "\", not naming " <> manifest.mentions ]

  unqualified g = case String.lastIndexOf (String.Pattern ".") g of
    Just i -> String.drop (i + 1) g
    Nothing -> g
