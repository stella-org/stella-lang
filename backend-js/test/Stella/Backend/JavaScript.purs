-- | The JavaScript backend: the bytecode fixtures generated and run in Node, and
-- | what only this backend does — the code it generates, what it refuses before
-- | generating, and the preconditions its runtime checks.
-- |
-- | **Everything here starts from a `.dmo`**, read from `fixtures/bytecode` as a
-- | backend outside this compiler would read one
-- | ([Fixtures](../../../../fixtures/bytecode/README.md)). A fixture's modules are
-- | generated one ES module each, written out, and the last imported; what its
-- | exports hold, or how loading ended, is checked against the fixture's manifest.
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
import Stella.Backend.JavaScript (JsError(..), fileName, generate)
import Stella.Compiler.Bytecode (Dmo, EncodeError(..), FuncIx(..), GlobalInit(..), Instr(..), decode, encode)
import Stella.Compiler.Bytecode as B
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), TyName(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- Reading the fixtures -------------------------------------------------------------------

foreign import fixturesRoot :: P.String
foreign import caseNames :: P.String -> Effect (P.Array P.String)
foreign import readText :: P.String -> Effect P.String
foreign import readBytes :: P.String -> Effect (P.Array P.Int)

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

-- | A fixture's manifest. `mentions` is what a refusal names, and `faults` the
-- | global whose initialization a fault ends, each `""` where it does not apply.
-- | `runs` holds for a fixture whose outcome is running an entry point.
type Manifest =
  { description :: P.String
  , modules :: P.Array P.String
  , loads :: P.Boolean
  , mentions :: P.String
  , faults :: P.String
  , observe :: P.Array { global :: P.String, value :: Expected }
  , runs :: P.Boolean
  }

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

inLib :: P.String -> Qualified Ident
inLib = Qualified (ModuleName "Lib") <<< Ident

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

generated :: P.Array Dmo -> Either P.String (P.Array { name :: P.String, source :: P.String })
generated dmos = case generatedOrRefused dmos of
  Left e -> Left (show e)
  Right files -> Right files

generatedOrRefused :: P.Array Dmo -> Either JsError (P.Array { name :: P.String, source :: P.String })
generatedOrRefused = traverse \dmo -> case generate { runtime: runtimeSpecifier } dmo of
  Left e -> Left e
  Right source -> Right { name: fileName dmo.name, source }

-- What a fixture's generation may end at ------------------------------------------------

-- | The fixtures holding a construct this backend does not generate, with the
-- | construct each is refused for. Such a fixture generating fails, and so does its
-- | refusal naming another construct.
knownUnsupported :: P.Array { name :: P.String, unsupported :: P.String }
knownUnsupported =
  map (gap (io "pure"))
    [ "io"
    , "io-entry-arity-bind"
    , "io-entry-arity-pure"
    , "io-pure"
    , "run-action-breached"
    , "run-action-refused"
    , "run-action-threw"
    , "run-action-threw-bug"
    , "run-action-threw-fault"
    , "run-breach-action-not-callable"
    , "run-breach-boolean-number"
    , "run-breach-char-surrogate"
    , "run-breach-char-two"
    , "run-breach-int-fraction"
    , "run-breach-int-string"
    , "run-breach-int-wide"
    , "run-breach-number-string"
    , "run-breach-string-surrogate"
    , "run-refused"
    , "run-threw"
    , "run-threw-bug"
    , "run-threw-fault"
    , "start-no-global"
    , "start-not-an-action"
    ]
    <> map (gap (host "greet"))
      [ "foreign-no-entry"
      , "foreign-no-export"
      , "foreign-no-signature"
      , "foreign-not-callable"
      , "foreign-params-length"
      , "foreign-unreachable"
      ]
    <> map (gap (host "add")) [ "stale-foreign-call", "stale-foreign-partial" ]
  where
  gap unsupported name = { name, unsupported }
  io x = "the foreign declaration Base.IO." <> x
  host x = "the foreign declaration Host." <> x

-- | The fixtures whose manifest says they are refused where they load, and which
-- | this backend refuses where it generates, with the refusal each must be. Any
-- | other refusal at generation fails, and so does such a fixture generating.
-- |
-- | Each refusal is pinned whole, since the manifest's `mentions` does not tell
-- | them apart: every shape refusal names the same effect.
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
  ]
  where
  meter = "e:Main:Meter"

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

  it "lists only fixtures that exist as unsupported" do
    names <- liftEffect (caseNames fixturesRoot)
    Array.filter (\n -> not (Array.elem n names)) (map _.name knownUnsupported)
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
          case encode lone, generate { runtime: runtimeSpecifier } lone of
            Left (NotScalarText _), Left (NotEncodable (NotScalarText _)) -> pure unit
            byEncoder, byBackend -> fail ("the encoder gave " <> show (map (const unit) byEncoder) <> " and the backend " <> show (map (const unit) byBackend))
        Right _ -> fail "not three modules"
        Left err -> fail err

  describe "what the backend refuses" do
    it "refuses a foreign that needs a host implementation" do
      programs <- fixtureModules "programs"
      case programs of
        Right [ _, lib, _ ] -> do
          -- a foreign the ABI does not fix is supplied by a host implementation
          let withForeign = lib { foreigns = lib.foreigns <> [ { name: inLib "now", arity: 1 } ] }
          case generate { runtime: runtimeSpecifier } withForeign of
            Left (Unsupported _) -> pure unit
            other -> fail ("expected the foreign to be refused, got " <> show (map (const unit) other))
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

-- | One thing a loader refuses, as a change to one module, and the refusal it gives.
type LoaderRefusal =
  { name :: P.String
  , change :: { int :: Dmo, main :: Dmo } -> Dmo
  , refusal :: JsError -> P.Boolean
  }

-- | Where the changed module is generated anyway, or refused for another reason,
-- | what happened.
unrefused :: Dmo -> Dmo -> LoaderRefusal -> Maybe P.String
unrefused intDmo mainDmo r = case generate { runtime: runtimeSpecifier } (r.change { int: intDmo, main: mainDmo }) of
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
        OperationDeclaredAtWrongArity _ 2 3 -> true
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
  case modules of
    Left err -> pure [ err ]
    Right dmos -> case generatedOrRefused dmos of
      Left err
        | Just gap <- listedUnsupported -> pure
            if err == Unsupported gap.unsupported then []
            else [ name <> ": refused as " <> show err <> ", not as the construct it is listed as unsupported for" ]
        | Just r <- refusedAtGeneration -> pure
            if refusedAtLoad manifest && r.refusal err && String.contains (String.Pattern manifest.mentions) (show err) then []
            else [ name <> ": refused as " <> show err <> ", not as the refusal naming " <> manifest.mentions <> " it is listed for" ]
        | otherwise -> pure [ name <> ": not generated: " <> show err ]
      Right files
        | Just _ <- listedUnsupported -> pure [ name <> ": generated, where it is listed as unsupported" ]
        | Just _ <- refusedAtGeneration -> pure [ name <> ": generated, where it is listed as refused" ]
        | manifest.runs -> pure [ name <> ": generated, and running an entry point is not checked here" ]
        | otherwise -> case Array.last manifest.modules of
            Nothing -> pure [ name <> ": no modules" ]
            Just entry -> run manifest files (entry <> ".js")
  where
  refusedAtGeneration = Array.find (\r -> r.name == name) generationRefusals

  listedUnsupported = Array.find (\gap -> gap.name == name) knownUnsupported

  refusedAtLoad m = not m.loads && m.faults == "" && not m.runs

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
