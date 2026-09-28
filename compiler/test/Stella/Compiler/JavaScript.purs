-- | The JavaScript backend: the bytecode fixtures generated and run in Node, and
-- | what only this backend does — the code it generates, what it refuses before
-- | generating, and the preconditions its runtime checks.
-- |
-- | A fixture's `.dmo` files are read from disk as a backend outside this compiler
-- | would read them, generated one ES module each, written out, and the last module
-- | imported; what its exports hold, or the refusal loading gives, is checked
-- | against the fixture's manifest ([Fixtures](Fixtures.purs)). Steam checks the
-- | same manifests, so the two agree wherever both pass.
-- |
-- | JavaScript holds an `Int`, a `Number`, and a `Char` alike as a number, so each is
-- | compared by the number it is; a function is compared as being one.
module Test.Stella.Compiler.JavaScript (spec) where

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
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Effect.Class (liftEffect)
import Stella.Compiler.Bytecode (Dmo, EncodeError(..), FuncIx(..), GlobalInit(..), Instr(..), decode, encode)
import Stella.Compiler.Bytecode as B
import Stella.Compiler.JavaScript (JsError(..), fileName, generate)
import Stella.Compiler.TypedCore (Decl(..), Ident(..), ModuleName(..), Qualified(..), TyName(..), monoScheme)
import Stella.Compiler.TypedCore.Prim (intTy, pureFn)
import Stella.Compiler.TypedCore (Type(..)) as T
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Stella.Compiler.Fixtures (Manifest, caseNames, compileAll, fixturesRoot, readBytes, readManifest)
import Test.Stella.Compiler.Fixtures.Programs (inInt, inMain, intModule, libModule, mainModule)
import Test.Stella.Compiler.Fixtures.Value (Expected(..), ExpectedKey(..))

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
generated = traverse \dmo -> case generate { runtime: runtimeSpecifier } dmo of
  Left e -> Left (show e)
  Right source -> Right { name: fileName dmo.name, source }

-- The fixtures ----------------------------------------------------------------------------

-- | What running a fixture gave where the manifest says otherwise, one line each.
fixtureMismatches :: P.String -> Aff (P.Array P.String)
fixtureMismatches name = do
  manifest <- liftEffect (readManifest name)
  bytes <- liftEffect (traverse (\m -> readBytes (fixturesRoot <> name <> "/" <> m <> ".dmo")) manifest.modules)
  case traverse decode bytes of
    Left err -> pure [ name <> ": does not decode: " <> show err ]
    Right dmos -> case generated dmos of
      Left err -> pure [ name <> ": not generated: " <> err ]
      Right files -> case Array.last manifest.modules of
        Nothing -> pure [ name <> ": no modules" ]
        Just entry -> run manifest files (entry <> ".js")
  where
  run :: Manifest -> _ -> P.String -> Aff (P.Array P.String)
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

spec :: Spec Unit
spec = describe "the JavaScript backend" do
  it "runs every bytecode fixture as its manifest says" do
    names <- liftEffect (caseNames fixturesRoot)
    when (Array.null names) (fail "no fixtures found")
    mismatches <- traverse fixtureMismatches names
    Array.concat mismatches `shouldEqual` []

  describe "what the generated code holds" do
    it "captures a computed local, and the closure reads it through CAPT" do
      case compileAll [ intModule, libModule, mainModule ] of
        Left err -> fail err
        Right compiled -> case Array.last compiled of
          Nothing -> fail "nothing compiled"
          Just main -> case capturingClosure main.dmo "captured" of
            Nothing -> fail "the value builds no closure with a capture"
            Just f -> do
              -- the closure's function takes a capture and reads it
              readsCapture main.dmo f `shouldEqual` true
              -- and the segment generated for it reads the frame's capture slot
              case generated [ main.dmo ] of
                Left err -> fail err
                Right files -> case Array.head files of
                  Nothing -> fail "nothing generated"
                  Just file -> String.contains (String.Pattern "f.caps[0]") (segmentOf f file.source) `shouldEqual` true

  describe "what a loader establishes, before code is generated" do
    it "refuses each module a loader refuses, for the reason a loader gives" do
      case compileAll [ intModule, libModule, mainModule ] of
        Right [ intCompiled, _, mainCompiled ] ->
          Array.mapMaybe (unrefused intCompiled.dmo mainCompiled.dmo) loaderRefusals `shouldEqual` []
        Right _ -> fail "not three modules"
        Left err -> fail err

  describe "what the runtime checks" do
    it "refuses, as a bug, each structural operation handed what its precondition excludes" do
      map _.name (Array.filter (not <<< _.refused) runtimeRefusals) `shouldEqual` []

  describe "what the encoder refuses" do
    it "refuses a module whose name the encoder would not write, as the encoder does" do
      case compileAll [ intModule, libModule, mainModule ] of
        Right [ _, _, mainCompiled ] -> do
          let
            dmo = mainCompiled.dmo
            -- `sum` is exported nowhere, so nothing but its spelling changes
            lone = dmo { globals = map (\g -> if g.name == inMain "sum" then g { name = inMain "s\xD800um" } else g) dmo.globals }
          case encode lone, generate { runtime: runtimeSpecifier } lone of
            Left (NotScalarText _), Left (NotEncodable (NotScalarText _)) -> pure unit
            byEncoder, byBackend -> fail ("the encoder gave " <> show (map (const unit) byEncoder) <> " and the backend " <> show (map (const unit) byBackend))
        Right _ -> fail "not three modules"
        Left err -> fail err

  describe "what the backend does not carry out yet" do
    it "refuses a foreign it does not yet reach" do
      let
        withForeign = libModule
          { decls = libModule.decls <> [ DeclForeign 9 { name: Ident "now", scheme: monoScheme (pureFn (T.TCon intTy []) (T.TCon intTy [])), attributes: [] } ] }
      case compileAll [ intModule, withForeign ] of
        Right compiled -> case Array.last compiled of
          Just lib -> case generate { runtime: runtimeSpecifier } lib.dmo of
            Left (Unsupported _) -> pure unit
            other -> fail ("expected the foreign to be refused, got " <> show (map (const unit) other))
          Nothing -> fail "nothing compiled"
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
