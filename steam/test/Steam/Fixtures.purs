-- | Steam running the bytecode fixtures.
-- |
-- | A fixture is a directory of `fixtures/bytecode` holding lowered modules and a
-- | manifest saying which load, in what order, whether they load or are refused
-- | where they load, what the named globals hold, and, for a fixture with an entry
-- | point, how running it ends and what effects the host saw on the way. The
-- | compiler's test suite writes them from hand-written Core and checks they are
-- | current; this reads the bytes as any consumer of a `.dmo` would and checks the
-- | manifest. The JavaScript backend checks the same manifests, so the two agree
-- | wherever both pass.
-- |
-- | A fixture holding a `foreign-manifest.json` has its foreign table assembled from
-- | it before the first module loads, as `steam run` assembles one, with the
-- | manifest's directory as the base its specifiers resolve against. An entry point
-- | is found and executed as `steam run` finds and executes one.
-- |
-- | Steam holds every value by its kind, so an `Int`, a `Number`, and a `Char` are
-- | told apart here as the manifest writes them.
module Test.Steam.Fixtures (spec) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (and)
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseAff', runBaseEffect)
import Run.Except as Except
import Steam.CLI.Assemble (AssembleError(..), tableFor)
import Steam.Drive (execute)
import Steam.Eval (Failure(..))
import Steam.Fault (Fault(..))
import Steam.Load (LoadError(..), Store, emptyStore, globalNamed, load, moduleNamed, namesOf, noIdentities, registryOf, unitValue)
import Steam.Structural (NumberAtom(..), StructuralValue(..), defaultLimits, inspect)
import Steam.Value (Value(..))
import Stella.CLI.Effect.Foreigns as Foreigns
import Stella.CLI.Runner.Node (nodeForeignsHandler)
import Stella.Compiler.Bytecode (decode)
import Stella.Compiler.Bytecode.Module (Key(..)) as M
import Stella.Compiler.ForeignManifest as ForeignManifest
import Stella.Compiler.TypedCore (EffName(..), Ident(..), ModuleName(..), OpName(..), Qualified(..), RowKey(..), Symbol(..), Tag(..), codePointOf, sameNumber, textOf)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

foreign import fixturesRoot :: P.String
foreign import caseNames :: P.String -> Effect (P.Array P.String)
foreign import exists :: P.String -> Effect P.Boolean
foreign import readText :: P.String -> Effect P.String
foreign import readBytes :: P.String -> Effect (P.Array P.Int)
foreign import eventsImpl :: P.String -> EffectFnAff (P.Array P.String)

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

-- | Whether a snapshot is the value a manifest expects.
matches :: Expected -> StructuralValue -> P.Boolean
matches e s = case e, s of
  EInt n, SInt m -> n == m
  ENumber x, SNumber (NumberAtom y) -> sameNumber x y
  EChar c, SChar v -> c == codePointOf v
  EString a, SString b -> b.complete && a == textOf b.text
  EBoolean a, SBoolean b -> a == b
  EData c fields, SData (Qualified (ModuleName m) (Ident x)) items ->
    items.complete && c == m <> "." <> x && Array.length fields == Array.length items.items
      && and (Array.zipWith matches fields items.items)
  ERecord fields, SRecord items ->
    let
      wanted = Array.sortWith _.key (map (\f -> { key: expectedKey f.key, value: f.value }) fields)
      held = Array.sortWith _.key (map (\f -> { key: rowKey f.key, value: f.value }) items.items)
    in
      items.complete && Array.length wanted == Array.length held
        && and (Array.zipWith (\w h -> w.key == h.key && matches w.value h.value) wanted held)
  EVariant k v, SVariant l x -> expectedKey k == rowKey l && matches v x
  EFunction, SClosure -> true
  EFunction, SPartialApplication -> true
  EFunction, SContinuation -> true
  _, _ -> false

-- | A key as text, of the same spelling whichever side it comes from.
expectedKey :: ExpectedKey -> P.String
expectedKey = case _ of
  KField s -> "field " <> s
  KTag t -> "tag " <> t
  KPosition n -> "position " <> show n
  KEffect q -> "effect " <> q

rowKey :: RowKey -> P.String
rowKey = case _ of
  SymbolKey (Symbol s) -> "field " <> s
  TagKey (Tag t) -> "tag " <> t
  PositionKey n -> "position " <> show n
  EffectKey (Qualified (ModuleName m) (EffName x)) -> "effect " <> m <> "." <> x
  _ -> "region"

-- | Whether a fault is the one a manifest expects, as far as both runtimes observe
-- | one of its kind.
faultMatches :: ExpectedFault -> Fault -> P.Boolean
faultMatches e = case e.kind, _ of
  "refused", ForeignRefused q reason -> qualifiedText q == e.foreign && reason == e.reason
  "threw", ForeignThrew q message -> qualifiedText q == e.foreign && message == e.message
  "breached", ForeignBreached q _ -> qualifiedText q == e.foreign
  "actionRefused", NativeRefused reason -> reason == e.reason
  "actionThrew", NativeThrew message -> message == e.message
  "actionBreached", NativeBreached q _ -> qualifiedText q == e.foreign
  _, _ -> false

-- | `Mod.Sub.name` as the global `name` of the module `Mod.Sub`.
qualified :: P.String -> Qualified Ident
qualified g = case String.lastIndexOf (String.Pattern ".") g of
  Just i -> Qualified (ModuleName (String.take i g)) (Ident (String.drop (i + 1) g))
  Nothing -> Qualified (ModuleName "") (Ident g)

-- | Where loading stopped short: assembling the foreign table, or loading a module.
data Refusal
  = Assembling AssembleError
  | Loading LoadError

-- | A refusal as text, for what a manifest says it names.
refusalText :: Refusal -> P.String
refusalText = case _ of
  Loading err -> show err
  Assembling err -> case err of
    ModuleUnreachable m reason -> "ModuleUnreachable " <> moduleText m <> " " <> reason
    NoSuchExport m x -> "NoSuchExport " <> moduleText m <> " " <> x
    ExportNotCallable m x -> "ExportNotCallable " <> moduleText m <> " " <> x
    NoSignature m x -> "NoSignature " <> moduleText m <> " " <> x
    SignatureDisagrees m x declared given ->
      "SignatureDisagrees " <> moduleText m <> " " <> x <> " " <> show declared <> " " <> show given

-- | What running a fixture gave where the manifest says otherwise, one line each.
fixtureMismatches :: P.String -> Aff (P.Array P.String)
fixtureMismatches name = do
  manifest <- liftEffect (readManifest name)
  bytes <- liftEffect (traverse (\m -> readBytes (dir <> "/" <> m <> ".dmo")) manifest.modules)
  case traverse decode bytes of
    Left err -> pure [ name <> ": does not decode: " <> show err ]
    Right dmos -> do
      -- the identities every module is loaded against, asked for `Prim.Unit` first
      -- so that a `unit` result stands for the value those modules compare against
      identities <- liftEffect (Ref.new noIdentities)
      primUnit <- liftEffect (unitValue identities)
      foreignManifest <- liftEffect readForeignManifest
      case foreignManifest of
        Left err -> pure [ name <> ": " <> err ]
        Right held -> do
          assembled <- runBaseAff' (Foreigns.interpret nodeForeignsHandler (tableFor dir held primUnit dmos))
          case assembled of
            Left err -> pure (refused manifest (Assembling err))
            Right table -> do
              loaded <- liftEffect (runBaseEffect (Except.runExcept (Array.foldM load (emptyStore table identities) dmos)))
              case loaded of
                Left err
                  | manifest.loads -> pure [ name <> ": refused as " <> show err ]
                  -- a fault the manifest expects is one the named global's initialization ended at
                  | manifest.faults /= "" -> pure case err of
                      InitializationFailed q (Faults _) | qualifiedText q == manifest.faults -> []
                      _ -> [ name <> ": ended as " <> show err <> ", not as a fault initializing " <> manifest.faults ]
                  | isFault err -> pure [ name <> ": faulted as " <> show err <> ", where a refusal naming " <> manifest.mentions <> " was expected" ]
                  | otherwise -> pure (refused manifest (Loading err))
                Right store
                  | not manifest.loads -> pure [ name <> ": loaded, and a refusal naming " <> manifest.mentions <> " was expected" ]
                  | otherwise -> do
                      observations <- liftEffect (traverse (observed store) manifest.observe)
                      ran <- case manifest.run of
                        Nothing -> pure []
                        Just run -> running store run
                      pure (Array.catMaybes observations <> ran)
  where
  dir = fixturesRoot <> name

  isFault = case _ of
    InitializationFailed _ (Faults _) -> true
    _ -> false

  readForeignManifest = do
    let path = dir <> "/foreign-manifest.json"
    present <- exists path
    if not present then pure (Right Nothing)
    else do
      source <- readText path
      pure case ForeignManifest.parse "javascript" source of
        Left err -> Left ("the foreign manifest does not parse: " <> show err)
        Right parsed -> Right (Just parsed)

  refused manifest refusal
    | manifest.loads = [ name <> ": refused as " <> refusalText refusal ]
    | not (String.contains (String.Pattern manifest.mentions) (refusalText refusal)) =
        [ name <> ": refused as " <> refusalText refusal <> ", not naming " <> manifest.mentions ]
    | Just r <- Array.find (\listed -> listed.name == name) loadRefusals, not (r.refusal refusal) =
        [ name <> ": refused as " <> refusalText refusal <> ", not as the refusal it is listed for" ]
    | otherwise = []

  observed :: Store -> { global :: P.String, value :: Expected } -> Effect (Maybe P.String)
  observed store o = do
    names <- namesOf store
    case globalNamed store (qualified o.global) of
      Nothing -> pure (Just (name <> ": no global " <> o.global))
      Just slot -> do
        held <- Ref.read slot
        pure case held of
          Nothing -> Just (name <> ": " <> o.global <> " holds nothing")
          Just value ->
            if matches o.value (inspect defaultLimits names value) then Nothing
            else Just (name <> ": " <> o.global <> " holds something else")

  -- the entry point found as `steam run` finds one: only the named module's own
  -- globals are consulted, and the global must hold an action
  running :: Store -> Run -> Aff (P.Array P.String)
  running store run = do
    let entry@(Qualified m _) = qualified run.entry
    held <- case globalNamed store entry of
      Nothing -> pure Nothing
      Just slot -> map Just (liftEffect (Ref.read slot))
    case moduleNamed store m, held, run.end of
      Nothing, _, _ -> pure [ name <> ": no module " <> moduleText m ]
      _, Nothing, FailsToStart "noSuchGlobal" -> pure []
      _, Just (Just (VIO _)), FailsToStart reason -> pure [ name <> ": started, where it fails to start as " <> reason ]
      _, Just _, FailsToStart "notAnAction" -> pure []
      _, Nothing, _ -> pure [ name <> ": no global " <> run.entry ]
      _, Just (Just (VIO action)), end -> do
        outcome <- runBaseAff' (Except.runExcept (execute (registryOf store) action))
        effects <- fromEffectFnAff (eventsImpl dir)
        names <- liftEffect (namesOf store)
        pure case end, outcome of
          Produces wanted wantedEffects, Right value ->
            (if matches wanted (inspect defaultLimits names value) then [] else [ name <> ": produced something else" ])
              <> sameEffects wantedEffects effects
          FaultsWith wanted wantedEffects, Left (Faults fault) ->
            (if faultMatches wanted fault then [] else [ name <> ": faulted as " <> show fault <> ", not as " <> wanted.kind ])
              <> sameEffects wantedEffects effects
          _, Left failure -> [ name <> ": ended as " <> show failure ]
          _, Right _ -> [ name <> ": produced a value, where it faults" ]
      _, _, _ -> pure [ name <> ": " <> run.entry <> " holds no action" ]

  sameEffects wanted seen =
    if wanted == seen then []
    else [ name <> ": saw the effects " <> show seen <> ", not " <> show wanted ]

spec :: Spec Unit
spec = describe "Steam, over the bytecode fixtures" do
  it "runs every fixture as its manifest says" do
    names <- liftEffect (caseNames fixturesRoot)
    when (Array.null names) (fail "no fixtures found")
    mismatches <- traverse fixtureMismatches names
    Array.concat mismatches `shouldEqual` []

  -- a name left behind when its fixture is renamed or removed would check nothing
  it "lists only fixtures that exist as refused for a given reason" do
    names <- liftEffect (caseNames fixturesRoot)
    Array.filter (\n -> not (Array.elem n names)) (map _.name loadRefusals) `shouldEqual` []

-- | The refusal each of these fixtures must be refused with, which a manifest's
-- | `mentions` does not pin down: every shape refusal names the same effect, and
-- | a report naming the key, the operation, or the foreign says nothing of the
-- | counts or of what was wrong with it.
loadRefusals :: P.Array { name :: P.String, refusal :: Refusal -> P.Boolean }
loadRefusals =
  [ { name: "handler-cell-twice", refusal: loading cellTwice }
  , { name: "handler-cell-aliased", refusal: loading cellTwice }
  , { name: "handler-clause-twice", refusal: loading clauseTwice }
  , { name: "handler-clause-aliased", refusal: loading clauseTwice }
  , { name: "handler-hndl-clauses", refusal: loading clausesDisagree }
  , { name: "handler-tailhndl-clauses", refusal: loading clausesDisagree }
  , { name: "handler-hndl-cells", refusal: loading cellsDisagree }
  , { name: "handler-tailhndl-cells", refusal: loading cellsDisagree }
  , { name: "foreign-unreachable"
    , refusal: assembling case _ of
        ModuleUnreachable m _ -> m == host
        _ -> false
    }
  , { name: "foreign-no-export"
    , refusal: assembling case _ of
        NoSuchExport m "greet" -> m == host
        _ -> false
    }
  , { name: "foreign-not-callable"
    , refusal: assembling case _ of
        ExportNotCallable m "greet" -> m == host
        _ -> false
    }
  , { name: "foreign-no-signature"
    , refusal: assembling case _ of
        NoSignature m "greet" -> m == host
        _ -> false
    }
  , { name: "foreign-params-length"
    , refusal: assembling case _ of
        SignatureDisagrees m "greet" 1 2 -> m == host
        _ -> false
    }
  , { name: "foreign-no-entry"
    , refusal: loading case _ of
        ForeignWithoutImplementation q -> q == inHost "greet"
        _ -> false
    }
  , { name: "io-entry-arity-pure"
    , refusal: loading case _ of
        InterpreterEntryDeclaredAtWrongArity q 1 2 -> q == inIO "pure"
        _ -> false
    }
  , { name: "io-entry-arity-bind"
    , refusal: loading case _ of
        InterpreterEntryDeclaredAtWrongArity q 2 3 -> q == inIO "bind"
        _ -> false
    }
  -- Host's declaration takes one and Main supplies what the interface it was
  -- compiled against gave it
  , { name: "stale-foreign-call"
    , refusal: loading case _ of
        WrongForeignArity q 1 2 -> q == inHost "add"
        _ -> false
    }
  , { name: "stale-foreign-call-inner"
    , refusal: loading case _ of
        WrongForeignArity q 1 2 -> q == inHost "add"
        _ -> false
    }
  , { name: "stale-foreign-partial"
    , refusal: loading case _ of
        PapNotBelowArity q 1 1 -> q == inHost "add"
        _ -> false
    }
  -- a foreign the runtime carries out is still a declaration its module exports or
  -- does not
  , { name: "io-pure-unexported", refusal: notExported (inIO "pure") }
  , { name: "io-bind-unexported", refusal: notExported (inIO "bind") }
  , { name: "operation-by-foreign-unexported", refusal: notExported (Qualified (ModuleName "Base.Int") (Ident "add")) }
  , { name: "foreign-unexported", refusal: notExported (inHost "greet") }
  ]
  where
  loading p = case _ of
    Loading err -> p err
    Assembling _ -> false

  notExported name = loading case _ of
    NotExported q -> q == name
    _ -> false

  assembling p = case _ of
    Assembling err -> p err
    Loading _ -> false

  cellTwice = case _ of
    CellKeyTwice (M.KSymbol (Symbol "reading")) -> true
    _ -> false

  clauseTwice = case _ of
    ClauseTwice (OpName "bump") -> true
    _ -> false

  -- the handler entry holds two of each and the instruction supplies one
  clausesDisagree = case _ of
    HandlerClausesDisagree key 2 1 -> key == meter
    _ -> false

  cellsDisagree = case _ of
    HandlerCellsDisagree key 2 1 -> key == meter
    _ -> false

  meter = M.KEffect (Qualified (ModuleName "Main") (EffName "Meter"))

  host = ModuleName "Host"

  inHost = Qualified host <<< Ident

  inIO = Qualified (ModuleName "Base.IO") <<< Ident

qualifiedText :: Qualified Ident -> P.String
qualifiedText (Qualified (ModuleName m) (Ident x)) = m <> "." <> x

moduleText :: ModuleName -> P.String
moduleText (ModuleName m) = m
