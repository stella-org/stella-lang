-- | Steam running the bytecode fixtures.
-- |
-- | A fixture is a directory of `fixtures/bytecode` holding lowered modules and a
-- | manifest saying which load, in what order, whether they load or are refused
-- | where they load, and what the named globals hold. The compiler's test suite
-- | writes them from hand-written Core and checks they are current; this reads the
-- | bytes as any consumer of a `.dmo` would and checks the manifest. The JavaScript
-- | backend checks the same manifests, so the two agree wherever both pass.
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
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Run (runBaseEffect)
import Run.Except as Except
import Steam.Foreign (emptyTable)
import Steam.Load (Store, emptyStore, globalNamed, load, namesOf, noIdentities)
import Steam.Structural (NumberAtom(..), StructuralValue(..), defaultLimits, inspect)
import Stella.Compiler.Bytecode (decode)
import Stella.Compiler.TypedCore (EffName(..), Ident(..), ModuleName(..), Qualified(..), RowKey(..), Symbol(..), Tag(..), codePointOf, sameNumber, textOf)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

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

type Manifest =
  { description :: P.String
  , modules :: P.Array P.String
  , loads :: P.Boolean
  , mentions :: P.String
  , observe :: P.Array { global :: P.String, value :: Expected }
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

-- | `Mod.Sub.name` as the global `name` of the module `Mod.Sub`.
qualified :: P.String -> Qualified Ident
qualified g = case String.lastIndexOf (String.Pattern ".") g of
  Just i -> Qualified (ModuleName (String.take i g)) (Ident (String.drop (i + 1) g))
  Nothing -> Qualified (ModuleName "") (Ident g)

-- | What running a fixture gave where the manifest says otherwise, one line each.
fixtureMismatches :: P.String -> Aff (P.Array P.String)
fixtureMismatches name = liftEffect do
  manifest <- readManifest name
  bytes <- traverse (\m -> readBytes (fixturesRoot <> name <> "/" <> m <> ".dmo")) manifest.modules
  case traverse decode bytes of
    Left err -> pure [ name <> ": does not decode: " <> show err ]
    Right dmos -> do
      store <- map (emptyStore emptyTable) (Ref.new noIdentities)
      loaded <- runBaseEffect (Except.runExcept (Array.foldM load store dmos))
      case loaded of
        Left err
          | manifest.loads -> pure [ name <> ": refused as " <> show err ]
          | String.contains (String.Pattern manifest.mentions) (show err) -> pure []
          | otherwise -> pure [ name <> ": refused as " <> show err <> ", not naming " <> manifest.mentions ]
        Right loadedStore
          | not manifest.loads -> pure [ name <> ": loaded, and a refusal naming " <> manifest.mentions <> " was expected" ]
          | otherwise -> map Array.catMaybes (traverse (observed loadedStore) manifest.observe)
  where
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

spec :: Spec Unit
spec = describe "Steam, over the bytecode fixtures" do
  it "runs every fixture as its manifest says" do
    names <- liftEffect (caseNames fixturesRoot)
    when (Array.null names) (fail "no fixtures found")
    mismatches <- traverse fixtureMismatches names
    Array.concat mismatches `shouldEqual` []
