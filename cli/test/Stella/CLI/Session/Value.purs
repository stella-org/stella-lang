-- | The generic value encoding and the descriptor check over it.
module Test.Stella.CLI.Session.Value (spec) where

import Prelude

import Data.Argonaut.Core (Json, fromArray, fromBoolean, fromNumber, fromObject, fromString, jsonNull, stringify)
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..), isRight)
import Data.Foldable (for_)
import Data.Maybe (fromJust)
import Data.Number (infinity, isNaN, nan)
import Data.Tuple (Tuple(..))
import Data.Map as Map
import Foreign.Object as Object
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Stella.CLI.Session.Frame (renderJson)
import Stella.CLI.Session.Value (WireValue(..), compareKeys, decodeValue, encodeValue, renderPath)
import Stella.CLI.Session.Value.Shape (conforms)
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.Elaborate.Protocol.Guest (bundle, elabModule, guestAnswerTy)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.TypedCore.Domain (scalarString, scalarValue)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), Symbol(..), Tag(..))
import Test.Spec (Spec, describe, it)
import Test.QuickCheck (class Arbitrary, Result(..), quickCheck', (<?>))
import Test.QuickCheck.Gen (Gen, arrayOf, chooseInt, elements, oneOf, resize, sized)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)

-- Building values ------------------------------------------------------------------------

ctor :: String -> String -> Qualified Ident
ctor m c = Qualified (ModuleName m) (Ident c)

elab :: String -> Array WireValue -> WireValue
elab c = WData (Qualified elabModule (Ident c))

text :: String -> WireValue
text s = WString (unsafePartial (fromJust (scalarString s)))

char :: Int -> WireValue
char c = WChar (unsafePartial (fromJust (scalarValue c)))

token :: String -> WireValue
token t = WToken (Object.singleton "handle" (fromString t))

symbol :: String -> Key
symbol = KSymbol <<< Symbol

record :: Array (Tuple String WireValue) -> WireValue
record = WRecord <<< map (\(Tuple k v) -> { key: symbol k, value: v })

-- | `Stella.Elab.List` of the elements, a chain of `Cons` as long as they are.
list :: Array WireValue -> WireValue
list = Array.foldr (\x rest -> elab "Cons" [ x, rest ]) (elab "Nil" [])

-- | A list of `n` names, built without recursion.
longList :: Int -> WireValue
longList n = go n (elab "Nil" [])
  where
  go 0 acc = acc
  go i acc = go (i - 1) (elab "Cons" [ elab "Name" [ text "M", text ("x" <> show i) ], acc ])

-- Generating values ----------------------------------------------------------------------

-- | Any value the constructors build, canonical or not: keys in any order and any
-- | number of times, negative positions, and names with lone surrogates.
newtype AnyValue = AnyValue WireValue

-- | A value a decoder accepts.
newtype CanonicalValue = CanonicalValue WireValue

instance Arbitrary AnyValue where
  arbitrary = AnyValue <$> genValue false

instance Arbitrary CanonicalValue where
  arbitrary = CanonicalValue <$> genValue true

genValue :: Boolean -> Gen WireValue
genValue canonical = sized go
  where
  go size
    | size <= 1 = leaf
    | otherwise = oneOf (NEA.cons' leaf [ dataValue size, recordValue size, variantValue size ])

  inner size = resize (size / 2) (sized go)

  leaf = oneOf $ NEA.cons'
    (WInt <$> chooseInt (-2147483648) 2147483647)
    [ WNumber <$> elements (NEA.cons' 0.0 [ negate 0.0, 1.5, 5.0e-324, nan, infinity, negate infinity ])
    , char <$> elements (NEA.cons' 0 [ 97, 0xE9, 0xFFFF, 0x1F600, 0x10FFFF ])
    , text <$> elements cleanTexts
    , WBoolean <$> elements (NEA.cons' true [ false ])
    , token <$> elements allTexts
    ]

  dataValue size = WData <$> (ctor <$> name <*> name) <*> arrayOf (inner size)

  recordValue size = do
    fields <- arrayOf ({ key: _, value: _ } <$> key <*> inner size)
    ordered <- if canonical then pure true else elements (NEA.cons' true [ false ])
    pure $ WRecord
      if ordered then Array.nubByEq (\a b -> a.key == b.key) (Array.sortBy (\a b -> compareKeys a.key b.key) fields)
      else fields

  variantValue size = WVariant <$> key <*> inner size

  name = elements (if canonical then cleanTexts else allTexts)

  key = oneOf $ NEA.cons'
    (symbol <$> name)
    [ KTag <<< Tag <$> name
    , KPosition <$> chooseInt (if canonical then 0 else -2) 3
    , (\m e -> KEffect (Qualified (ModuleName m) (EffName e))) <$> name <*> name
    ]

  cleanTexts = NEA.cons' "a" [ "b", "Z", "", "é", "\x1F600" ]

  allTexts = NEA.cons' "a" [ "b", "Z", "", "é", "\x1F600", "\xD800", "x\xDC00" ]

-- Reading and writing text ---------------------------------------------------------------------

decodeText :: String -> Either String WireValue
decodeText source = case jsonParser source of
  Left err -> Left ("not JSON: " <> err)
  Right json -> case decodeValue json of
    Left p -> Left (renderPath p.path <> ": " <> p.problem)
    Right v -> Right v

-- | Where a text is refused, or that it was not.
refusedAt :: String -> Either String String
refusedAt source = case jsonParser source of
  Left err -> Left ("not JSON: " <> err)
  Right json -> case decodeValue json of
    Left p -> Right (renderPath p.path)
    Right v -> Left ("accepted as " <> show v)

-- | The value's encoding as text, or where it has none.
encodeText :: WireValue -> String
encodeText v = case encodeValue v of
  Right json -> renderJson json
  Left p -> "no encoding at " <> renderPath p.path <> ": " <> p.problem

-- | Where encoding a value is refused, or that it was not.
encodingRefusedAt :: WireValue -> Either String String
encodingRefusedAt v = case encodeValue v of
  Left p -> Right (renderPath p.path)
  Right json -> Left ("encoded as " <> renderJson json)

numberText :: Number -> String
numberText n = encodeText (WNumber n)

descriptor :: Descriptor
descriptor = case bundle of
  Right b -> b.descriptor
  Left _ -> Map.empty

-- | Where a value is refused as a `GuestAnswer`, or that it was not.
answerRefusedAt :: WireValue -> Either String String
answerRefusedAt v = case conforms descriptor guestAnswerTy v of
  Left p -> Right (renderPath p.path)
  Right _ -> Left "accepted"

spec :: Spec Unit
spec = describe "Stella.CLI.Session.Value" do
  describe "encoding" do
    it "writes each form with exactly its members" do
      encodeText
        ( WData (ctor "M" "Pair")
            [ WInt 1
            , record [ Tuple "a" (WBoolean true) ]
            , WVariant (KTag (Tag "t")) (text "x")
            , token "h1"
            , char 97
            , WVariant (KEffect (Qualified (ModuleName "M") (EffName "E"))) (WVariant (KPosition 0) (WInt 0))
            ]
        ) `shouldEqual`
        ( "{\"data\":{\"module\":\"M\",\"name\":\"Pair\"},\"fields\":["
            <> "{\"int\":1},"
            <> "{\"record\":[{\"key\":{\"symbol\":\"a\"},\"value\":{\"boolean\":true}}]},"
            <> "{\"variant\":{\"key\":{\"tag\":\"t\"},\"value\":{\"string\":\"x\"}}},"
            <> "{\"token\":{\"handle\":\"h1\"}},"
            <> "{\"char\":97},"
            <> "{\"variant\":{\"key\":{\"effect\":{\"module\":\"M\",\"name\":\"E\"}},\"value\":{\"variant\":{\"key\":{\"position\":0},\"value\":{\"int\":0}}}}}"
            <> "]}"
        )

    it "writes a number as its bit pattern, high nibble first, every NaN as the one" do
      numberText 1.0 `shouldEqual` "{\"number\":\"3ff0000000000000\"}"
      numberText (negate 0.0) `shouldEqual` "{\"number\":\"8000000000000000\"}"
      numberText 5.0e-324 `shouldEqual` "{\"number\":\"0000000000000001\"}"
      numberText infinity `shouldEqual` "{\"number\":\"7ff0000000000000\"}"
      numberText (negate infinity) `shouldEqual` "{\"number\":\"fff0000000000000\"}"
      numberText nan `shouldEqual` "{\"number\":\"7ff8000000000000\"}"

    it "refuses a value a decoder would refuse, naming where" do
      let
        effect m e = KEffect (Qualified (ModuleName m) (EffName e))
        field k v = { key: k, value: v }
      for_
        [ Tuple "a negative position" (Tuple (WVariant (KPosition (-1)) (WInt 0)) ".variant.key.position")
        , Tuple "keys out of order"
            (Tuple (WRecord [ field (symbol "b") (WInt 0), field (symbol "a") (WInt 0) ]) ".record[1].key")
        , Tuple "a key twice"
            (Tuple (WRecord [ field (symbol "a") (WInt 0), field (symbol "a") (WInt 1) ]) ".record[1].key")
        , Tuple "a tag before a symbol"
            (Tuple (WRecord [ field (KTag (Tag "a")) (WInt 0), field (symbol "a") (WInt 0) ]) ".record[1].key")
        , Tuple "a lone surrogate in a constructor's name"
            (Tuple (WData (ctor "M" "\xD800") []) ".data.name")
        , Tuple "a lone surrogate in a module's name"
            (Tuple (WData (ctor "M\xDC00" "C") []) ".data.module")
        , Tuple "a lone surrogate in a record key"
            (Tuple (WRecord [ field (symbol "\xD800") (WInt 0) ]) ".record[0].key.symbol")
        , Tuple "a lone surrogate in an effect key, deep"
            ( Tuple
                (WData (ctor "M" "C") [ WInt 0, WVariant (effect "M\xD800" "E") (WInt 0) ])
                ".fields[1].variant.key.effect.module"
            )
        ]
        \(Tuple what (Tuple v path)) -> Tuple what (encodingRefusedAt v) `shouldEqual` Tuple what (Right path)

    it "writes only what reads back as itself, for any value" do
      liftEffect $ quickCheck' 2000 \(AnyValue v) -> case encodeValue v of
        Left _ -> Success
        Right json -> decodeText (renderJson json) == Right v <?> ("does not read back: " <> show v)

    it "writes every canonical value" do
      liftEffect $ quickCheck' 2000 \(CanonicalValue v) -> case encodeValue v of
        Left p -> Failed ("refused at " <> renderPath p.path <> ": " <> p.problem)
        Right json -> decodeText (renderJson json) == Right v <?> ("does not read back: " <> show v)

  describe "decoding" do
    it "reads back what it writes, for every form" do
      for_
        [ WInt 0
        , WInt (-2147483648)
        , WInt 2147483647
        , WNumber (negate 0.0)
        , WNumber 1.5
        , WNumber infinity
        , char 0
        , char 0x10FFFF
        , text "é\x1F600"
        , WBoolean false
        , WData (ctor "Stella.Elab" "Nil") []
        , record [ Tuple "a" (WInt 1), Tuple "b" (record []) ]
        , WVariant (KTag (Tag "t")) (list [ WInt 1, WInt 2 ])
        , token "h"
        ]
        \v -> decodeText (encodeText v) `shouldEqual` Right v

    it "reads any NaN pattern as NaN, and writes it back as the one" do
      case decodeText "{\"number\":\"7ff0000000000001\"}" of
        Right (WNumber n) -> do
          n `shouldSatisfy` isNaN
          numberText n `shouldEqual` "{\"number\":\"7ff8000000000000\"}"
        other -> fail ("read as " <> show other)

    it "reads -0 as the integer 0, and writes it back as 0" do
      decodeText "{\"int\":-0}" `shouldEqual` Right (WInt 0)
      encodeText (WInt 0) `shouldEqual` "{\"int\":0}"

    it "takes the canonical order of keys: kind first, then text by scalar value and positions by number" do
      decodeText
        ( "{\"record\":["
            <> "{\"key\":{\"symbol\":\"Z\"},\"value\":{\"int\":0}},"
            <> "{\"key\":{\"symbol\":\"a\"},\"value\":{\"int\":0}},"
            <> "{\"key\":{\"tag\":\"A\"},\"value\":{\"int\":0}},"
            <> "{\"key\":{\"position\":2},\"value\":{\"int\":0}},"
            <> "{\"key\":{\"position\":10},\"value\":{\"int\":0}},"
            <> "{\"key\":{\"effect\":{\"module\":\"A\",\"name\":\"z\"}},\"value\":{\"int\":0}},"
            <> "{\"key\":{\"effect\":{\"module\":\"B\",\"name\":\"a\"}},\"value\":{\"int\":0}}"
            <> "]}"
        ) `shouldSatisfy` isRight

    it "refuses what is not canonical, naming where" do
      for_
        [ Tuple "[]" ""
        , Tuple "{\"fields\":[]}" ""
        , Tuple "{\"int\":1,\"extra\":true}" ""
        , Tuple "{\"int\":2147483648}" ".int"
        , Tuple "{\"int\":1.5}" ".int"
        , Tuple "{\"int\":\"1\"}" ".int"
        , Tuple "{\"number\":\"3FF0000000000000\"}" ".number"
        , Tuple "{\"number\":\"3ff000000000000\"}" ".number"
        , Tuple "{\"number\":\"0x3ff00000000000\"}" ".number"
        , Tuple "{\"number\":1}" ".number"
        , Tuple "{\"char\":55296}" ".char"
        , Tuple "{\"char\":1114112}" ".char"
        , Tuple "{\"char\":-1}" ".char"
        , Tuple "{\"string\":\"\\ud800\"}" ".string"
        , Tuple "{\"boolean\":1}" ".boolean"
        , Tuple "{\"token\":[1]}" ".token"
        , Tuple "{\"data\":{\"module\":\"M\",\"name\":\"C\"}}" ""
        , Tuple "{\"data\":{\"module\":\"M\",\"name\":\"C\",\"x\":1},\"fields\":[]}" ".data"
        , Tuple "{\"data\":{\"module\":\"M\",\"name\":\"\\udc00\"},\"fields\":[]}" ".data.name"
        , Tuple "{\"data\":{\"module\":\"M\",\"name\":\"C\"},\"fields\":{}}" ".fields"
        , Tuple
            "{\"record\":[{\"key\":{\"symbol\":\"b\"},\"value\":{\"int\":1}},{\"key\":{\"symbol\":\"a\"},\"value\":{\"int\":2}}]}"
            ".record[1].key"
        , Tuple
            "{\"record\":[{\"key\":{\"symbol\":\"a\"},\"value\":{\"int\":1}},{\"key\":{\"symbol\":\"a\"},\"value\":{\"int\":2}}]}"
            ".record[1].key"
        , Tuple
            "{\"record\":[{\"key\":{\"tag\":\"a\"},\"value\":{\"int\":1}},{\"key\":{\"symbol\":\"a\"},\"value\":{\"int\":2}}]}"
            ".record[1].key"
        , Tuple "{\"record\":[{\"key\":{\"symbol\":\"a\"}}]}" ".record[0]"
        , Tuple "{\"record\":[{\"key\":{\"region\":0},\"value\":{\"int\":0}}]}" ".record[0].key"
        , Tuple "{\"variant\":{\"key\":{\"position\":-1},\"value\":{\"int\":0}}}" ".variant.key.position"
        , Tuple
            "{\"data\":{\"module\":\"M\",\"name\":\"C\"},\"fields\":[{\"int\":0},{\"record\":[{\"key\":{\"symbol\":\"a\"},\"value\":{\"char\":-1}}]}]}"
            ".fields[1].record[0].value.char"
        ]
        \(Tuple source path) -> Tuple source (refusedAt source) `shouldEqual` Tuple source (Right path)

  describe "a value as deep as it is long" do
    it "is written, rendered, parsed, read, and compared without running out of stack" do
      let v = longList 100000
      decodeText (encodeText v) `shouldEqual` Right v

  describe "rendering JSON" do
    it "writes what the host's serializer writes" do
      let
        sample = fromObject $ Object.fromFoldable
          [ Tuple "text" (fromString "quote \" backslash \\ newline \n tab \t nul \x0000 lone \xD800 é \x1F600")
          , Tuple "numbers" (fromArray [ fromNumber 0.0, fromNumber (negate 1.5), fromNumber 1.0e21, fromNumber 5.0e-324 ])
          , Tuple "nested" (fromArray [ fromArray [], fromObject Object.empty, jsonNull, fromBoolean false ])
          , Tuple "key \"quoted\"" (fromObject (Object.singleton "1" (fromString "x")))
          ]
      renderJson sample `shouldEqual` stringify sample

    it "renders nesting far deeper than the host's serializer can" do
      let rendered = renderJson (deep 100000 jsonNull)
      rendered `shouldEqual` (power "[" 100000 <> "null" <> power "]" 100000)

  describe "the descriptor check" do
    it "accepts an answer of the kernel's shape" do
      answerRefusedAt
        ( elab "Returned"
            [ elab "BinderAnswer" [ record [ Tuple "binder" (token "b"), Tuple "bodyScope" (token "s"), Tuple "variable" (token "v") ] ] ]
        ) `shouldEqual` Left "accepted"
      answerRefusedAt (elab "CandidateFailed" []) `shouldEqual` Left "accepted"
      answerRefusedAt
        ( elab "Returned"
            [ elab "SwitchCtorAnswer"
                [ record
                    [ Tuple "binder" (token "b")
                    , Tuple "branches" (list [ record [ Tuple "fields" (list [ token "f" ]), Tuple "scope" (token "s") ] ])
                    , Tuple "fallback" (elab "Just" [ token "x" ])
                    ]
                ]
            ]
        ) `shouldEqual` Left "accepted"

    it "accepts a list as long as a frame allows" do
      answerRefusedAt (elab "Returned" [ elab "NamesAnswer" [ longList 100000 ] ]) `shouldEqual` Left "accepted"

    it "refuses a canonical value of another shape, naming where" do
      for_
        [ Tuple "a boolean for the whole" (Tuple (WBoolean true) "")
        , Tuple "a constructor of another type" (Tuple (elab "Nil" []) "")
        , Tuple "an answer of another arity" (Tuple (elab "Returned" [ elab "UnitAnswer" [], elab "UnitAnswer" [] ]) ".fields")
        , Tuple "a view for a kernel answer" (Tuple (elab "Returned" [ elab "KindType" [] ]) ".fields[0]")
        , Tuple "a variant for a kernel answer" (Tuple (elab "Returned" [ WVariant (KTag (Tag "t")) (WInt 0) ]) ".fields[0]")
        , Tuple "a record short of a field"
            (Tuple (elab "Returned" [ elab "BinderAnswer" [ record [ Tuple "binder" (token "b"), Tuple "variable" (token "v") ] ] ]) ".fields[0].fields[0]")
        , Tuple "a record with a field besides"
            ( Tuple
                ( elab "Returned"
                    [ elab "AssumptionAnswer"
                        [ record [ Tuple "assumption" (token "a"), Tuple "bodyScope" (token "s"), Tuple "extra" (token "x") ] ]
                    ]
                )
                ".fields[0].fields[0]"
            )
        , Tuple "a token for a record field that is no token"
            ( Tuple
                ( elab "Returned"
                    [ elab "LetRecAnswer"
                        [ record [ Tuple "binder" (token "b"), Tuple "bodyScope" (token "s"), Tuple "variables" (token "v") ] ]
                    ]
                )
                ".fields[0].fields[0].record[2].value"
            )
        , Tuple "a token among names"
            (Tuple (elab "Returned" [ elab "NamesAnswer" [ list [ token "n" ] ] ]) ".fields[0].fields[0].fields[0]")
        , Tuple "an int for a token, deep in a list"
            (Tuple (elab "Returned" [ elab "LetRecAnswer" [ record [ Tuple "binder" (token "b"), Tuple "bodyScope" (token "s"), Tuple "variables" (list [ token "a", WInt 1 ]) ] ] ]) ".fields[0].fields[0].record[2].value.fields[1].fields[0]")
        ]
        \(Tuple what (Tuple v path)) -> Tuple what (answerRefusedAt v) `shouldEqual` Tuple what (Right path)

deep :: Int -> Json -> Json
deep 0 acc = acc
deep i acc = deep (i - 1) (fromArray [ acc ])

power :: String -> Int -> String
power s n = go n ""
  where
  go 0 acc = acc
  go i acc = go (i - 1) (acc <> s)
