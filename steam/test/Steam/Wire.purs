-- | Interpreter values to and from a session's generic values, over a store holding
-- | the trusted `Stella.Elab`.
module Test.Steam.Wire (spec) where

import Prelude

import Prim as P

import Data.Argonaut.Core (fromString)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Map as Map
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Foreign.Object as Object
import Partial.Unsafe (unsafePartial)
import Run (runBaseEffect)
import Run.Except as Except
import Steam.CLI.Wire (Unencodable(..), fromWire, toWire)
import Steam.Foreign (emptyTable)
import Steam.Load (Store, emptyStore, load, namesOf, noIdentities, unitValue)
import Steam.Value (Callee(..), Continuation(..), IOValue(..), ModuleId(..), Opaque, Value(..))
import Stella.CLI.Session.Guest (ValueClass(..))
import Stella.CLI.Session.Value (WireValue(..), renderPath)
import Stella.Compiler.Bytecode (Dmo, decode, encode, lower)
import Stella.Compiler.Bytecode.Instr (FuncIx(..))
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.Elaborate.Protocol.Guest (elabModule, guestModule, withGuest)
import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.Primitive (PrimOp(..))
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..), Qualified(..), Symbol(..), declareAnnotated, primSignature)
import Stella.Compiler.TypedCore.Domain (scalarString)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Unsafe.Coerce (unsafeCoerce)

-- The trusted module, loaded ------------------------------------------------------------

elabDmo :: Either P.String Dmo
elabDmo = case declareAnnotated (withGuest primSignature) guestModule of
  Left err -> Left (show err.error)
  Right declared -> case translate noImports guestModule declared of
    Left err -> Left (show err)
    Right mid -> case lower mid of
      Left err -> Left (show err)
      Right out -> case encode out.dmo of
        Left err -> Left (show err)
        Right bytes -> case decode bytes of
          Left err -> Left (show err)
          Right dmo -> Right dmo

fresh :: Effect Store
fresh = map (emptyStore emptyTable) (Ref.new noIdentities)

-- | A store holding `Stella.Elab` and nothing else.
withElab :: Aff Store
withElab = liftEffect case elabDmo of
  Left err -> throw ("Stella.Elab did not lower: " <> err)
  Right dmo -> do
    store <- fresh
    loaded <- runBaseEffect (Except.runExcept (load store dmo))
    case loaded of
      Left err -> throw ("Stella.Elab did not load: " <> show err)
      Right s -> pure s

-- Building values ----------------------------------------------------------------------

elab :: P.String -> P.Array WireValue -> WireValue
elab c = WData (Qualified elabModule (Ident c))

text :: P.String -> WireValue
text s = WString (unsafePartial (fromJust (scalarString s)))

token :: P.String -> WireValue
token t = WToken (Object.singleton "handle" (fromString t))

record :: P.Array (Tuple P.String WireValue) -> WireValue
record = WRecord <<< map (\(Tuple k v) -> { key: KSymbol (Symbol k), value: v })

list :: P.Array WireValue -> WireValue
list = Array.foldr (\x rest -> elab "Cons" [ x, rest ]) (elab "Nil" [])

longList :: P.Int -> WireValue
longList n = go n (elab "Nil" [])
  where
  go 0 acc = acc
  go i acc = go (i - 1) (elab "Cons" [ elab "Name" [ text "M", text ("x" <> show i) ], acc ])

-- | An answer with a token, a list, a record inside a list, and an optional record.
answer :: WireValue
answer = elab "Returned"
  [ elab "SwitchKeyAnswer"
      [ record
          [ Tuple "binder" (token "b")
          , Tuple "branches" (list [ record [ Tuple "payload" (token "p"), Tuple "scope" (token "s") ] ])
          , Tuple "fallback" (elab "Just" [ record [ Tuple "residual" (token "r"), Tuple "scope" (token "t") ] ])
          ]
      ]
  ]

-- Going both ways ------------------------------------------------------------------------

-- | The value brought in, and taken back out.
roundTrip :: Store -> WireValue -> Aff (Either P.String WireValue)
roundTrip store wire = liftEffect do
  brought <- fromWire store wire
  case brought of
    Left p -> pure (Left ("refused at " <> renderPath p.path <> ": " <> p.problem))
    Right value -> do
      names <- namesOf store
      pure case toWire store names value of
        Left failure -> Left (unencodable failure)
        Right back -> Right back

-- | Where bringing a value in is refused, or that it was not.
refusedAt :: Store -> WireValue -> Aff (Either P.String P.String)
refusedAt store wire = liftEffect do
  brought <- fromWire store wire
  pure case brought of
    Left p -> Right (renderPath p.path)
    Right _ -> Left "brought in"

-- | Why a value was not taken out, or that it was.
takenOut :: Store -> Value -> Aff P.String
takenOut store value = liftEffect do
  names <- namesOf store
  pure case toWire store names value of
    Left failure -> unencodable failure
    Right _ -> "taken out"

unencodable :: Unencodable -> P.String
unencodable = case _ of
  NotEncodable class' -> "not encodable: " <> show class'
  Unaccounted _ -> "unaccounted"

spec :: Spec Unit
spec = describe "Steam.CLI.Wire" do
  describe "bringing a value in and taking it back out" do
    it "gives back the generic value it was given" do
      store <- withElab
      result <- roundTrip store answer
      result `shouldEqual` Right answer

    it "interns a record key no loaded module names" do
      store <- withElab
      before <- liftEffect (namesOf store)
      Array.elem (KSymbol (Symbol "residual")) (Array.fromFoldable (Map.values before.keys)) `shouldEqual` false
      _ <- roundTrip store answer
      after <- liftEffect (namesOf store)
      Array.elem (KSymbol (Symbol "residual")) (Array.fromFoldable (Map.values after.keys)) `shouldEqual` true

    it "carries a list as long as a frame allows" do
      store <- withElab
      let v = elab "Returned" [ elab "NamesAnswer" [ longList 100000 ] ]
      result <- roundTrip store v
      result `shouldEqual` Right v

  describe "bringing a value in" do
    it "refuses a constructor no loaded module has, and one of another arity, naming where" do
      store <- withElab
      for_
        [ Tuple "an unknown constructor" (Tuple (WData (Qualified (ModuleName "M") (Ident "Nope")) []) ".data")
        , Tuple "one too few fields" (Tuple (elab "Returned" []) ".fields")
        , Tuple "an unknown constructor inside" (Tuple (elab "Returned" [ WData (Qualified (ModuleName "M") (Ident "Nope")) [] ]) ".fields[0].data")
        , Tuple "a wrong arity inside a record"
            (Tuple (record [ Tuple "a" (elab "Just" []) ]) ".record[0].value.fields")
        ]
        \(Tuple what (Tuple v path)) -> do
          refused <- refusedAt store v
          Tuple what refused `shouldEqual` Tuple what (Right path)

  describe "taking a value out" do
    it "names the class of what has no generic encoding, wherever it stands" do
      store <- withElab
      captures <- liftEffect (Ref.new Map.empty)
      let
        closure = VClos { func: { module: ModuleId 0, func: FuncIx 0 }, captures }

        someObject :: Opaque
        someObject = unsafeCoerce { not: "a token" }
      for_
        [ Tuple closure ClassClosure
        , Tuple (VPap { callee: CalleePrim IntAdd, args: [ VInt 1 ] }) ClassPartialApplication
        , Tuple (VCont (Continuation [])) ClassContinuation
        , Tuple (VIO (IOPure (VInt 1))) ClassIO
        , Tuple (VOpaque someObject) ClassOpaque
        ]
        \(Tuple value class') -> do
          out <- takenOut store value
          out `shouldEqual` ("not encodable: " <> show class')
      cons <- liftEffect (fromWire store (list [ WInt 0 ]))
      case cons of
        Right (VData id [ _, rest ]) -> do
          deep <- takenOut store (VData id [ closure, rest ])
          deep `shouldEqual` ("not encodable: " <> show ClassClosure)
        _ -> fail "a list was not brought in"

    it "refuses a constructor identity nothing committed, and a committed one at another arity" do
      store <- withElab
      identities <- liftEffect (Ref.new noIdentities)
      unit' <- liftEffect (unitValue identities)
      bare <- liftEffect fresh
      out <- takenOut bare unit'
      out `shouldEqual` "unaccounted"
      nil <- liftEffect (fromWire store (elab "Nil" []))
      case nil of
        Right (VData id []) -> do
          wrong <- takenOut store (VData id [ VInt 1 ])
          wrong `shouldEqual` "unaccounted"
        _ -> fail "Nil was not brought in"

    it "takes a token out as the same JSON" do
      store <- withElab
      result <- roundTrip store (token "h")
      result `shouldEqual` Right (token "h")
