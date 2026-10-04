-- | The kernel's vocabulary read from and written as generic values.
module Test.Stella.CLI.Session.BrokerCodec (spec) where

import Prelude

import Data.Argonaut.Core (fromNumber, fromString)
import Data.Array as Array
import Data.Either (Either(..), isLeft)
import Data.Foldable (for_)
import Data.List (List(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.String as String
import Data.Tuple (Tuple(..))
import Foreign.Object as Object
import Partial.Unsafe (unsafePartial)
import Stella.CLI.Session.Broker.Codec (class Guest, decodeCommand, encodeAnswer, fromGuest, handleOfToken, runCodec, toGuest, tokenOfHandle)
import Stella.CLI.Session.Value (WireValue(..))
import Stella.CLI.Session.Value.Shape (conforms)
import Stella.Compiler.Elaborate.Driver.Attempt (Response(..))
import Stella.Compiler.Elaborate.Environment.Catalog (EntrySort(..))
import Stella.Compiler.Elaborate.Protocol.Guest (bundle, elabModule, guestAnswerTy)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Elaborate.Vocabulary.Envelope (ConversationId(..), TransactionToken(..))
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle(..), HandleClass(..), SessionId(..))
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Vocabulary.Request (BuildRequest(..), Command(..), CommandAnswer(..), HandlerRequest(..), KernelAnswer(..), KernelRequest(..), ObserveRequest(..), ReportRequest(..), TermRequest(..))
import Stella.Compiler.Elaborate.Vocabulary.View (KindView(..), PayloadView(..), TypeView(..))
import Stella.Compiler.TypedCore (Constant(..), EffName(..), Ident(..), Literal(..), ModuleName(..), OpName(..), Qualified(..), RowElemKind(..), RowKey(..), Symbol(..), Tag(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore as Core
import Stella.Compiler.TypedCore.Domain (scalarString, scalarValue)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)

descriptor :: Descriptor
descriptor = case bundle of
  Right b -> b.descriptor
  Left _ -> Map.empty

h :: Int -> Handle
h slot = Handle { session: SessionId 1, handleClass: TypeClass, slot, generation: 7 }

qualified :: String -> String -> Qualified Ident
qualified m x = Qualified (ModuleName m) (Ident x)

-- | A value's generic form, and that form read back and written again. The two
-- | are compared as generic values, whose equality walks without recursion.
roundTrip :: forall a. Guest a => a -> Either String (Tuple WireValue WireValue)
roundTrip x = runCodec do
  w <- toGuest x
  back <- (fromGuest Nil w :: _ a)
  again <- toGuest back
  pure (Tuple w again)

sameAfterRoundTrip :: forall a. Guest a => a -> Boolean
sameAfterRoundTrip x = case roundTrip x of
  Right (Tuple w again) -> w == again
  Left _ -> false

-- | A value's generic form, as a `GuestAnswer` holds it, checked by the descriptor.
answerConforms :: KernelAnswer -> Either String Unit
answerConforms answer = case encodeAnswer (Returned (KernelAnswered answer)) of
  Left err -> Left err
  Right w -> case conforms descriptor guestAnswerTy w of
    Left p -> Left p.problem
    Right _ -> Right unit

-- | The command a guest would send asking this request.
asked :: KernelRequest -> Either String WireValue
asked request = runCodec ((\w -> WData (Qualified elabModule (Ident "Kernel")) [ w ]) <$> toGuest request)

requests :: Array KernelRequest
requests =
  [ BuildRequest (ExtendRow (h 0) (EffectKey (Qualified (ModuleName "M") (EffName "E"))) (EffectPayload (Qualified (ModuleName "M") (EffName "E")) [ h 1, h 2 ]) (h 3))
  , BuildRequest (TypeConstructor (h 0) (Qualified (ModuleName "M") (TyName "T")) [ KindFun KindType (KindRow RowEffect), KindVar (Core.KindVar "k") ])
  , BuildRequest (OpenForall (h 0) "a" KindAnyRow)
  , TermRequest (OpenLetRec (h 0) [ { hint: "f", type: h 1 }, { hint: "g", type: h 2 } ])
  , TermRequest (LiteralTerm (h 0) (LitString (unsafePartial (fromJust (scalarString "é")))))
  , TermRequest (LiteralTerm (h 0) (LitChar (unsafePartial (fromJust (scalarValue 0x1F600)))))
  , TermRequest (LocalVariable (h 0) (Ident "x"))
  , HandlerRequest (OpenHandle (h 0) (h 1) (TagKey (Tag "t")) (TypePayload (h 2)) (Just [ { key: SymbolKey (Symbol "k"), type: h 3 } ]) (h 4) (h 5) [ { op: OpName "op", full: true } ])
  , HandlerRequest (ReadCell (h 0) RegionKey)
  , ObserveRequest (LookupGlobal (qualified "M" "f"))
  , ObserveRequest LocalContext
  , ReportRequest (Throw [ TextPart "no", TypePart (h 0), NamePart (qualified "M" "g") ])
  ]

answers :: Array KernelAnswer
answers =
  [ UnitAnswer
  , HandleAnswer (h 0)
  , TypeViewAnswer (ConType (Qualified (ModuleName "M") (TyName "T")) [ KindFun KindType KindType ])
  , TypeViewAnswer (NormalRow { elementKind: Just RowType, known: [ { key: PositionKey 0, payload: TypePayload (h 1) } ], rigid: [ TyVar "r" ], flexible: [ { meta: h 2, type: h 3 } ] })
  , TypeViewAnswer (VarType (TyVar "a"))
  , ContextAnswer [ { name: Ident "x", type: h 0 } ]
  , DeclAnswer (Just { name: qualified "M" "f", sort: ValueEntry, kindVars: [ Core.KindVar "k" ], scheme: h 0, attributes: [ { name: qualified "M" "a", positional: [ ConstantRecord [ { label: Symbol "b", value: ConstantConstructor (qualified "M" "C") [ ConstantLiteral (LitInt 1) ] } ] ], keyword: [ { label: "k", value: ConstantValue (qualified "M" "v") } ] } ] })
  , DeclAnswer Nothing
  , NamesAnswer [ qualified "M" "a", qualified "M" "b" ]
  , BinderAnswer { binder: h 0, variable: h 1, bodyScope: h 2 }
  , SwitchKeyAnswer { binder: h 0, branches: [ { scope: h 1, payload: h 2 } ], fallback: Just { scope: h 3, residual: h 4 } }
  , HandlerAnswer { binder: h 0, returnClause: { variable: h 1, scope: h 2 }, clauses: [ { typeVariables: [ h 3 ], argument: h 4, continuation: Nothing, scope: h 5 } ] }
  ]

-- | A kind nested that deep in its first argument.
deepKind :: Int -> KindView
deepKind n = go n KindType
  where
  go 0 acc = acc
  go i acc = go (i - 1) (KindFun acc KindType)

-- | An attribute argument nested that deep.
deepConstant :: Int -> Constant
deepConstant n = go n (ConstantLiteral (LitInt 0))
  where
  go 0 acc = acc
  go i acc = go (i - 1) (if i `mod` 2 == 0 then ConstantConstructor (qualified "M" "C") [ acc ] else ConstantRecord [ { label: Symbol "k", value: acc } ])

spec :: Spec Unit
spec = describe "Stella.CLI.Session.Broker.Codec" do
  describe "handles as tokens" do
    it "writes a handle as its four fields and reads it back" do
      let handle = Handle { session: SessionId 3, handleClass: OccurrenceClass, slot: 0, generation: 2147483647 }
      handleOfToken (tokenOfHandle handle) `shouldEqual` Right handle

    it "refuses a token of another shape, saying nothing of what it holds" do
      let
        token = tokenOfHandle (h 0)
        secret = "secret-xyz"
      for_
        [ Object.delete "slot" token
        , Object.insert "extra" (fromNumber 1.0) token
        , Object.insert "slot" (fromNumber 1.5) token
        , Object.insert "slot" (fromNumber 2147483648.0) token
        , Object.insert "class" (fromString secret) token
        , Object.insert "session" (fromString secret) token
        ]
        \t -> case handleOfToken t of
          Left why -> why `shouldSatisfy` (not <<< String.contains (String.Pattern secret))
          Right _ -> fail "a token of another shape was read"

  describe "the vocabulary" do
    it "reads back every request it writes, as a command the descriptor admits" do
      for_ requests \request -> do
        sameAfterRoundTrip request `shouldEqual` true
        case asked request of
          Left err -> fail err
          Right w -> decodeCommand descriptor w `shouldEqual` Right (Kernel request)

    it "writes every answer as a GuestAnswer the descriptor admits, and reads it back" do
      for_ answers \answer -> do
        answerConforms answer `shouldEqual` Right unit
        sameAfterRoundTrip answer `shouldEqual` true

    it "writes the transaction answers without their tokens" do
      let token = TransactionToken { conversation: ConversationId 0, serial: 0 }
      map show (encodeAnswer (Returned (TransactionBegun token))) `shouldEqual` Right (show (WData (Qualified elabModule (Ident "TransactionBegun")) []))

    it "reads the guest's own transaction commands" do
      decodeCommand descriptor (WData (Qualified elabModule (Ident "BeginTransaction")) []) `shouldEqual` Right BeginTransaction
      decodeCommand descriptor (WData (Qualified elabModule (Ident "CommitTransaction")) []) `shouldEqual` Right CommitTransaction

    it "refuses a canonical value that is no GuestCommand, and a token that is no handle" do
      decodeCommand descriptor (WBoolean true) `shouldSatisfy` isLeft
      decodeCommand descriptor (WData (Qualified elabModule (Ident "Returned")) [ WData (Qualified elabModule (Ident "UnitAnswer")) [] ]) `shouldSatisfy` isLeft
      let badToken = WToken (Object.singleton "handle" (fromString "secret-xyz"))
      case decodeCommand descriptor (WData (Qualified elabModule (Ident "Kernel")) [ WData (Qualified elabModule (Ident "ObserveRequest")) [ WData (Qualified elabModule (Ident "GoalType")) [ badToken ] ] ]) of
        Left why -> why `shouldSatisfy` (not <<< String.contains (String.Pattern "secret-xyz"))
        Right _ -> fail "a token that is no handle was read"

  describe "a value as deep as it is" do
    it "converts a kind nested 100,000 deep without running out of stack" do
      sameAfterRoundTrip (deepKind 100000) `shouldEqual` true

    it "converts attributes nested 100,000 deep without running out of stack" do
      sameAfterRoundTrip (deepConstant 100000) `shouldEqual` true

    it "converts a list of 100,000 names without running out of stack" do
      let names = map (\i -> qualified "M" ("x" <> show i)) (Array.range 1 100000)
      sameAfterRoundTrip (NamesAnswer names) `shouldEqual` true
