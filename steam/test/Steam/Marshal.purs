-- | The boundary between the interpreter and a JavaScript implementation.
-- |
-- | **What these pin is the signature doing the work**: a host number is one
-- | representation and two Stella values, so what a result becomes is decided by the
-- | kind the manifest gives it and never by looking at the value.
module Test.Steam.Marshal (spec) where

import Prelude

import Prim as P

import Data.Either (Either(..))
import Data.Maybe (fromJust)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (try)
import Effect.Uncurried (runEffectFn1)
import Partial.Unsafe (unsafePartial)
import Steam.CLI.Marshal (bodyFor)
import Steam.Value (ActionOutcome(..), CtorId(..), ForeignOutcome(..), IOValue(..), Opaque, Value(..))
import Stella.CLI.Effect.Foreigns (HostExport)
import Stella.Compiler.ForeignManifest (ResultKind(..), Signature, ValueKind(..))
import Stella.Compiler.TypedCore.Domain (codePointOf, scalarString, scalarValue, textOf)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

foreign import echo :: HostExport
foreign import recording :: HostExport
foreign import receivedImpl :: Effect (P.Array P.String)
foreign import typesReceivedImpl :: Effect (P.Array P.String)
foreign import twoPointZero :: HostExport
foreign import twoPointFive :: HostExport
foreign import outsideInt32 :: HostExport
foreign import astral :: HostExport
foreign import twoScalars :: HostExport
foreign import halfAPair :: HostExport
foreign import loneSurrogate :: HostExport
foreign import yes :: HostExport
foreign import aString :: HostExport
foreign import anObject :: HostExport
foreign import aPromise :: Opaque
foreign import returnsPromise :: HostExport
foreign import isThePromise :: Opaque -> P.Boolean
foreign import refusing :: HostExport
foreign import refusingFromAnotherCopy :: HostExport
foreign import actionOf :: forall a. a -> HostExport
foreign import actionRefusing :: HostExport
foreign import actionThrowing :: HostExport
foreign import countingAction :: HostExport
foreign import performedImpl :: Effect P.Int

-- | The entry every body here is built for.
entry :: Qualified Ident
entry = Qualified (ModuleName "Host") (Ident "f")

-- | `Prim.Unit`, under an identity of this suite's choosing.
primUnit :: Value
primUnit = VData (CtorId 0) []

returning :: ResultKind -> Signature
returning result = { params: [], result }

call :: Signature -> HostExport -> P.Array Value -> Effect ForeignOutcome
call signature implementation = runEffectFn1 (bodyFor entry primUnit signature implementation)

-- | What an outcome amounts to, as a line an assertion can compare.
described :: ForeignOutcome -> P.String
described = case _ of
  Produced value -> "produced " <> shown value
  Refused reason -> "refused " <> reason
  Breached _ -> "breached"
  ArgumentNotOfKind position -> "argument " <> show position

describedAction :: ActionOutcome -> P.String
describedAction = case _ of
  ActionProduced value -> "produced " <> shown value
  ActionRefused reason -> "refused " <> reason
  ActionBreached name _ -> "breached by " <> show name

shown :: Value -> P.String
shown = case _ of
  VInt n -> "int " <> show n
  VNumber n -> "number " <> show n
  VChar c -> "char " <> show (codePointOf c)
  VString s -> "string " <> textOf s
  VBoolean b -> "boolean " <> show b
  VData (CtorId 0) [] -> "unit"
  VOpaque o -> if isThePromise o then "the promise" else "opaque"
  VIO _ -> "an action"
  _ -> "something else"

outcome :: Signature -> HostExport -> P.Array Value -> P.String -> Aff Unit
outcome signature implementation args expected = do
  answered <- liftEffect (call signature implementation args)
  described answered `shouldEqual` expected

-- | The action a body answered with, performed.
performed :: ResultKind -> HostExport -> Aff ActionOutcome
performed result implementation = do
  answered <- liftEffect (call (returning result) implementation [])
  case answered of
    Produced (VIO (IONative action)) -> liftEffect action
    other -> fail ("no action came back: " <> described other) *> pure (ActionRefused "")

spec :: Spec Unit
spec = describe "the foreign boundary" do

  describe "a result" do

    -- `Number.isInteger` deciding it would make `2.0 :: Number` an `Int`
    it "is wrapped by its kind and not by its value" do
      outcome (returning (AsValue AsInt)) twoPointZero [] "produced int 2"
      outcome (returning (AsValue AsNumber)) twoPointZero [] "produced number 2.0"

    it "breaches an int that is not whole, or outside an int32" do
      outcome (returning (AsValue AsInt)) twoPointFive [] "breached"
      outcome (returning (AsValue AsInt)) outsideInt32 [] "breached"

    it "takes an astral character as one char" do
      outcome (returning (AsValue AsChar)) astral [] "produced char 128512"

    it "breaches a char of two scalar values, or of half a pair" do
      outcome (returning (AsValue AsChar)) twoScalars [] "breached"
      outcome (returning (AsValue AsChar)) halfAPair [] "breached"

    it "breaches a string holding an unpaired surrogate" do
      outcome (returning (AsValue AsString)) aString [] "produced string stella"
      outcome (returning (AsValue AsString)) loneSurrogate [] "breached"

    it "breaches a host object where a boolean was owed" do
      outcome (returning (AsValue AsBoolean)) yes [] "produced boolean true"
      outcome (returning (AsValue AsBoolean)) anObject [] "breached"

    -- nothing of the host value is read for a `unit` result
    it "is Prim.Unit at unit, whatever the host returned" do
      outcome (returning (AsValue AsUnit)) anObject [] "produced unit"

    it "passes through at opaque, a promise among them" do
      outcome (returning (AsValue AsOpaque)) returnsPromise [] "produced the promise"

    -- nothing here waits, so a promise is a host object where a number was owed
    it "does not await a promise owed as a scalar" do
      outcome (returning (AsValue AsInt)) returnsPromise [] "breached"

  describe "a refusal" do

    it "is a refusal with the reason the helper was given, at every kind" do
      outcome (returning (AsValue AsInt)) refusing [] "refused nothing to give"
      outcome (returning (AsValue AsUnit)) refusing [] "refused nothing to give"
      outcome (returning (AsValue AsOpaque)) refusing [] "refused nothing to give"

    -- the limit of one instance being a precondition of the build, pinned so that it
    -- is not mistaken for an oversight
    it "built by a second copy of the helper is not recognised" do
      outcome (returning (AsValue AsInt)) refusingFromAnotherCopy [] "breached"
      outcome (returning (AsValue AsUnit)) refusingFromAnotherCopy [] "produced unit"
      outcome (returning (AsValue AsOpaque)) refusingFromAnotherCopy [] "produced opaque"

  describe "the arguments" do

    it "arrive as arguments, each as the host's own value" do
      _ <- liftEffect
        ( call
            { params: [ AsInt, AsString, AsChar, AsBoolean, AsNumber, AsUnit ]
            , result: AsValue AsInt
            }
            recording
            [ VInt 3
            , VString (unsafePartial (fromJust (scalarString "x")))
            , VChar (unsafePartial (fromJust (scalarValue 121)))
            , VBoolean true
            , VNumber 1.5
            , primUnit
            ]
        )
      types <- liftEffect typesReceivedImpl
      types `shouldEqual` [ "number", "string", "string", "boolean", "number", "undefined" ]
      received <- liftEffect receivedImpl
      received `shouldEqual` [ "3", "x", "y", "true", "1.5", "undefined" ]

    it "hand an opaque value over as the host value it was" do
      outcome { params: [ AsOpaque ], result: AsValue AsOpaque } echo
        [ VOpaque aPromise ]
        "produced the promise"

    -- the values are the interpreter's own, so this is above the implementation
    it "not of the kind their position gives them are reported by position" do
      outcome { params: [ AsInt ], result: AsValue AsInt } echo [ VBoolean true ]
        "argument 0"

  describe "an action" do

    -- a target entry constructs the action and performs nothing
    it "is returned and not performed" do
      before <- liftEffect performedImpl
      answered <- liftEffect (call (returning (AsAction AsInt)) countingAction [])
      described answered `shouldEqual` "produced an action"
      after <- liftEffect performedImpl
      after `shouldEqual` before

    it "produces what it returned, wrapped by the kind it was declared with" do
      outcome' <- performed (AsAction AsNumber) (actionOf 2.0)
      describedAction outcome' `shouldEqual` "produced number 2.0"

    it "is performed once, where it is performed" do
      before <- liftEffect performedImpl
      _ <- performed (AsAction AsInt) countingAction
      after <- liftEffect performedImpl
      after `shouldEqual` (before + 1)

    it "breaches, naming the entry, where it produced what its kind cannot be" do
      outcome' <- performed (AsAction AsInt) (actionOf 2.5)
      describedAction outcome' `shouldEqual` ("breached by " <> show entry)

    it "refuses through the helper" do
      outcome' <- performed (AsAction AsUnit) actionRefusing
      describedAction outcome' `shouldEqual` "refused no action today"

    -- the drive loop catches it and keeps it apart from a refusal
    it "throws out of performing, and not out of the body" do
      answered <- liftEffect (call (returning (AsAction AsUnit)) actionThrowing [])
      case answered of
        Produced (VIO (IONative action)) -> do
          thrown <- liftEffect (try action)
          case thrown of
            Left _ -> pure unit
            Right _ -> fail "performing did not throw"
        other -> fail ("no action came back: " <> described other)

    it "declared, and not a function, is a breach" do
      outcome (returning (AsAction AsUnit)) anObject [] "breached"
