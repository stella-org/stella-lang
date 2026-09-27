-- | How a value crosses between the interpreter and a JavaScript implementation
-- | ([Foreign Manifest](../../../docs/technical-references/05-Backend/04-Foreign-Manifest.md),
-- | D44).
-- |
-- | **Every Stella value is held in a shape of the interpreter's own**, a scalar
-- | included, so no export is a table entry as it stands. What makes one is the
-- | signature the manifest carries per foreign: arguments are unwrapped by the kind
-- | of their position, and the result is wrapped by the kind of the result, **by the
-- | kind and not by the value** — a host number is one representation and two
-- | Stella values (D37), so `2.0` owed as a `number` stays a `number`.
-- |
-- | **Wrapping is a check as well as a conversion.** What comes back is the host's
-- | and nothing has constrained it, so a host value its kind cannot be is a breach of
-- | the contract by the implementation, reported as a fault naming the entry rather
-- | than written into a register. Nothing is checked on the way in: the values are
-- | the interpreter's own.
-- |
-- | **Nothing here waits.** A value an implementation hands back is one it has
-- | already, and nothing tests for a thenable: a promise crosses where the kind is
-- | `opaque` and is a breach against any other kind.
module Steam.CLI.Marshal
  ( bodyFor
  , isCallable
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..), either, note)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.TraversableWithIndex (traverseWithIndex)
import Effect.Uncurried (EffectFn1, EffectFn2, mkEffectFn1, runEffectFn1, runEffectFn2)
import Stella.CLI.Effect.Foreigns (HostExport)
import Stella.Compiler.ForeignManifest (ResultKind(..), Signature, ValueKind(..))
import Stella.Compiler.TypedCore.Domain (scalarString, scalarStringOf, scalarsOf, textOf)
import Stella.Compiler.TypedCore.Name (Ident, Qualified)
import Steam.Value (ActionOutcome(..), ForeignBody, ForeignOutcome(..), IOValue(..), NativeAction, Value(..))
import Unsafe.Coerce (unsafeCoerce)

-- | A value on the host's side of the boundary, of a type nothing here can name.
foreign import data HostValue :: P.Type

-- | The body the interpreter calls for one foreign, from the implementation the
-- | manifest reached and the signature it carries.
-- |
-- | `unit` is `Prim.Unit` under the identity the registry assigns it, which is what
-- | a `unit` result stands for whatever the host returned.
-- |
-- | **A throw is not caught here.** It escapes the body, and the interpreter catches
-- | it where the body is called, keeping it apart from a refusal and from a breach
-- | ([Eval](../Eval.purs)); a throw where a returned action is performed is the drive
-- | loop's ([Drive](../Drive.purs)).
bodyFor :: Qualified Ident -> Value -> Signature -> HostExport -> ForeignBody
bodyFor name unit signature implementation = mkEffectFn1 \args ->
  case traverseWithIndex argument args of
    Left position -> pure (ArgumentNotOfKind position)
    Right given -> do
      answered <- runEffectFn2 applyImpl implementation given
      pure (resultOf name unit signature.result answered)
  where
  argument position value =
    note position (Array.index signature.params position >>= \kind -> unwrap kind value)

-- | A value as the host sees it, where it is of the kind its position gives it.
-- |
-- | **A `unit` parameter keeps its place and is not read**: the host sees
-- | `undefined` there, and omitting it would make the call shorter than the arity
-- | the declaration states.
unwrap :: ValueKind -> Value -> Maybe HostValue
unwrap kind value = case kind, value of
  AsInt, VInt n -> Just (unsafeCoerce n)
  AsNumber, VNumber n -> Just (unsafeCoerce n)
  AsChar, VChar c -> Just (unsafeCoerce (textOf (scalarStringOf [ c ])))
  AsString, VString s -> Just (unsafeCoerce (textOf s))
  AsBoolean, VBoolean b -> Just (unsafeCoerce b)
  AsUnit, _ -> Just nothingAtAll
  AsOpaque, VOpaque o -> Just (unsafeCoerce o)
  _, _ -> Nothing

-- | What a body answers with, from what the implementation returned.
-- |
-- | **A refusal is recognised before the kind is read**, by the runtime package's own
-- | brand and at every kind. A refusal built by a second copy of that package carries
-- | a brand this one does not know, so it faces the kind like any other host object:
-- | a breach where a scalar was owed, and — at `unit` and `opaque`, which read
-- | nothing of what came back — a success. One instance of the package is a
-- | precondition of the build rather than something checked here.
resultOf :: Qualified Ident -> Value -> ResultKind -> HostValue -> ForeignOutcome
resultOf name unit kind answered = case refusalOf answered of
  Just reason -> Refused reason
  Nothing -> case kind of
    AsValue owed -> either Breached Produced (wrap unit owed answered)
    -- **the host returns the action and constructs no `IO` value**: the boundary
    -- wraps it as the one a program halts on, and marshals what it produces when
    -- the drive loop performs it
    AsAction owed
      | isCallable answered -> Produced (VIO (IONative (perform name unit owed answered)))
      | otherwise -> Breached "declared an action, and the value is not a function"

-- | Performing an action a foreign returned: calling it with no arguments, and
-- | wrapping what it produced by the kind it was declared with.
perform :: Qualified Ident -> Value -> ValueKind -> HostValue -> NativeAction
perform name unit owed action = do
  produced <- runEffectFn1 performImpl action
  pure case refusalOf produced of
    Just reason -> ActionRefused reason
    Nothing -> either (ActionBreached name) ActionProduced (wrap unit owed produced)

-- | A host value as the interpreter holds it, or what is wrong with it.
wrap :: Value -> ValueKind -> HostValue -> Either P.String Value
wrap unit owed given = case owed of
  AsInt -> do
    n <- number
    -- a whole number within an int32 (D37); `Int.fromNumber` refuses anything else
    note (owing "not a whole number within 32 bits") (map VInt (Int.fromNumber n))
  AsNumber -> map VNumber number
  AsChar -> do
    text <- scalarText
    case scalarsOf text of
      [ c ] -> Right (VChar c)
      _ -> Left (owing "not one scalar value")
  AsString -> map VString scalarText
  AsBoolean -> map VBoolean (note (owing "not a boolean") (booleanOf given))
  -- nothing of the host value is read
  AsUnit -> Right unit
  AsOpaque -> Right (VOpaque (unsafeCoerce given))
  where
  owing why = "declared `" <> spelled owed <> "`, and the value is " <> why

  number = note (owing "not a number") (numberOf given)

  -- a Stella string holds no unpaired surrogate (D27), and `scalarString` refuses one
  scalarText = do
    text <- note (owing "not a string") (stringOf given)
    note (owing "a string holding an unpaired surrogate") (scalarString text)

-- | A kind as the manifest spells it.
spelled :: ValueKind -> P.String
spelled = case _ of
  AsInt -> "int"
  AsNumber -> "number"
  AsChar -> "char"
  AsString -> "string"
  AsBoolean -> "boolean"
  AsUnit -> "unit"
  AsOpaque -> "opaque"

refusalOf :: HostValue -> Maybe P.String
refusalOf = refusalOfImpl Nothing Just

numberOf :: HostValue -> Maybe P.Number
numberOf = numberOfImpl Nothing Just

stringOf :: HostValue -> Maybe P.String
stringOf = stringOfImpl Nothing Just

booleanOf :: HostValue -> Maybe P.Boolean
booleanOf = booleanOfImpl Nothing Just

foreign import refusalOfImpl
  :: (forall a. Maybe a) -> (forall a. a -> Maybe a) -> HostValue -> Maybe P.String

foreign import numberOfImpl
  :: (forall a. Maybe a) -> (forall a. a -> Maybe a) -> HostValue -> Maybe P.Number

foreign import stringOfImpl
  :: (forall a. Maybe a) -> (forall a. a -> Maybe a) -> HostValue -> Maybe P.String

foreign import booleanOfImpl
  :: (forall a. Maybe a) -> (forall a. a -> Maybe a) -> HostValue -> Maybe P.Boolean

-- | Whether a host value can be called. **The one shape of an export that can be
-- | checked**, a `.dmo` carrying no type; an arity cannot be read off one.
foreign import isCallable :: forall a. a -> P.Boolean

foreign import nothingAtAll :: HostValue

foreign import applyImpl :: EffectFn2 HostExport (P.Array HostValue) HostValue

foreign import performImpl :: EffectFn1 HostValue HostValue
