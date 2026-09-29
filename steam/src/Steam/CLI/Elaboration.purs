-- | What the elaboration profile adds to a session: the trusted `Stella.Elab`, the
-- | root boundary an invocation stands on, and what the client's answers are taken
-- | as.
-- |
-- | **`Stella.Elab` is the interpreter's own to install.** It comes from the
-- | compiler this interpreter is built with, as one bundle — the module, the
-- | fragment of the signature typing its handles, and the shape descriptor read off
-- | it — and no request loads it: a module of that name from anywhere else would
-- | decide what a guest's commands and answers are. It is lowered once when the
-- | session starts and installed when the handshake opens the profile, before the
-- | session says it is ready.
-- |
-- | **Who is at fault for an answer decides what it ends in.** One that is not a
-- | canonical value, or not a `GuestAnswer` by the descriptor, or not an answer at
-- | all, is the client breaking the protocol. One that passes both and still cannot
-- | be taken into the machine names a constructor the installed module does not
-- | have as the descriptor says, which is the interpreter disagreeing with itself.
module Steam.CLI.Elaboration
  ( Elaboration
  , prepare
  , Opened
  , install
  , TakenAnswer(..)
  , takeAnswer
  ) where

import Prelude

import Prim as P

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Run (EFFECT, Run, liftEffect)
import Run.Except as Except
import Steam.CLI.Wire (fromWire)
import Steam.Load (Store, internKeyIn, internOpIn, load)
import Steam.Value (Root, Value)
import Stella.CLI.Session.Kernel (abandonedKind, answeredKind, decodeAbandoned, decodeAnswered)
import Stella.CLI.Session.Peer (Reply)
import Stella.CLI.Session.ProtocolError (decodeProtocolError, protocolErrorKind)
import Stella.CLI.Session.Value (ValueProblem, decodeValue, renderPath)
import Stella.CLI.Session.Value.Shape (conforms)
import Stella.Compiler.Bytecode (Dmo)
import Stella.Compiler.Bytecode as Bytecode
import Stella.Compiler.Bytecode.Module (Key(..))
import Stella.Compiler.Elaborate.Protocol.Guest (bundle, commandOp, guestAnswerTy, kernelEffect)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Interface (noImports)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore (declareAnnotated, primSignature)
import Type.Row (type (+))

-- | `Stella.Elab` lowered, and the descriptor of its data types.
type Elaboration = { dmo :: Dmo, descriptor :: Descriptor }

-- | `Stella.Elab` made ready to install, or why it could not be: a failure here is
-- | a defect of the compiler the interpreter is built with.
prepare :: Either P.String Elaboration
prepare = do
  trusted <- bundle
  declared <- case declareAnnotated (trusted.withSignature primSignature) trusted.module of
    Left err -> Left ("it does not declare: " <> show err.error)
    Right declared -> Right declared
  mid <- case translate noImports trusted.module declared of
    Left err -> Left ("it does not translate: " <> show err)
    Right mid -> Right mid
  lowered <- case Bytecode.lower mid of
    Left err -> Left ("it does not lower: " <> show err)
    Right lowered -> Right lowered
  pure { dmo: lowered.dmo, descriptor: trusted.descriptor }

-- | What an open session answers its guests with: the store holding `Stella.Elab`,
-- | and the root boundary every invocation stands on.
type Opened = { store :: Store, root :: Root }

-- | Install `Stella.Elab` in the store and name the root boundary: the key of
-- | `Stella.Elab.Kernel` and its operation `command`.
install :: forall r. Elaboration -> Store -> Run (EFFECT + r) (Either P.String Opened)
install elaboration store = Except.runExcept (load store elaboration.dmo) >>= case _ of
  Left err -> pure (Left ("it does not load: " <> show err))
  Right installed -> liftEffect do
    key <- internKeyIn installed.identities (KEffect kernelEffect)
    op <- internOpIn installed.identities commandOp
    pure (Right { store: installed, root: { key, op } })

-- | What a response to a `kernel` request comes to.
data TakenAnswer
  -- | The answer, in the machine, to resume the guest with.
  = Resume Value
  -- | The host ended the attempt.
  | Abandon
  -- | The client broke the protocol, as how.
  | Violated P.String
  -- | The interpreter disagrees with itself, as where and why.
  | Inconsistent P.String

-- | Take a response to a `kernel` request. **A token's content is never part of
-- | what is said**: a refusal names a place and a rule, not a value.
takeAnswer :: Store -> Descriptor -> Reply -> Effect TakenAnswer
takeAnswer store descriptor reply
  | reply.kind == answeredKind = case decodeAnswered reply.payload of
      Nothing -> pure (Violated "an `answered` payload has exactly the field `answer`")
      Just json -> case decodeValue json of
        Left problem -> pure (Violated ("the answer is not a canonical value: " <> at problem))
        Right wire -> case conforms descriptor guestAnswerTy wire of
          Left problem -> pure (Violated ("the answer is not a GuestAnswer: " <> at problem))
          Right _ -> fromWire store wire <#> case _ of
            Left problem -> Inconsistent (at problem)
            Right value -> Resume value
  | reply.kind == abandonedKind = pure case decodeAbandoned reply.payload of
      Just _ -> Abandon
      Nothing -> Violated "an `abandoned` payload is empty"
  | reply.kind == protocolErrorKind = pure $ Violated case decodeProtocolError reply.payload of
      Just error -> "a `kernel` request was answered with the protocol error `" <> error.code <> "`"
      Nothing -> "a `kernel` request was answered with a protocol error"
  | otherwise = pure (Violated ("a `kernel` request was answered with `" <> reply.kind <> "`"))

at :: ValueProblem -> P.String
at problem = "answer" <> renderPath problem.path <> ": " <> problem.problem
