-- | The `session` command: a long-lived process a compiler talks to.
-- |
-- | The session's messages travel on the channel this process was started with,
-- | reached through the `TRANSPORT` effect; on Node that is descriptor 3, and
-- | standard output and standard error stay for logs and for what host modules
-- | print. A session opens with a handshake that fixes its profile, loads modules
-- | and applies guest functions as it is asked, and answers a message it cannot take
-- | with a protocol error rather than ending.
-- |
-- | **`load`, `invoke`, and `close` run one at a time, in the order they arrived.**
-- | The receiver decides at once whether a request is admitted and puts an admitted
-- | one on a queue; `serve` takes the queue in order, so a module one request loads
-- | is there for the next, and nothing closes under a request still running. The
-- | receiver goes on reading meanwhile, which is what a response to a request of
-- | this side's own needs. `ping` is answered by the receiver and queues nothing.
-- |
-- | How the session ended is what `serve` answers with: normally after `close`, and
-- | otherwise as an `ErrorType` the command reports and exits by. Every final
-- | response is written out and the channel released before `serve` returns.
module Steam.CLI.Session
  ( Setup
  , serve
  ) where

import Prelude

import Prim as P

import Data.Array (elem)
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.AVar (AVar)
import Effect.AVar as AVar
import Effect.Aff (Aff, makeAff, nonCanceler)
import Effect.Aff.AVar as AffVar
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object as Object
import Run (AFF, EFFECT, Run, liftAff, liftEffect)
import Run.Except (EXCEPT)
import Run.Except as Except
import Steam.CLI.Assemble (entriesFor)
import Steam.CLI.Error (ErrorType(SessionChannelMissing, SessionRefused, SessionFailed, SessionDefect), SessionDefect(..), unreachable)
import Steam.CLI.Token as Token
import Steam.Eval (Failure(..), applyFunction)
import Steam.Foreign (emptyTable, insert)
import Steam.Load (Identities, LoadError(InitializationFailed), Store, emptyStore, globalNamed, load, moduleNamed, registryOf)
import Steam.Value (Value(..))
import Stella.CLI.Effect.FS (FS, readBytes)
import Stella.CLI.Effect.Foreigns (FOREIGNS)
import Stella.CLI.Effect.Transport (Channel, TRANSPORT, ownChannel)
import Stella.CLI.Session.Guest (GlobalName, InvocationFailure, InvocationReason(..), LoadFailure, LoadStage(..), Token, ValueClass(..), decodeInvoke, decodeLoad, encodeInvocationFailed, encodeLoadFailed, encodeLoaded, encodeReturned, invocationFailedKind, invokeKind, loadFailedKind, loadKind, loadedKind, returnedKind)
import Stella.CLI.Session.Peer (Answer, Incoming, Peer, SessionFailure, answer)
import Stella.CLI.Session.Peer as Peer
import Stella.CLI.Session.Protocol (Refusal, capabilityFor, closeKind, closedKind, decodeHello, emptyPayload, encodeReady, encodeRefusal, helloKind, negotiate, pingKind, pongKind, readyKind, refusedKind)
import Stella.CLI.Session.ProtocolError (ProtocolError(..), encodeProtocolError, protocolErrorKind)
import Stella.Compiler.Bytecode (decode)
import Stella.Compiler.ForeignManifest (Manifest)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Type.Row (type (+))

-- | What a session is started with: the manifest, where it was read from, the
-- | identities every module is loaded against, and `Prim.Unit` under them.
type Setup =
  { manifest :: Maybe Manifest
  , base :: P.String
  , identities :: Ref Identities
  , unit :: Value
  }

-- | Where the session stands. An open session holds the capabilities its handshake
-- | put in force. A closing one admits nothing more: it was asked to close, or it
-- | refused the handshake.
data Stage = AwaitingHello | Open (P.Array P.String) | Closing

-- | How a session ended.
data Ending
  = Closed
  | RefusedHello Refusal
  | Lost SessionFailure

-- | What `serve` runs, in the order it was admitted.
data Job
  = LoadJob P.String
  | InvokeJob { global :: GlobalName, arguments :: P.Array Token }
  | CloseJob

-- | What the queue holds. A failure of the channel is not among them: it is recorded
-- | apart and seen before the next job, and `Wake` only rouses a worker waiting on an
-- | empty queue to look.
data Work
  = Next { job :: Job, reply :: Answer -> Effect Unit }
  | Stop Ending
  | Wake

type SessionEffects r = (FS + FOREIGNS + TRANSPORT + EXCEPT ErrorType + AFF + EFFECT + r)

-- | Serve a session on this process's channel until it ends.
serve :: forall r. Setup -> Run (SessionEffects r) Unit
serve setup = ownChannel >>= case _ of
  Left reason -> Except.throw (SessionChannelMissing reason)
  Right channel -> do
    queue <- liftEffect AVar.empty
    lost <- liftEffect (Ref.new Nothing)
    peer <- liftEffect (open channel queue lost)
    ending <- work setup peer queue lost (emptyStore emptyTable setup.identities)
    case ending of
      Closed -> pure unit
      RefusedHello refusal -> Except.throw (SessionRefused refusal)
      Lost failure -> Except.throw (SessionFailed failure)

open :: Channel -> AVar Work -> Ref (Maybe SessionFailure) -> Effect Peer
open channel queue lost = do
  stage <- Ref.new AwaitingHello
  self <- Ref.new Nothing
  peer <- Peer.start channel
    { request: \incoming -> makeAff \done -> do
        admit stage queue incoming (done <<< Right)
        pure nonCanceler
    , notification: \incoming -> Ref.read self >>= notified incoming
    , failed: \failure -> do
        Ref.write (Just failure) lost
        enqueue queue Wake
    }
  Ref.write (Just peer) self
  pure peer

enqueue :: AVar Work -> Work -> Effect Unit
enqueue queue item = void (AVar.put item queue (\_ -> pure unit))

-- The one place requests are taken, in the order they were admitted.
--
-- **A lost channel is looked at before every job, and wins over the queue.** A
-- close is graceful and finishes what arrived before it; a channel gone is not, and
-- nothing still queued is started once it is known, since no one is left to answer.
-- The job running when the channel went finishes first: stopping one midway is the
-- business of cancellation.
work
  :: forall r
   . Setup
  -> Peer
  -> AVar Work
  -> Ref (Maybe SessionFailure)
  -> Store
  -> Run (SessionEffects r) Ending
work setup peer queue lost store = liftEffect (Ref.read lost) >>= case _ of
  Just failure -> do
    liftAff (release peer)
    pure (Lost failure)
  Nothing -> liftAff (AffVar.take queue) >>= \item -> liftEffect (Ref.read lost) >>= case _, item of
    Just failure, _ -> do
      liftAff (release peer)
      pure (Lost failure)
    Nothing, Wake -> work setup peer queue lost store
    Nothing, Stop ending -> do
      liftAff (release peer)
      pure ending
    Nothing, Next next -> run next
  where
  run :: { job :: Job, reply :: Answer -> Effect Unit } -> Run (SessionEffects r) Ending
  run { job, reply } = case job of
    CloseJob -> do
      liftEffect $ reply
        { kind: closedKind, payload: emptyPayload, afterwards: enqueue queue (Stop Closed) }
      work setup peer queue lost store
    LoadJob path -> loadInto setup store path >>= case _ of
      Loaded next name -> do
        liftEffect (reply (answer { kind: loadedKind, payload: encodeLoaded name }))
        work setup peer queue lost next
      LoadRefused failure -> do
        liftEffect (reply (answer { kind: loadFailedKind, payload: encodeLoadFailed failure }))
        work setup peer queue lost store
      LoadBroken defect -> broken defect
    InvokeJob request -> invokeIn store request >>= case _ of
      Returned token -> do
        liftEffect (reply (answer { kind: returnedKind, payload: encodeReturned token }))
        work setup peer queue lost store
      InvocationRefused failure -> do
        liftEffect $ reply $ answer
          { kind: invocationFailedKind, payload: encodeInvocationFailed failure }
        work setup peer queue lost store
      InvocationBroken defect -> broken defect

  -- a defect answers nothing: the session ends with it
  broken :: forall a. SessionDefect -> Run (SessionEffects r) a
  broken defect = do
    liftAff (release peer)
    Except.throw (SessionDefect defect)

-- | Write out what is queued, then release the channel.
release :: Peer -> Aff Unit
release peer = makeAff \done -> do
  Peer.shutdown peer (done (Right unit))
  pure nonCanceler

-- Admitting ------------------------------------------------------------------------------

-- | Decide at once what becomes of a request: answered now, or queued. **The
-- | checks are taken in one order**, and the first that applies answers: the stage
-- | the session stands at, then the kind, then the capability, and only then the
-- | payload the kind carries.
admit :: Ref Stage -> AVar Work -> Incoming -> (Answer -> Effect Unit) -> Effect Unit
admit stage queue incoming reply = Ref.read stage >>= case _, incoming.kind of
  Closing, kind -> problem (KindUnexpected kind)
  AwaitingHello, kind
    | kind == helloKind -> case decodeHello incoming.payload of
        Nothing -> problem (PayloadInvalid kind)
        Just hello -> case negotiate hello of
          Right ready -> do
            Ref.write (Open ready.capabilities) stage
            reply (answer { kind: readyKind, payload: encodeReady ready })
          Left refusal -> do
            Ref.write Closing stage
            reply
              { kind: refusedKind
              , payload: encodeRefusal refusal
              , afterwards: enqueue queue (Stop (RefusedHello refusal))
              }
    | otherwise -> problem (KindUnexpected kind)
  Open capabilities, kind
    | kind == helloKind -> problem (KindUnexpected kind)
    | kind == pingKind -> lifecycle kind do
        reply (answer { kind: pongKind, payload: emptyPayload })
    | kind == closeKind -> lifecycle kind do
        Ref.write Closing stage
        queued CloseJob
    | otherwise -> case capabilityFor kind of
        Nothing -> problem (KindUnknown kind)
        Just capability
          | not (capability `elem` capabilities) -> problem (CapabilityNotInForce kind)
          | kind == loadKind -> case decodeLoad incoming.payload of
              Nothing -> problem (PayloadInvalid kind)
              Just path -> queued (LoadJob path)
          | kind == invokeKind -> case decodeInvoke incoming.payload of
              Nothing -> problem (PayloadInvalid kind)
              Just request -> queued (InvokeJob request)
          | otherwise -> problem (KindUnknown kind)
  where
  -- a lifecycle request carries an empty payload
  lifecycle kind accepted
    | Object.isEmpty incoming.payload = accepted
    | otherwise = problem (PayloadInvalid kind)

  queued job = enqueue queue (Next { job, reply })

  problem error = reply (answer { kind: protocolErrorKind, payload: encodeProtocolError error })

lifecycleKinds :: P.Array P.String
lifecycleKinds = [ helloKind, pingKind, closeKind ]

notified :: Incoming -> Maybe Peer -> Effect Unit
notified incoming = case _ of
  Nothing -> pure unit
  Just peer
    -- a protocol error is not answered, or two sides could answer each other forever
    | incoming.kind == protocolErrorKind -> pure unit
    | incoming.kind `elem` lifecycleKinds ->
        Peer.notify peer protocolErrorKind
          (encodeProtocolError (KindUnexpected incoming.kind))
    | otherwise -> Peer.notify peer protocolErrorKind
        (encodeProtocolError (KindUnknown incoming.kind))

-- Loading ---------------------------------------------------------------------------------

data Loading
  = Loaded Store P.String
  | LoadRefused LoadFailure
  | LoadBroken SessionDefect

-- | Load the module at that path against the store.
-- |
-- | **The module, its globals, and the foreign entries it needed are one commit**:
-- | the entries are added to the store the module is loaded against, and only a load
-- | that succeeds hands that store back. A failure leaves the store as it was, the
-- | identities interned on the way and the host modules reached excepted.
loadInto :: forall r. Setup -> Store -> P.String -> Run (FS + FOREIGNS + EFFECT + r) Loading
loadInto setup store path = readBytes path >>= case _ of
  Left reason -> pure (refused Unreadable reason)
  Right bytes -> case decode bytes of
    Left err -> pure (refused NotBytecode (show err))
    Right dmo -> entriesFor setup.base setup.manifest setup.unit [ dmo ] >>= case _ of
      Left err -> pure (refused Foreigns (unreachable err))
      Right entries -> do
        let
          table = foldl (\t (Tuple name entry) -> insert name entry t) store.hostForeigns
            (Map.toUnfoldable entries :: P.Array _)
        outcome <- Except.runExcept (load (store { hostForeigns = table }) dmo)
        pure case outcome of
          Right loaded -> Loaded loaded (unModule dmo.name)
          Left (InitializationFailed name (Faults fault)) ->
            refused Initialization (showName name <> ": " <> show fault)
          Left (InitializationFailed _ failure) -> LoadBroken (DefectRunning failure)
          Left err -> refused Refused (show err)
  where
  refused stage detail = LoadRefused { stage, detail }

-- Invoking ----------------------------------------------------------------------------------

data Invocation
  = Returned Token
  | InvocationRefused InvocationFailure
  | InvocationBroken SessionDefect

-- | Apply a global to tokens.
-- |
-- | **Whether the global holds a function is asked before it is applied.**
-- | Applying what is not callable is a defect of the interpreter, so reading one
-- | into `notCallable` afterwards would pass off a genuine defect as the program's.
invokeIn
  :: forall r
   . Store
  -> { global :: GlobalName, arguments :: P.Array Token }
  -> Run (EFFECT + r) Invocation
invokeIn store { global, arguments } =
  case moduleNamed store (ModuleName global.module) of
    Nothing -> pure (refused NoSuchModule ("no module " <> global.module <> " is loaded"))
    Just _ -> case globalNamed store name of
      Nothing -> pure (refused NoSuchGlobal (showName name <> " is not a global of its module"))
      Just slot -> liftEffect (Ref.read slot) >>= case _ of
        Nothing -> pure (InvocationBroken (GlobalEmpty name))
        Just value
          | callable value -> do
              outcome <- Except.runExcept
                (applyFunction (registryOf store) value (map (VOpaque <<< Token.wrap) arguments))
              pure case outcome of
                Left (Faults fault) -> refused Fault (show fault)
                Left failure -> InvocationBroken (DefectRunning failure)
                Right (VOpaque o) | Just token <- Token.unwrap o -> Returned token
                Right other ->
                  refused (NotAToken (classOf other)) "what the function returned is not a token"
          | otherwise ->
              pure (refused NotCallable (showName name <> " does not hold a function"))
  where
  name = Qualified (ModuleName global.module) (Ident global.name)
  refused reason detail = InvocationRefused { reason, detail }

callable :: Value -> P.Boolean
callable = case _ of
  VClos _ -> true
  VPap _ -> true
  VCont _ -> true
  _ -> false

classOf :: Value -> ValueClass
classOf = case _ of
  VInt _ -> ClassInt
  VNumber _ -> ClassNumber
  VChar _ -> ClassChar
  VString _ -> ClassString
  VBoolean _ -> ClassBoolean
  VData _ _ -> ClassData
  VRecord _ -> ClassRecord
  VVariant _ _ -> ClassVariant
  VClos _ -> ClassClosure
  VPap _ -> ClassPartialApplication
  VCont _ -> ClassContinuation
  VIO _ -> ClassIO
  VOpaque _ -> ClassOpaque

unModule :: ModuleName -> P.String
unModule (ModuleName m) = m

showName :: Qualified Ident -> P.String
showName (Qualified (ModuleName m) (Ident x)) = m <> "." <> x
