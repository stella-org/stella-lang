-- | The `session` command: a long-lived process a compiler talks to.
-- |
-- | The session's messages travel on the channel this process was started with,
-- | reached through the `TRANSPORT` effect; on Node that is descriptor 3, and
-- | standard output and standard error stay for logs and for what host modules
-- | print. A session opens with a handshake that fixes its profile, loads modules
-- | and applies guest functions as it is asked, and answers a message it cannot take
-- | with a protocol error rather than ending.
-- |
-- | **Opening installs `Stella.Elab` before the session says it is ready.** An
-- | accepted `hello` does not answer at once: it puts the opening first on the
-- | queue, and `ready` goes out once the trusted module is in the store
-- | ([Elaboration](Elaboration.purs)). Every request arriving until then is answered
-- | after it: one admitted waits its turn, and an answer settled at once — a `pong`,
-- | a protocol error — is held behind the opening. So nothing a request of the
-- | session is answered with comes before `ready`, and `ready` means `Stella.Elab` is
-- | there. A message the channel layer refuses before it is a request at all — a
-- | payload that does not read, an envelope that is not one, a number used before —
-- | is answered by that layer where it arrives.
-- |
-- | **Opening installs `Stella.Syntax` too where `parse` is in force**, after
-- | `Base.Int`, which it depends on, both loaded as any module is. A client then
-- | finds `Base.Int` loaded, and loads no other of that name.
-- |
-- | **`load`, `invoke`, `parse`, and `close` run one at a time, in the order they
-- | arrived.**
-- | The receiver decides at once whether a request is admitted and puts an admitted
-- | one on a queue; `serve` takes the queue in order, so a module one request loads
-- | is there for the next, and nothing closes under a request still running. The
-- | receiver goes on reading meanwhile, which is what the answers to the `kernel`
-- | requests a running invocation makes need. Once open, `ping` is answered by the
-- | receiver and queues nothing.
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

import Data.Argonaut.Core (Json)
import Data.Array (elem)
import Data.Array as Array
import Data.Either (Either(..), either)
import Data.Foldable (foldM, foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..), stripPrefix)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.AVar (AVar)
import Effect.AVar as AVar
import Effect.Aff (Aff, Milliseconds(..), delay, makeAff, nonCanceler)
import Effect.Aff.AVar as AffVar
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object (Object)
import Foreign.Object as Object
import Run (AFF, EFFECT, Run, liftAff, liftEffect)
import Run.Except (EXCEPT)
import Run.Except as Except
import Steam.CLI.Assemble (entriesFor)
import Steam.CLI.Elaboration (Elaboration, Opened, TakenAnswer(..), install, takeAnswer)
import Steam.CLI.Error (ErrorType(SessionChannelMissing, SessionRefused, SessionFailed, SessionDefect), SessionDefect(..), unreachable)
import Steam.CLI.Token as Token
import Steam.CLI.Wire (Unencodable(..), classOf, fromWire, toWire)
import Steam.Eval (Bug(AskedOutsideInvocation, HaltedOutsideClosedRun), Failure(..), Halt(..), Outcome(..), Slice, invoke, invokeClosed, resumePaused, resumeWith)
import Steam.Foreign (emptyTable, insert)
import Steam.Load (Identities, Initialization(..), LoadError(InitializationFailed, InitializationHalted), Store, claimedByInterpreter, emptyStore, globalNamed, loadWith, moduleNamed, namesOf, registryOf)
import Steam.Value (Value(..))
import Stella.CLI.Effect.FS (FS, readBytes)
import Stella.CLI.Effect.Foreigns (FOREIGNS)
import Stella.CLI.Effect.Transport (Channel, TRANSPORT, ownChannel)
import Stella.CLI.Session.Guest (InvocationFailure, InvocationReason(..), InvokeRequest, LoadFailure, LoadStage(..), Token, cancelKind, cancelledKind, decodeCancel, decodeInvoke, decodeLoad, encodeInvocationFailed, encodeLoadFailed, encodeLoaded, encodeReturned, invocationFailedKind, invokeKind, loadFailedKind, loadKind, loadedKind, returnedKind)
import Stella.CLI.Session.Kernel (encodeKernel, kernelKind)
import Stella.CLI.Session.Peer (Answer, Incoming, Peer, SessionFailure(..), answer)
import Stella.CLI.Session.Peer as Peer
import Stella.CLI.Session.Parse (ExecutionReason(EffectRequested, ForeignRequested, InputInvalid, NotAParser, ParserNotCallable, ResultInvalid, StateRequested), ParseRequest, budgetExceededKind, decodeParse, encodeBudgetExceeded, encodeExecutionFailed, encodeParseFailed, encodeParsed, executionFailedKind, parseFailedKind, parseKind, parsedKind)
import Stella.CLI.Session.Parse as Parse
import Stella.CLI.Session.Protocol (Ready, Refusal, capabilityFor, closeKind, closedKind, decodeHello, emptyPayload, encodeReady, encodeRefusal, helloKind, kernelCapability, negotiate, parseCapability, pingKind, pongKind, readyKind, refusedKind)
import Stella.CLI.Session.ProtocolError (ProtocolError(..), encodeProtocolError, protocolErrorKind)
import Stella.CLI.Session.Syntax (positionShape, resultShape, treesShape)
import Stella.CLI.Session.Value (WireValue(..), decodeValue, encodeValue, renderPath)
import Stella.CLI.Session.Value.Shape (conformsTo)
import Stella.Compiler.Bytecode (decode)
import Stella.Compiler.ForeignManifest (Manifest)
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.Macro.Compiled (Compiled)
import Stella.Compiler.Primitive (entryOfOp)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Type.Row (type (+))

-- | What a session is started with: the manifest, where it was read from, the
-- | identities every module is loaded against, `Prim.Unit` under them, and
-- | `Stella.Elab` and `Stella.Syntax` ready to install.
type Setup =
  { manifest :: Maybe Manifest
  , base :: P.String
  , identities :: Ref Identities
  , unit :: Value
  , elaboration :: Elaboration
  -- | `Stella.Syntax` compiled, after the module it depends on, ready to install
  -- | where `parse` is in force.
  , syntax :: Compiled
  -- | How many steps a guest takes between two looks at the loop: a cancel, a
  -- | channel lost. Nothing a guest answers depends on it.
  , quantum :: P.Int
  }

-- | What an invocation is watched by while it runs: the channel lost, and the
-- | attempts a client has cancelled. **An attempt is cancelled only while it is
-- | queued or running**, so `active` holds those, and a cancel naming any other
-- | changes nothing.
type Watch =
  { lost :: Ref (Maybe SessionFailure)
  , active :: Ref (Set P.Int)
  , cancelled :: Ref (Set P.Int)
  }

-- | Where the session stands. An opening session has accepted the handshake and
-- | not yet said it is ready; an open one has. Both hold the capabilities the
-- | handshake put in force. A closing one admits nothing more: it was asked to
-- | close, or it refused the handshake.
data Stage
  = AwaitingHello
  | Opening (P.Array P.String)
  | Open (P.Array P.String)
  | Closing

-- | How a session ended.
data Ending
  = Closed
  | RefusedHello Refusal
  | Lost SessionFailure

-- | What `serve` runs, in the order it was admitted.
data Job
  = OpenJob Ready
  -- | An answer settled when the request arrived, held until `ready` has gone out.
  | ReplyJob Answer
  | LoadJob P.String
  | InvokeJob InvokeRequest
  | ParseJob ParseRequest
  | CloseJob

-- | What the queue holds. A failure of the channel is not among them: it is recorded
-- | apart and seen before the next job, and `Wake` only rouses a worker waiting on an
-- | empty queue to look.
data Work
  = Next { job :: Job, reply :: Answer -> Effect Unit }
  | Stop Ending
  | Wake

-- | What the worker carries from one job to the next: the store, and once the
-- | session is open, the root boundary and whether the client answers `kernel`
-- | requests.
type Held =
  { store :: Store
  , opened :: Maybe { root :: Opened, kernel :: P.Boolean, parse :: P.Boolean }
  }

type SessionEffects r = (FS + FOREIGNS + TRANSPORT + EXCEPT ErrorType + AFF + EFFECT + r)

-- | Serve a session on this process's channel until it ends.
serve :: forall r. Setup -> Run (SessionEffects r) Unit
serve setup = ownChannel >>= case _ of
  Left reason -> Except.throw (SessionChannelMissing reason)
  Right channel -> do
    queue <- liftEffect AVar.empty
    lost <- liftEffect (Ref.new Nothing)
    active <- liftEffect (Ref.new Set.empty)
    cancelled <- liftEffect (Ref.new Set.empty)
    let watch = { lost, active, cancelled }
    stage <- liftEffect (Ref.new AwaitingHello)
    withheld <- liftEffect (Ref.new false)
    peer <- liftEffect (open channel stage withheld queue watch)
    ending <- work setup peer stage withheld queue watch
      { store: emptyStore emptyTable setup.identities, opened: Nothing }
    case ending of
      Closed -> pure unit
      RefusedHello refusal -> Except.throw (SessionRefused refusal)
      Lost failure -> Except.throw (SessionFailed failure)

open :: Channel -> Ref Stage -> Ref P.Boolean -> AVar Work -> Watch -> Effect Peer
open channel stage withheld queue watch = do
  self <- Ref.new Nothing
  lastAttempt <- Ref.new 0
  peer <- Peer.start channel
    { request: \incoming -> makeAff \done -> do
        admit stage withheld lastAttempt watch queue incoming (done <<< Right)
        pure nonCanceler
    , notification: \incoming -> Ref.read self >>= notified incoming
    , failed: \failure -> do
        Ref.write (Just failure) watch.lost
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
  -> Ref Stage
  -> Ref P.Boolean
  -> AVar Work
  -> Watch
  -> Held
  -> Run (SessionEffects r) Ending
work setup peer stage withheld queue watch held = liftEffect (Ref.read watch.lost) >>= case _ of
  Just failure -> do
    liftAff (release peer)
    pure (Lost failure)
  Nothing -> liftAff (AffVar.take queue) >>= \item -> liftEffect (Ref.read watch.lost) >>= case _, item of
    Just failure, _ -> do
      liftAff (release peer)
      pure (Lost failure)
    Nothing, Wake -> work setup peer stage withheld queue watch held
    Nothing, Stop ending -> do
      liftAff (release peer)
      pure ending
    Nothing, Next next -> run next
  where
  continue = work setup peer stage withheld queue watch

  run :: { job :: Job, reply :: Answer -> Effect Unit } -> Run (SessionEffects r) Ending
  run { job, reply } = case job of
    -- `Stella.Elab` goes in before `ready` goes out, and the session is open once
    -- it has; a `close` admitted meanwhile has already made it closing
    OpenJob ready -> install setup.elaboration held.store >>= case _ of
      Left reason -> broken (ElaborationUnavailable reason)
      Right elab -> installSyntax ready elab.store >>= case _ of
        Left reason -> broken (SyntaxUnavailable reason)
        Right store -> do
          let opened = elab { store = store }
          liftEffect do
            reply (answer { kind: readyKind, payload: encodeReady ready })
            Ref.write false withheld
            Ref.modify_
              ( case _ of
                  Opening capabilities -> Open capabilities
                  other -> other
              )
              stage
          continue
            { store: opened.store
            , opened: Just
                { root: opened
                , kernel: kernelCapability `elem` ready.capabilities
                , parse: parseCapability `elem` ready.capabilities
                }
            }
    ReplyJob settled -> do
      liftEffect (reply settled)
      continue held
    CloseJob -> do
      liftEffect $ reply
        { kind: closedKind, payload: emptyPayload, afterwards: enqueue queue (Stop Closed) }
      continue held
    LoadJob path -> loadInto setup (maybe false _.parse held.opened) held.store path >>= case _ of
      Loaded next name -> do
        liftEffect (reply (answer { kind: loadedKind, payload: encodeLoaded name }))
        continue (held { store = next })
      LoadRefused failure -> do
        liftEffect (reply (answer { kind: loadFailedKind, payload: encodeLoadFailed failure }))
        continue held
      LoadBroken defect -> broken defect
    ParseJob request -> parseIn setup watch held.store request >>= case _ of
      ParseAnswered settled -> do
        liftEffect (reply (answer settled))
        continue held
      ParseBroken defect -> broken defect
      ParseLost failure -> do
        liftAff (release peer)
        pure (Lost failure)
    InvokeJob request -> case held.opened of
      -- an invocation is admitted only once the session has opened
      Nothing -> broken (ElaborationUnavailable "an invocation ran before the session opened")
      Just opened -> do
        -- one cancelled while it waited in the queue is not begun
        waited <- liftEffect (Set.member request.attempt <$> Ref.read watch.cancelled)
        invocation <-
          if waited then pure (InvocationRefused { reason: Cancelled, detail: "the client cancelled the invocation before it began" })
          else invokeIn setup peer watch held.store opened request
        -- an attempt settled is neither queued nor running, and no cancel reaches it
        liftEffect do
          Ref.modify_ (Set.delete request.attempt) watch.active
          Ref.modify_ (Set.delete request.attempt) watch.cancelled
        case invocation of
          Returned token -> do
            liftEffect (reply (answer { kind: returnedKind, payload: encodeReturned token }))
            continue held
          InvocationRefused failure -> do
            liftEffect $ reply $ answer
              { kind: invocationFailedKind, payload: encodeInvocationFailed failure }
            continue held
          InvocationBroken defect -> broken defect
          InvocationLost failure -> do
            liftAff (release peer)
            pure (Lost failure)

  -- `Base.Int` and `Stella.Syntax`, in that order, where `parse` is in force
  installSyntax ready store
    | parseCapability `elem` ready.capabilities =
        foldM (\acc dmo -> either (pure <<< Left) (\s -> lmapShow <$> Except.runExcept (loadWith ClosedInitialization s dmo)) acc)
          (Right store)
          setup.syntax.modules
    | otherwise = pure (Right store)
  lmapShow = case _ of
    Left err -> Left (show err)
    Right s -> Right s

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
-- |
-- | **Nothing is answered between an accepted `hello` and `ready`.** While
-- | `withheld` holds, an answer settled here — a `pong`, a protocol error — is queued
-- | behind the opening rather than written, so it goes out after `ready` and in the
-- | order its request arrived.
-- |
-- | **An `invoke`'s attempt is taken when it is admitted**, in the order requests
-- | arrive: one not above every attempt admitted before is refused, and one admitted
-- | is never taken again, whatever becomes of the invocation.
admit
  :: Ref Stage
  -> Ref P.Boolean
  -> Ref P.Int
  -> Watch
  -> AVar Work
  -> Incoming
  -> (Answer -> Effect Unit)
  -> Effect Unit
admit stage withheld lastAttempt watch queue incoming reply = Ref.read stage >>= case _, incoming.kind of
  Closing, kind -> problem (KindUnexpected kind)
  AwaitingHello, kind
    | kind == helloKind -> case decodeHello incoming.payload of
        Nothing -> problem (PayloadInvalid kind)
        Just hello -> case negotiate hello of
          Right ready -> do
            Ref.write (Opening ready.capabilities) stage
            Ref.write true withheld
            queued (OpenJob ready)
          Left refusal -> do
            Ref.write Closing stage
            reply
              { kind: refusedKind
              , payload: encodeRefusal refusal
              , afterwards: enqueue queue (Stop (RefusedHello refusal))
              }
    | otherwise -> problem (KindUnexpected kind)
  Opening capabilities, kind -> opened capabilities kind
  Open capabilities, kind -> opened capabilities kind
  where
  opened capabilities kind
    | kind == helloKind = problem (KindUnexpected kind)
    | kind == pingKind = lifecycle kind (respond (answer { kind: pongKind, payload: emptyPayload }))
    | kind == closeKind = lifecycle kind do
        Ref.write Closing stage
        queued CloseJob
    | otherwise = case capabilityFor kind of
        Nothing -> problem (KindUnknown kind)
        Just capability
          | not (capability `elem` capabilities) -> problem (CapabilityNotInForce kind)
          | kind == loadKind -> case decodeLoad incoming.payload of
              Nothing -> problem (PayloadInvalid kind)
              Just path -> queued (LoadJob path)
          | kind == invokeKind -> case decodeInvoke incoming.payload of
              Nothing -> problem (PayloadInvalid kind)
              Just request -> do
                last <- Ref.read lastAttempt
                if request.attempt <= last then problem AttemptNotAbove
                else do
                  Ref.write request.attempt lastAttempt
                  Ref.modify_ (Set.insert request.attempt) watch.active
                  queued (InvokeJob request)
          -- a cancel is noted, and answered, where it arrives: it is for an
          -- invocation queued or running, which the queue would hold it behind
          | kind == parseKind -> case decodeParse incoming.payload of
              Nothing -> problem (PayloadInvalid kind)
              Just request -> queued (ParseJob request)
          | kind == cancelKind -> case decodeCancel incoming.payload of
              Nothing -> problem (PayloadInvalid kind)
              Just attempt -> do
                current <- Ref.read watch.active
                when (Set.member attempt current) (Ref.modify_ (Set.insert attempt) watch.cancelled)
                respond (answer { kind: cancelledKind, payload: emptyPayload })
          -- `kernel` is a request this side makes, not one it answers
          | otherwise -> problem (KindUnexpected kind)

  -- a lifecycle request carries an empty payload
  lifecycle kind accepted
    | Object.isEmpty incoming.payload = accepted
    | otherwise = problem (PayloadInvalid kind)

  queued job = enqueue queue (Next { job, reply })

  -- an answer settled now, written now or held behind the opening
  respond settled = Ref.read withheld >>= if _ then queued (ReplyJob settled) else reply settled

  problem error = respond (answer { kind: protocolErrorKind, payload: encodeProtocolError error })

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
-- |
-- | **A module under the `Stella` prefix is refused by its name**, whatever the
-- | path holds: those names are the compiler's, and `Stella.Elab` in particular is
-- | the interpreter's own to install.
-- |
-- | **A session running parsers loads no module declaring a foreign the host
-- | carries out**, and refuses one before anything of it is reached or
-- | initialized: a parse is to depend on its input and its parser alone, and a
-- | module that reached the host as it initialized would carry what it saw into
-- | every parse after. The operations and the `IO` entries the interpreter carries
-- | out itself are not the host's, and stay admitted.
-- |
-- | **Such a session initializes every module it loads closed** ([Load](../Load.purs)):
-- | an initializer reaching an array made outside its module, which an invocation
-- | or another module's initializer may have written, would carry that history
-- | into the module's values and through them into a parse.
loadInto :: forall r. Setup -> P.Boolean -> Store -> P.String -> Run (FS + FOREIGNS + EFFECT + r) Loading
loadInto setup parsing store path = readBytes path >>= case _ of
  Left reason -> pure (refused Unreadable reason)
  Right bytes -> case decode bytes of
    Left err -> pure (refused NotBytecode (show err))
    Right dmo
      | reserved dmo.name ->
          pure (refused Refused (unModule dmo.name <> " is a name the compiler reserves"))
      | parsing, Just hosted <- Array.find (not <<< claimedByInterpreter <<< _.name) dmo.foreigns ->
          pure (refused Refused (showName hosted.name <> " is a foreign the host carries out, which a session running parsers does not load"))
      | otherwise -> entriesFor setup.base setup.manifest setup.unit [ dmo ] >>= case _ of
          Left err -> pure (refused Foreigns (unreachable err))
          Right entries -> do
            let
              table = foldl (\t (Tuple name entry) -> insert name entry t) store.hostForeigns
                (Map.toUnfoldable entries :: P.Array _)
            outcome <- Except.runExcept (loadWith initialization (store { hostForeigns = table }) dmo)
            pure case outcome of
              Right loaded -> Loaded loaded (unModule dmo.name)
              Left (InitializationFailed name (Faults fault)) ->
                refused Initialization (showName name <> ": " <> show fault)
              Left (InitializationHalted name halt) ->
                refused Initialization (showName name <> " reached outside the module as it was initialized: " <> show halt)
              Left (InitializationFailed _ failure) -> LoadBroken (DefectRunning failure)
              Left err -> refused Refused (show err)
  where
  refused stage detail = LoadRefused { stage, detail }
  initialization = if parsing then ClosedInitialization else OpenInitialization

-- | `Stella`, or a name under it.
reserved :: ModuleName -> P.Boolean
reserved (ModuleName name) = name == "Stella" || stripPrefix (Pattern "Stella.") name /= Nothing

-- Invoking ----------------------------------------------------------------------------------

data Invocation
  = Returned Token
  | InvocationRefused InvocationFailure
  | InvocationBroken SessionDefect
  -- | The session cannot go on: the channel went, or the client broke the protocol
  -- | answering the invocation's `kernel` request.
  | InvocationLost SessionFailure

-- | Apply a global to tokens, as an attempt standing on the root boundary.
-- |
-- | **Whether the global holds a function is asked before it is applied.**
-- | Applying what is not callable is a defect of the interpreter, so reading one
-- | into `notCallable` afterwards would pass off a genuine defect as the program's.
-- |
-- | **Each command the guest asks goes to the client as a `kernel` request**, and
-- | the invocation waits for the answer. The names a command is written with are
-- | read from the identities as they stand when it is sent: taking an answer in may
-- | have interned a key the next command carries.
invokeIn
  :: forall r
   . Setup
  -> Peer
  -> Watch
  -> Store
  -> { root :: Opened, kernel :: P.Boolean, parse :: P.Boolean }
  -> InvokeRequest
  -> Run (AFF + EFFECT + r) Invocation
invokeIn setup peer watch store opened request =
  case moduleNamed store (ModuleName request.global.module) of
    Nothing -> pure (refused NoSuchModule ("no module " <> request.global.module <> " is loaded"))
    Just _ -> case globalNamed store name of
      Nothing -> pure (refused NoSuchGlobal (showName name <> " is not a global of its module"))
      Just slot -> liftEffect (Ref.read slot) >>= case _ of
        Nothing -> pure (InvocationBroken (GlobalEmpty name))
        Just value
          | callable value ->
              Except.runExcept
                ( invoke (registryOf store) opened.root.root (allowed 0) value
                    (map (VOpaque <<< Token.wrap) request.arguments)
                ) >>= continued 0
          | otherwise ->
              pure (refused NotCallable (showName name <> " does not hold a function"))
  where
  name = Qualified (ModuleName request.global.module) (Ident request.global.name)

  refused reason detail = InvocationRefused { reason, detail }

  -- the steps the next stretch may take: a quantum, or what is left of the budget
  allowed spent = min setup.quantum (request.budget - spent)

  cancelledNow = Set.member request.attempt <$> Ref.read watch.cancelled

  continued :: P.Int -> Either Failure Slice -> Run (AFF + EFFECT + r) Invocation
  continued before = case _ of
    Left (Faults fault) -> pure (refused Fault (show fault))
    Left failure -> pure (InvocationBroken (DefectRunning failure))
    Right slice -> outcome (before + slice.spent) slice.outcome

  outcome :: P.Int -> Outcome -> Run (AFF + EFFECT + r) Invocation
  outcome spent = case _ of
    Done (VOpaque o) | Just token <- Token.unwrap o -> pure (Returned token)
    Done other ->
      pure (refused (NotAToken (classOf other)) "what the function returned is not a token")
    -- an invocation stands on a root boundary, which ends no run
    Halted _ -> pure (InvocationBroken (DefectRunning (Bug HaltedOutsideClosedRun)))
    -- a pause needs another step: none is left, or the loop is let go round first,
    -- so that a cancel or a channel lost meanwhile is seen before the next stretch
    Paused pause
      | spent >= request.budget ->
          pure (refused BudgetExhausted ("the guest took the " <> show request.budget <> " steps its budget allows and needed another"))
      | otherwise -> do
          liftAff (delay (Milliseconds 0.0))
          gone <- liftEffect (Ref.read watch.lost)
          stop <- liftEffect cancelledNow
          case gone of
            Just failure -> pure (InvocationLost failure)
            Nothing
              | stop -> pure (refused Cancelled "the client cancelled the invocation")
              | otherwise -> Except.runExcept (resumePaused (allowed spent) pause) >>= continued spent
    Asked argument suspension
      | not opened.kernel ->
          pure (refused KernelNotInForce "the guest asked the kernel, and `kernel` is not in force")
      | otherwise -> liftEffect cancelledNow >>=
          if _ then pure (refused Cancelled "the client cancelled the invocation")
          else do
            names <- liftEffect (namesOf store)
            case toWire store names argument of
              Left (NotEncodable class') ->
                pure (refused (CommandNotEncodable class') "the guest asked with a value the wire has no form for")
              Left (Unaccounted why) -> pure (InvocationBroken (ValueUnaccounted why))
              Right wire -> case encodeValue wire of
                Left problem ->
                  pure (InvocationBroken (CommandUnencodable ("command" <> renderPath problem.path <> ": " <> problem.problem)))
                Right command ->
                  liftAff (Peer.request peer kernelKind (encodeKernel { attempt: request.attempt, command })) >>= case _ of
                    Left failure -> pure (InvocationLost failure)
                    -- a cancel taken while the client answered wins over what it answered
                    Right reply -> liftEffect cancelledNow >>=
                      if _ then pure (refused Cancelled "the client cancelled the invocation")
                      else liftEffect (takeAnswer store setup.elaboration.descriptor reply) >>= case _ of
                        Resume answer' -> Except.runExcept (resumeWith (allowed spent) suspension answer') >>= continued spent
                        Abandon -> pure (refused Abandoned "the host ended the attempt")
                        Violated why -> pure (InvocationLost (PeerViolated why))
                        Inconsistent why -> pure (InvocationBroken (AnswerInconsistent why))

callable :: Value -> P.Boolean
callable = case _ of
  VClos _ -> true
  VPap _ -> true
  VCont _ -> true
  _ -> false

unModule :: ModuleName -> P.String
unModule (ModuleName m) = m

showName :: Qualified Ident -> P.String
showName (Qualified (ModuleName m) (Ident x)) = m <> "." <> x

-- Parsing ---------------------------------------------------------------------------------

data Parsing
  = ParseAnswered { kind :: P.String, payload :: Object Json }
  | ParseBroken SessionDefect
  -- | The channel went while the parser ran.
  | ParseLost SessionFailure

-- | Run the parser a global holds on the input, as a closed run of the trusted
-- | `Stella.Syntax.runParser`.
-- |
-- | **What the session holds is no type**, so what it checks is what each value
-- | is: the global holds a `Stella.Syntax.Parser` whose function is callable, the
-- | input is a canonical value of the type its place wants, and so is what the
-- | parser returns. A failure of any of them, of the parser executing, and an
-- | effect it handles nowhere, is the parser's, answered as `executionFailed`;
-- | `Stella.Syntax` not being as the session installed it is the session's own
-- | defect.
parseIn :: forall r. Setup -> Watch -> Store -> ParseRequest -> Run (AFF + EFFECT + r) Parsing
parseIn setup watch store request =
  case moduleNamed store (ModuleName request.parser.module) of
    Nothing -> failed Parse.NoSuchModule ("no module " <> request.parser.module <> " is loaded")
    Just _ -> case globalNamed store name of
      Nothing -> failed Parse.NoSuchGlobal (showName name <> " is not a global of its module")
      Just slot -> liftEffect (Ref.read slot) >>= case _ of
        Nothing -> pure (ParseBroken (GlobalEmpty name))
        Just parser -> case Map.lookup (syntaxName "Parser") store.ctors, parser of
          Nothing, _ -> pure (ParseBroken (SyntaxUnavailable "it declares no constructor Parser"))
          Just ctor, VData id [ function ]
            | id == ctor.id ->
                if callable function then withInput parser
                else failed ParserNotCallable (showName name <> " holds a parser whose function is not callable")
          _, _ -> failed NotAParser (showName name <> " does not hold a parser")
  where
  name = Qualified (ModuleName request.parser.module) (Ident request.parser.name)

  failed reason detail = pure (ParseAnswered { kind: executionFailedKind, payload: encodeExecutionFailed { reason, detail } })

  withInput parser = do
    trees <- input "trees" treesShape request.input.trees
    end <- input "end" positionShape request.input.end
    case trees, end of
      Left why, _ -> pure why
      _, Left why -> pure why
      Right t, Right e -> case globalNamed store (syntaxName "runParser") of
        Nothing -> pure (ParseBroken (SyntaxUnavailable "it declares no global runParser"))
        Just slot -> liftEffect (Ref.read slot) >>= case _ of
          Nothing -> pure (ParseBroken (GlobalEmpty (syntaxName "runParser")))
          Just runParser ->
            Except.runExcept (invokeClosed (registryOf store) (allowed 0) runParser [ parser, t, e ]) >>= continued 0

  -- a part of the input, read and checked before it is taken into the machine
  input part shape json = case decodeValue json of
    Left problem -> pure (Left (inputInvalid part problem))
    Right wire -> case conformsTo setup.syntax.descriptor shape wire of
      Left problem -> pure (Left (inputInvalid part problem))
      Right _ -> liftEffect (fromWire store wire) <#> case _ of
        Left problem -> Left (ParseBroken (SyntaxUnavailable ("the input" <> renderPath problem.path <> ": " <> problem.problem)))
        Right value -> Right value

  inputInvalid part problem = ParseAnswered
    { kind: executionFailedKind
    , payload: encodeExecutionFailed
        { reason: InputInvalid, detail: "input." <> part <> renderPath problem.path <> ": " <> problem.problem }
    }

  allowed spent = min setup.quantum (request.budget - spent)

  continued :: P.Int -> Either Failure Slice -> Run (AFF + EFFECT + r) Parsing
  continued before = case _ of
    Left (Faults fault) -> failed Parse.Fault (show fault)
    Left failure -> pure (ParseBroken (DefectRunning failure))
    Right slice -> outcome (before + slice.spent) slice.outcome

  outcome :: P.Int -> Outcome -> Run (AFF + EFFECT + r) Parsing
  outcome spent = case _ of
    Done value -> returned value
    Halted halt -> case halt of
      EffectPerformed key -> do
        names <- liftEffect (namesOf store)
        failed EffectRequested
          ("the parser performed " <> maybe "an effect" show (Map.lookup key names.keys) <> " and handles it nowhere")
      HostForeignCalled foreign' ->
        failed ForeignRequested ("the parser called " <> showName foreign' <> ", which the host carries out")
      StateNotOwned op ->
        failed StateRequested ("the parser reached an array it did not make, by " <> showName (entryOfOp op))
      OperationWithheld op ->
        failed Parse.OperationWithheld ("the parser called " <> showName (entryOfOp op) <> ", which no parser may")
    -- a closed run stands on no root boundary
    Asked _ _ -> pure (ParseBroken (DefectRunning (Bug AskedOutsideInvocation)))
    -- as an invocation's: none is left, or the loop is let go round first
    Paused pause
      | spent >= request.budget ->
          pure (ParseAnswered { kind: budgetExceededKind, payload: encodeBudgetExceeded })
      | otherwise -> do
          liftAff (delay (Milliseconds 0.0))
          liftEffect (Ref.read watch.lost) >>= case _ of
            Just failure -> pure (ParseLost failure)
            Nothing -> Except.runExcept (resumePaused (allowed spent) pause) >>= continued spent

  returned value = do
    names <- liftEffect (namesOf store)
    case toWire store names value of
      Left (NotEncodable class') -> failed ResultInvalid ("the parser returned a value holding a " <> show class' <> ", which has no wire form")
      Left (Unaccounted why) -> pure (ParseBroken (ValueUnaccounted why))
      Right wire -> case conformsTo setup.syntax.descriptor resultShape wire of
        Left problem -> failed ResultInvalid ("the parser returned no Result (Syntax Term), at " <> renderPath problem.path <> ": " <> problem.problem)
        Right _ -> case wire of
          WData (Qualified _ (Ident "Parsed")) [ syntax ] -> encoded parsedKind encodeParsed syntax
          WData (Qualified _ (Ident "Failed")) [ failure ] -> encoded parseFailedKind encodeParseFailed failure
          _ -> pure (ParseBroken (SyntaxUnavailable "a value the descriptor admits as a Result is neither constructor"))

  encoded kind encode wire = pure case encodeValue wire of
    Left problem -> ParseBroken (ResultUnencodable (renderPath problem.path <> ": " <> problem.problem))
    Right json -> ParseAnswered { kind, payload: encode json }

syntaxName :: P.String -> Qualified Ident
syntaxName = Qualified syntaxModuleName <<< Ident
