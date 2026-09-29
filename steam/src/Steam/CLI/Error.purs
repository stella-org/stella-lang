-- | What ends a command before it answers, and what a process makes of it.
-- |
-- | **Two questions decide the exit status, and asking them in order makes it
-- | total.** Was it an interpreter bug? If so it is a bug wherever it arose, because
-- | that is a statement about whose the defect is rather than about the moment.
-- | Otherwise: had the entry point begun to run? Before it, the program never
-- | started; after it, the program ran and reached something the ABI admits may
-- | fail.
-- |
-- | Collapsing these into one non-zero status would leave a script unable to tell a
-- | build handed over wrong from a program that ran and failed.
module Steam.CLI.Error
  ( ErrorType(..)
  , exitStatus
  , endsQuietly
  , report
  ) where

import Prelude

import Fmt (fmt)
import Prim as P

import Steam.Eval (Bug, Failure(..))
import Steam.CLI.Assemble (AssembleError(..))
import Steam.Load (LoadError)
import Stella.Compiler.ForeignManifest (ManifestError)
import Stella.Compiler.Bytecode (DecodeError)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))
import Stella.CLI.Session.Frame (FrameFailure(..))
import Stella.CLI.Session.Peer (SessionFailure(..))
import Stella.CLI.Session.Protocol (Refusal, RefusalReason(..))

data ErrorType
  -- | A file that could not be read, as the path and what the host said.
  = FileUnreadable P.String P.String
  -- | Bytes the decoder rejected, as the path.
  | FileNotBytecode P.String DecodeError
  -- | A module the registry refused.
  | ModuleRefused LoadError
  -- | A module whose global faulted as it was evaluated. The module did not load,
  -- | so the program never started.
  | InitializationFailed (Qualified Ident) Failure
  -- | No module of that name among the ones given.
  | NoEntryModule ModuleName
  -- | The entry module holds no global of that name.
  | NoEntryGlobal (Qualified Ident)
  -- | The entry point holds something that is not an `IO`, so there is nothing to
  -- | execute. What it does hold is not reported: a `.dmo` carries no type, and
  -- | naming a class here would suggest one was checked.
  | EntryNotAnAction (Qualified Ident)
  -- | A manifest that does not read as one, as the path and what was wrong. **It
  -- | fails once and before anything else**: it is read when the command starts, so
  -- | this is a failure to start rather than a refusal of one module.
  | ManifestRefused P.String ManifestError
  -- | Implementations the manifest named that could not be reached, or that were
  -- | reached and were not what a foreign needs.
  | ForeignsUnreachable AssembleError
  -- | The entry point ran and failed.
  | RunFailed Failure
  -- | The `session` command was started with no channel to speak on, as what the
  -- | host said.
  | SessionChannelMissing P.String
  -- | The session refused the handshake, and so never opened.
  | SessionRefused Refusal
  -- | The session ended other than by `close`.
  | SessionFailed SessionFailure

-- | What the process exits with.
exitStatus :: ErrorType -> P.Int
exitStatus = case _ of
  -- a bug is asked about first: the defect is above the program, whenever it
  -- happened
  InitializationFailed _ (Bug _) -> 3
  RunFailed (Bug _) -> 3
  -- a session that could not answer, or built a message it could not send, is the
  -- interpreter's own defect
  SessionFailed (HandlerFailed _) -> 3
  SessionFailed (OutgoingTooLarge _) -> 3
  SessionFailed (OutgoingUnencodable _) -> 3
  -- then by the moment: everything below stopped the program before it started
  FileUnreadable _ _ -> 1
  FileNotBytecode _ _ -> 1
  ModuleRefused _ -> 1
  InitializationFailed _ _ -> 1
  NoEntryModule _ -> 1
  NoEntryGlobal _ -> 1
  EntryNotAnAction _ -> 1
  ManifestRefused _ _ -> 1
  ForeignsUnreachable _ -> 1
  RunFailed _ -> 2
  -- a session that did not open, or that ended unasked
  SessionChannelMissing _ -> 1
  SessionRefused _ -> 1
  SessionFailed _ -> 1

-- | Whether the process should end by having nothing left to do rather than by
-- | exiting at once. **A session ends that way**: it has written its last frame
-- | and released its channel, and what is still queued for standard output or
-- | standard error is written before the process ends, where exiting at once would
-- | cut off what a pipe had not yet taken.
endsQuietly :: ErrorType -> P.Boolean
endsQuietly = case _ of
  SessionChannelMissing _ -> true
  SessionRefused _ -> true
  SessionFailed _ -> true
  _ -> false

-- | The line a user reads.
-- |
-- | **Nothing here points at an internal document.** What a reader is told is what
-- | happened and, where there is one, what to do about it.
report :: ErrorType -> P.String
report = case _ of
  FileUnreadable path reason ->
    fmt @"Cannot read {path}: {reason}" { path, reason }

  FileNotBytecode path err ->
    fmt @"Not readable as bytecode: {path}\n  {reason}"
      { path, reason: show err }

  ModuleRefused err ->
    fmt @"A module was refused: {reason}" { reason: show err }

  InitializationFailed name failure ->
    fmt @"Failed while initializing {name}: {reason}"
      { name: qualified name, reason: describe failure }

  NoEntryModule name ->
    fmt @"No module named {name} among the files given.\n  Give the module holding the entry point with --entry."
      { name: unModule name }

  NoEntryGlobal name ->
    fmt @"No {name} to run.\n  Name the entry point within the module with --entry-global."
      { name: qualified name }

  EntryNotAnAction name ->
    fmt @"{name} is not an action, so there is nothing to run."
      { name: qualified name }

  ManifestRefused path err ->
    fmt @"Not readable as a foreign manifest: {path}\n  {reason}"
      { path, reason: show err }

  ForeignsUnreachable err ->
    unreachable err

  RunFailed failure ->
    describe failure

  SessionChannelMissing reason ->
    "The session has no channel to speak on: " <> reason
      <> "\n  Start `steam session` with a bidirectional pipe as descriptor 3."

  SessionRefused refusal ->
    "The session was not opened: " <> refused refusal.reason

  SessionFailed failure ->
    "The session ended: " <> sessionFailure failure

refused :: RefusalReason -> P.String
refused = case _ of
  ProtocolUnsupported -> "the client asked for a protocol version this session does not speak"
  ProfileUnsupported -> "the client asked for a profile this session does not offer"
  CapabilityUnsupported -> "the client required a capability this session does not have"

sessionFailure :: SessionFailure -> P.String
sessionFailure = case _ of
  FrameUnreadable (Oversized length) ->
    "a frame declared " <> show length <> " bytes, above the limit"
  FrameUnreadable (TruncatedPrefix _) -> "the channel ended inside a frame's length"
  FrameUnreadable (TruncatedPayload _) -> "the channel ended inside a frame"
  ChannelEnded -> "the channel ended without `close`"
  ChannelFailed reason -> "the channel failed: " <> reason
  IdsExhausted -> "every request number has been used"
  OutgoingTooLarge kind -> "a `" <> kind <> "` message was too large to send"
  OutgoingUnencodable kind -> "a `" <> kind <> "` message could not be encoded"
  HandlerFailed reason -> "a request could not be answered: " <> reason
  ShutDown -> "the session was shut down"

describe :: Failure -> P.String
describe = case _ of
  Faults fault -> fmt @"the program failed: {reason}" { reason: show fault }
  Unimplemented what ->
    fmt @"this interpreter does not carry out {what}" { what }
  Bug bug -> defect bug

-- | **A bug is said to be one.** What went wrong is not the program, and a reader
-- | acting on it should be told so rather than left to read a failure as their own.
defect :: Bug -> P.String
defect bug =
  fmt @"Internal error in the interpreter: {reason}\n  This is a defect above the program being run."
    { reason: show bug }

-- | A name as a reader wrote it.
qualified :: Qualified Ident -> P.String
qualified (Qualified m (Ident name)) = unModule m <> "." <> name

unModule :: ModuleName -> P.String
unModule (ModuleName name) = name

-- | **What a reader is told is the module and the export**, which is what a manifest
-- | or a host module has to be fixed by. The specifier is not named: what one is
-- | belongs to the target, and a reader who wrote the manifest has it to hand.
unreachable :: AssembleError -> P.String
unreachable = case _ of
  ModuleUnreachable name reason ->
    fmt @"Cannot reach the implementations of {name}: {reason}"
      { name: unModule name, reason }

  NoSuchExport name export ->
    fmt @"The implementations of {name} have no `{export}`.\n  A foreign is supplied by the export of its own name."
      { name: unModule name, export }

  ExportNotCallable name export ->
    fmt @"`{export}` in the implementations of {name} is not a function."
      { name: unModule name, export }

  NoSignature name foreign' ->
    fmt @"The foreign manifest does not say how the values of {name}.{foreign} cross.\n  Use the manifest written by the build that produced these bytecode files."
      { name: unModule name, foreign: foreign' }

  SignatureDisagrees name foreign' declared given ->
    fmt @"The foreign manifest gives {name}.{foreign} {given} parameters, and its declaration takes {declared}.\n  Use the manifest written by the build that produced these bytecode files."
      { name: unModule name, foreign: foreign', declared: show declared, given: show given }
