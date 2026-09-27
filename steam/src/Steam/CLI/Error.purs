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
  , report
  ) where

import Prelude

import Fmt (fmt)
import Prim as P

import Steam.Eval (Bug, Failure(..))
import Steam.Load (LoadError)
import Stella.Compiler.Bytecode (DecodeError)
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..))

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
  -- | The entry point ran and failed.
  | RunFailed Failure
  -- | The long-lived mode, which is not built yet. **A refusal and not a notice**:
  -- | a command that printed a failure and exited zero would tell a reader one
  -- | thing and a shell another.
  | SessionUnavailable

-- | What the process exits with.
exitStatus :: ErrorType -> P.Int
exitStatus = case _ of
  -- a bug is asked about first: the defect is above the program, whenever it
  -- happened
  InitializationFailed _ (Bug _) -> 3
  RunFailed (Bug _) -> 3
  -- then by the moment: everything below stopped the program before it started
  FileUnreadable _ _ -> 1
  FileNotBytecode _ _ -> 1
  ModuleRefused _ -> 1
  InitializationFailed _ _ -> 1
  NoEntryModule _ -> 1
  NoEntryGlobal _ -> 1
  EntryNotAnAction _ -> 1
  SessionUnavailable -> 1
  RunFailed _ -> 2

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

  RunFailed failure ->
    describe failure

  SessionUnavailable ->
    "The session mode is not built yet. Use `steam run` to run a program."

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
