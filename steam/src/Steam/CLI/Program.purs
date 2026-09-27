-- | What the `steam` command does.
-- |
-- | **This is the wiring and not a second interpreter.** Running a program is a
-- | function of three things — the modules in order, the entry point, and the
-- | foreign table — and `runProgram` is that function. The command passes an empty
-- | table, a command line carrying paths and names and not host functions; the
-- | application above calls the same wiring with the table it assembled.
module Steam.CLI.Program
  ( SteamEffects
  , program
  , runProgram
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Ref as Ref
import Run (AFF, EFFECT, Run, liftEffect)
import Run.Except (EXCEPT)
import Run.Except as Except
import Steam.CLI.Error (ErrorType(..))
import Steam.CLI.Options (Command(..), Options, RunOptions)
import Steam.Drive (execute)
import Steam.Foreign (ForeignTable, emptyTable)
import Steam.Load (Store, emptyStore, globalNamed, load, moduleNamed, noIdentities, registryOf)
import Steam.Load as Load
import Steam.Value (IOValue, Value(..))
import Stella.CLI.Effect.FS (FS, readBytes)
import Stella.CLI.Effect.Log (LOG)
import Stella.CLI.Effect.Log as Log
import Stella.Compiler.Bytecode (Dmo, decode)
import Stella.Compiler.TypedCore.Name (Qualified(..))
import Type.Row (type (+))

type SteamEffects = (LOG + FS + EXCEPT ErrorType + AFF + EFFECT + ())

program :: Options -> Run SteamEffects Unit
program opts = case opts.command of
  Run runOptions -> runProgram emptyTable runOptions
  -- **a refusal and not a message**: a command that printed a failure and exited
  -- zero would tell a reader one thing and a shell another
  Session _ -> Except.throw SessionUnavailable

-- | Load the modules given, in the order given, and execute the entry point.
-- |
-- | The table is a parameter rather than something built here, which is what lets
-- | the application above reach this with one it assembled.
runProgram :: ForeignTable -> RunOptions -> Run SteamEffects Unit
runProgram table options = do
  modules <- traverseA readModule options.modules
  store <- loadAll table modules
  action <- entryPoint store options
  outcome <- Except.runExcept (execute (registryOf store) action)
  case outcome of
    -- **the value is discarded.** A front end that type checks knows the entry
    -- point is `IO Unit`; this command knows only that the global held an action,
    -- a `.dmo` carrying no type to check the rest against
    Right _ -> pure unit
    Left failure -> Except.throw (RunFailed failure)

-- | The bytes of one file, decoded.
-- |
-- | **Reading and decoding are told apart**, a file that is not there and a file
-- | that is not bytecode being different things to act on.
readModule :: forall r. P.String -> Run (FS + EXCEPT ErrorType + r) Dmo
readModule path = do
  read <- readBytes path
  case read of
    Left reason -> Except.throw (FileUnreadable path reason)
    Right bytes -> case decode bytes of
      Left err -> Except.throw (FileNotBytecode path err)
      Right dmo -> pure dmo

-- | Load them left to right.
-- |
-- | **Nothing is sorted.** The order is the one the command was given, a module
-- | whose imports are not already loaded is refused, and the refusal is the front
-- | end's mistake to hear about rather than something to work around here.
loadAll
  :: forall r
   . ForeignTable
  -> P.Array Dmo
  -> Run (EXCEPT ErrorType + EFFECT + r) Store
loadAll table modules = do
  identities <- liftEffect (Ref.new noIdentities)
  Array.foldM one (emptyStore table identities) modules
  where
  one store dmo = do
    outcome <- Except.runExcept (load store dmo)
    case outcome of
      Right loaded -> pure loaded
      -- **a failure while a global was evaluated is kept apart from every other
      -- refusal**, because what ended it decides the exit status: a fault there is
      -- a program that never started, and a bug there is a bug wherever it arose
      Left (Load.InitializationFailed name failure) ->
        Except.throw (InitializationFailed name failure)
      Left err -> Except.throw (ModuleRefused err)

-- | The action the entry point holds.
-- |
-- | **Only the named module's own globals are consulted.** Nothing is searched
-- | across modules, so a second module declaring the same name is not a competitor
-- | and a dependency that happens to be runnable is not picked up.
entryPoint
  :: forall r
   . Store
  -> RunOptions
  -> Run (EXCEPT ErrorType + EFFECT + r) IOValue
entryPoint store options = do
  -- a module that was never given and a module without the global are different
  -- things to be told, and only the first is answered by naming another file
  when (moduleNamed store options.entry == Nothing)
    (Except.throw (NoEntryModule options.entry))
  let name = Qualified options.entry options.entryGlobal
  case globalNamed store name of
    Nothing -> Except.throw (NoEntryGlobal name)
    Just slot -> do
      held <- liftEffect (Ref.read slot)
      case held of
        Just (VIO action) -> pure action
        _ -> Except.throw (EntryNotAnAction name)

-- | `traverse` over the effects this command runs in.
traverseA
  :: forall r a b
   . (a -> Run (EXCEPT ErrorType + AFF + EFFECT + r) b)
  -> P.Array a
  -> Run (EXCEPT ErrorType + AFF + EFFECT + r) (P.Array b)
traverseA f = Array.foldM step []
  where
  step acc a = map (\b -> acc <> [ b ]) (f a)
