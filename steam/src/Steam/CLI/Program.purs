-- | What the `steam` command does.
-- |
-- | **This is the wiring and not a second interpreter.** Running a program is a
-- | function of three things — the modules in order, the entry point, and the
-- | foreign table — and `runProgram` is that function. **The interpreter assembles
-- | the table itself**, from the manifest it is given: a table holds
-- | host functions, which no command line can carry, so whoever builds one must be
-- | in the process that uses it (D43).
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
import Steam.CLI.Elaboration as Elaboration
import Steam.CLI.Error (ErrorType(..), SessionDefect(..))
import Steam.CLI.Options (Command(..), Options, RunOptions)
import Data.String as String
import Steam.Drive (execute)
import Stella.Compiler.ForeignManifest (Manifest)
import Stella.Compiler.ForeignManifest as Manifest
import Steam.CLI.Assemble as Assemble
import Steam.CLI.Session as Session
import Steam.Load (Store, emptyStore, globalNamed, load, noIdentities, registryOf, unitValue)
import Steam.Load as Load
import Steam.Value (IOValue, Value(..))
import Stella.CLI.Effect.FS (FS, readBytes, readText)
import Stella.CLI.Effect.Foreigns (FOREIGNS)
import Steam.CLI.Effect.Tuning (TUNING)
import Steam.CLI.Effect.Tuning as Tuning
import Stella.CLI.Effect.Transport (TRANSPORT)
import Stella.CLI.Effect.Log (LOG)
import Stella.Compiler.Bytecode (Dmo, decode)
import Stella.Compiler.Macro.Compiled (compiled)
import Stella.Compiler.ProgramDescriptor (Descriptor, DescriptorError(..))
import Stella.Compiler.ProgramDescriptor as ProgramDescriptor
import Stella.Compiler.TypedCore.Name (Ident, Qualified)
import Type.Row (type (+))

type SteamEffects = (LOG + FS + FOREIGNS + TRANSPORT + TUNING + EXCEPT ErrorType + AFF + EFFECT + ())

program :: Options -> Run SteamEffects Unit
program opts = case opts.command of
  Run runOptions -> runProgram runOptions
  Session sessionOptions -> do
    -- **the manifest is read before the channel is opened**: a manifest that does not
    -- read is a session that does not start, not a refusal it could answer
    manifest <- readManifest sessionOptions.manifest
    -- `Stella.Elab` is lowered before the channel is opened too: the compiler this
    -- interpreter is built with failing to supply it is a defect, not a refusal
    elaboration <- case Elaboration.prepare of
      Left reason -> Except.throw (SessionDefect (ElaborationUnavailable reason))
      Right elaboration -> pure elaboration
    -- and so is `Stella.Syntax`, with the module it depends on
    syntax <- case compiled of
      Left reason -> Except.throw (SessionDefect (SyntaxUnavailable reason))
      Right syntax -> pure syntax
    identities <- liftEffect (Ref.new noIdentities)
    unit <- liftEffect (unitValue identities)
    quantum <- Tuning.quantum
    Session.serve { manifest, base: baseOf sessionOptions.manifest, identities, unit, elaboration, syntax, quantum }

-- | **The table is complete before the first module is loaded**: a run is given every
-- | module at once, so it reaches every implementation their declarations ask for
-- | first.
runProgram :: RunOptions -> Run SteamEffects Unit
runProgram options = do
  descriptor <- readDescriptor options.program
  let base = directoryOf options.program
  modules <- traverseA (readModule <<< locatedFrom base <<< _.object) descriptor.modules
  case ProgramDescriptor.validate descriptor modules of
    Left err -> Except.throw (DescriptorRefused options.program err)
    Right _ -> pure unit
  manifest <- case descriptor.foreign of
    Nothing -> pure Nothing
    Just body -> case Manifest.readBody thisTarget body of
      Left err -> Except.throw (ManifestRefused options.program err)
      Right m -> pure (Just m)
  -- the identities every module is loaded against, asked for `Prim.Unit` first so
  -- that a `unit` result stands for the value those modules compare against
  identities <- liftEffect (Ref.new noIdentities)
  primUnit <- liftEffect (unitValue identities)
  assembled <- Assemble.tableFor base manifest primUnit modules
  table <- case assembled of
    Left err -> Except.throw (ForeignsUnreachable err)
    Right table -> pure table
  store <- loadAll (emptyStore table identities) modules
  action <- entryPoint store options.program descriptor.entry
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
   . Store
  -> P.Array Dmo
  -> Run (EXCEPT ErrorType + EFFECT + r) Store
loadAll empty modules = Array.foldM one empty modules
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
entryPoint
  :: forall r
   . Store
  -> P.String
  -> Qualified Ident
  -> Run (EXCEPT ErrorType + EFFECT + r) IOValue
entryPoint store path name =
  case globalNamed store name of
    Nothing -> Except.throw (DescriptorRefused path (NoEntryGlobal name))
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

-- | The manifest, where one was named.
-- |
-- | **Absent is not an error.** A program over `Base` alone declares no foreign
-- | anything supplies, so there is nothing for a manifest to say; a program that
-- | does declare one and was given no manifest is refused where that module loads,
-- | naming the foreign rather than the missing file.
readManifest
  :: forall r
   . Maybe P.String
  -> Run (FS + EXCEPT ErrorType + r) (Maybe Manifest)
readManifest = case _ of
  Nothing -> pure Nothing
  Just path -> do
    read <- readText path
    case read of
      Left reason -> Except.throw (FileUnreadable path reason)
      Right source -> case Manifest.parse thisTarget source of
        Left err -> Except.throw (ManifestRefused path err)
        Right manifest -> pure (Just manifest)

readDescriptor :: forall r. P.String -> Run (FS + EXCEPT ErrorType + r) Descriptor
readDescriptor path = do
  read <- readText path
  case read of
    Left reason -> Except.throw (FileUnreadable path reason)
    Right source -> case ProgramDescriptor.parse source of
      Left err -> Except.throw (DescriptorRefused path err)
      Right descriptor -> pure descriptor

locatedFrom :: P.String -> P.String -> P.String
locatedFrom base path
  | String.take 1 path == "/" = path
  | otherwise = base <> "/" <> path

-- | The target this runtime is. A manifest naming another describes a machine that
-- | is not this one, and is rejected rather than read past.
thisTarget :: P.String
thisTarget = "javascript"

-- | The directory a manifest's relative parts are resolved against, which is the
-- | directory the manifest itself was read from — the one base that makes a file
-- | mean the same thing wherever it is read from.
baseOf :: Maybe P.String -> P.String
baseOf = case _ of
  Nothing -> "."
  Just path -> directoryOf path

directoryOf :: P.String -> P.String
directoryOf path = case String.lastIndexOf (String.Pattern "/") path of
  Nothing -> "."
  Just i -> String.take i path
