-- | `output.json`: what `stellac compile` writes beside the modules it built,
-- | stating of each what only the compiler knows, so that whatever drives the
-- | compiler can put a program together from it. `codec` both reads and
-- | writes it.
-- |
-- | ```json
-- | { "formatVersion": 0,
-- |   "modules": [
-- |     { "module": "App.Main", "interface": "App.Main.dmi", "object": "App.Main.dmo",
-- |       "imports": [ "App.Util" ], "entrypoint": "$entrypoint" } ] }
-- | ```
-- |
-- | `modules` lists the modules the build compiled, in the order `stella.json`
-- | lists them: each with its interface and bytecode, by their paths from the
-- | directory `output.json` stands in; the modules its bytecode imports, its
-- | runtime dependencies; and the entry point its interface names, where it
-- | names one. Every field but `entrypoint` is required, no other is accepted,
-- | no string is empty, and no module is listed twice. Each file read back is
-- | checked to hold the module it was written for.
-- |
-- | A build removes the `output.json` an earlier build left before it does
-- | anything, and writes its own once every module is written, so a build that
-- | fails, or has no module to build, leaves none.
module Stellac.Output
  ( Output
  , Built
  , OutputError(..)
  , formatVersion
  , codec
  , decode
  , encode
  , withdrawn
  , written
  , printOutputError
  ) where

import Prelude

import Data.Argonaut.Core (stringifyWithIndent)
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Codec as Codec
import Data.Codec.Argonaut (JsonCodec, JsonDecodeError)
import Data.Codec.Argonaut as CA
import Data.Codec.Argonaut.Record as CAR
import Data.Either (Either(..), either)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Profunctor (dimap)
import Data.Show.Generic (genericShow)
import Data.Traversable (for)
import Fmt (fmt)
import Run (Run)
import Run.Except (EXCEPT, throw)
import Run.Except as Except
import Stella.CLI.Effect.FS (FS, FilePath)
import Stella.CLI.Effect.FS as FS
import Stella.Compiler.Bytecode (decode) as Bytecode
import Stella.Compiler.Bytecode.Bytes (DecodeError)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..))
import Stella.CLI.Codec (exactly, moduleName, nonEmpty)
import Stellac.Config (Config)
import Stellac.Paths (builtPath, outputPath)
import Type.Row (type (+))

-- | The version of the file this compiler writes.
formatVersion :: Int
formatVersion = 0

-- | A module the build compiled.
type Built =
  { module :: ModuleName
  , interface :: FilePath
  , object :: FilePath
  , imports :: Array ModuleName
  , entrypoint :: Maybe Ident
  }

type Output = { modules :: Array Built }

data OutputError
  = NotJson String
  | Undecodable JsonDecodeError
  | Unreadable FilePath String
  | Rejected FilePath DecodeError
  -- | A file the build wrote for the first module named, holding the second.
  | OfAnother FilePath ModuleName ModuleName
  | Unwritten FilePath String
  | Unremoved FilePath String

derive instance Eq OutputError
derive instance Generic OutputError _

instance Show OutputError where
  show = genericShow

codec :: JsonCodec Output
codec =
  dimap (\o -> { formatVersion: unit, modules: o.modules }) (\o -> { modules: o.modules })
    $ exactly "output.json"
        { formatVersion: version
        , modules: once $ CA.array
            ( exactly "module"
                { module: moduleName
                , interface: nonEmpty
                , object: nonEmpty
                , imports: CA.array moduleName
                , entrypoint: CAR.optional ident
                }
            )
        }
  where
  version = CA.prismaticCodec (fmt @"{formatVersion}, the version this compiler writes" { formatVersion }) (\v -> if v == formatVersion then Just unit else Nothing) (const formatVersion) CA.int
  ident = dimap (\(Ident i) -> i) Ident nonEmpty
  once = CA.prismaticCodec "a list naming each module once" (\ms -> if Array.length (Array.nubEq (map _.module ms)) == Array.length ms then Just ms else Nothing) identity

decode :: String -> Either OutputError Output
decode text = case jsonParser text of
  Left why -> Left (NotJson why)
  Right json -> lmap Undecodable (Codec.decode codec json)

-- | The file as `codec` writes it, indented.
encode :: Output -> String
encode output = stringifyWithIndent 2 (Codec.encode codec output)

-- | Removes the `output.json` an earlier build left in the output directory
-- | `stella.json` gives, if any.
withdrawn :: forall r. Config -> Run (FS + r) (Either OutputError Unit)
withdrawn config = lmap (Unremoved file) <$> FS.remove file
  where
  file = outputPath config.options.output

-- | Writes the `output.json` of the build `stella.json` gives, read off the
-- | files the build wrote.
written :: forall r. Config -> Run (FS + r) (Either OutputError Unit)
written config = Except.runExcept do
  modules <- for config.modules \m -> do
    let
      dmi = builtPath output m.module "dmi"
      dmo = builtPath output m.module "dmo"
    stored <- read dmi >>= either (throw <<< Rejected dmi) pure <<< Interface.decode
    when (stored.interface.name /= m.module) (throw (OfAnother dmi m.module stored.interface.name))
    object <- read dmo >>= either (throw <<< Rejected dmo) pure <<< Bytecode.decode
    when (object.name /= m.module) (throw (OfAnother dmo m.module object.name))
    pure { module: m.module, interface: file m.module "dmi", object: file m.module "dmo", imports: object.imports, entrypoint: stored.interface.entrypoint }
  FS.writeText (outputPath output) (encode { modules }) >>= either (throw <<< Unwritten (outputPath output)) pure
  where
  output = config.options.output

  read :: forall r'. FilePath -> Run (EXCEPT OutputError + FS + r') (Array Int)
  read path = FS.readBytes path >>= either (throw <<< Unreadable path) pure

  file (ModuleName m) extension = fmt @"{m}.{extension}" { m, extension }

printOutputError :: OutputError -> String
printOutputError = case _ of
  NotJson why -> fmt @"`output.json` is not JSON: {why}" { why }
  Undecodable error -> fmt @"`output.json` is not one this compiler writes: {why}" { why: CA.printJsonDecodeError error }
  Unreadable path why -> fmt @"`{path}`, which the build wrote, could not be read: {why}" { path, why }
  Rejected path err -> fmt @"`{path}`, which the build wrote, could not be decoded: {why}" { path, why: show err }
  OfAnother path m other -> fmt @"`{path}`, which the build wrote for `{m}`, holds `{other}`" { path, m: text m, other: text other }
  Unwritten path why -> fmt @"`{path}` could not be written: {why}" { path, why }
  Unremoved path why -> fmt @"`{path}`, which an earlier build wrote, could not be removed: {why}" { path, why }
  where
  text (ModuleName n) = n
