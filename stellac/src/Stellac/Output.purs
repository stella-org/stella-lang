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
-- | names one. Every field but `entrypoint` and `foreign` is required, no other
-- | is accepted, no string is empty, and no module is listed twice. Each file
-- | read back is checked to hold the module it was written for.
-- |
-- | A build removes the `output.json` an earlier build left before it does
-- | anything, and writes its own once every module is written, so a build that
-- | fails, or has no module to build, leaves none.
module Stellac.Output
  ( Output
  , Built
  , Foreign
  , Supplying
  , Crossing
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

import Data.Argonaut.Core (isString, stringifyWithIndent)
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Codec as Codec
import Data.Codec.Argonaut (JsonCodec, JsonDecodeError)
import Data.Codec.Argonaut as CA
import Data.Codec.Argonaut.Record as CAR
import Data.Either (Either(..), either)
import Data.Foldable (foldM)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Profunctor (dimap)
import Data.Show.Generic (genericShow)
import Data.String as String
import Data.Traversable (for)
import Data.Tuple (Tuple(..), fst, snd)
import Fmt (fmt)
import Run (Run)
import Run.Except (EXCEPT, throw)
import Run.Except as Except
import Stella.CLI.Effect.FS (FS, FilePath)
import Stella.CLI.Effect.FS as FS
import Stella.Compiler.Bytecode (decode) as Bytecode
import Stella.CLI.Build (internal)
import Stella.Compiler.Bytecode.Bytes (DecodeError)
import Stella.Compiler.ForeignManifest (ResultKind(..), ValueKind(..), kindSpelling)
import Stella.Compiler.HostForeign (hostForeigns)
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.TypedCore (Ident(..), ModuleName(..))
import Stella.CLI.Codec (exactly, moduleName, nonEmpty)
import Stellac.Config (Config, relativeSpecifier)
import Stellac.Paths (builtPath, outputPath, relativeTo)
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

type Supplying = { module :: ModuleName, specifier :: String, foreigns :: Array Crossing }

type Crossing = { name :: String, params :: Array ValueKind, result :: ResultKind }

type Foreign = { target :: String, modules :: Array Supplying }

type Output = { modules :: Array Built, foreign :: Maybe Foreign }

data OutputError
  = NotJson String
  | Undecodable JsonDecodeError
  | Unreadable FilePath String
  | Rejected FilePath DecodeError
  -- | A file the build wrote for the first module named, holding the second.
  | OfAnother FilePath ModuleName ModuleName
  | Untargeted ModuleName (Array String)
  | Unsupplied ModuleName (Array String)
  | SuppliesNothing ModuleName
  | CompilerFault String
  | Unwritten FilePath String
  | Unremoved FilePath String

derive instance Eq OutputError
derive instance Generic OutputError _

instance Show OutputError where
  show = genericShow

codec :: JsonCodec Output
codec =
  CA.prismaticCodec "Output" (\o -> if suppliesBuilt o then Just o else Nothing) identity
    $ dimap (\o -> { formatVersion: unit, modules: o.modules, foreign: o.foreign }) (\o -> { modules: o.modules, foreign: o.foreign })
    $ exactly "output.json"
        { formatVersion: version
        , modules: once "module" _.module $ CA.array
            ( exactly "module"
                { module: moduleName
                , interface: nonEmpty
                , object: nonEmpty
                , imports: CA.array moduleName
                , entrypoint: CAR.optional ident
                }
            )
        , foreign: CAR.optional
            ( exactly "Foreign"
                { target: nonEmpty
                , modules: once "module" _.module $ CA.array
                    ( exactly "Supplying"
                        { module: moduleName
                        , specifier: nonEmpty
                        , foreigns: once "foreign" _.name $ CA.array (exactly "Crossing" { name: nonEmpty, params: CA.array valueKind, result: resultKind })
                        }
                    )
                }
            )
        }
  where
  -- `foreign` is of the modules built alone, and absent rather than empty
  suppliesBuilt o = case o.foreign of
    Nothing -> true
    Just f -> not (Array.null f.modules) && Array.all (\s -> not (Array.null s.foreigns) && Array.elem s.module (map _.module o.modules)) f.modules

  version = CA.prismaticCodec (fmt @"{formatVersion}, the version this compiler writes" { formatVersion }) (\v -> if v == formatVersion then Just unit else Nothing) (const formatVersion) CA.int
  ident = dimap (\(Ident i) -> i) Ident nonEmpty

  once :: forall a k. Eq k => String -> (a -> k) -> JsonCodec (Array a) -> JsonCodec (Array a)
  once what key = CA.prismaticCodec (fmt @"a list naming each {what} once" { what }) (\as -> if Array.length (Array.nubEq (map key as)) == Array.length as then Just as else Nothing) identity

  valueKind = CA.prismaticCodec "ValueKind" (\s -> Array.find (\k -> kindSpelling k == s) [ AsInt, AsNumber, AsChar, AsString, AsBoolean, AsUnit, AsOpaque ]) kindSpelling CA.string

  action = exactly "ResultKind" { action: valueKind }
  resultKind = Codec.codec'
    (\json -> if isString json then AsValue <$> Codec.decode valueKind json else (AsAction <<< _.action) <$> Codec.decode action json)
    case _ of
      AsValue k -> Codec.encode valueKind k
      AsAction k -> Codec.encode action { action: k }

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
written :: forall r. Config -> BuildEnvironment -> Run (FS + r) (Either (Array OutputError) Unit)
written config linked = Except.runExcept do
  read <- for config.modules \m -> do
    let
      dmi = builtPath output m.module "dmi"
      dmo = builtPath output m.module "dmo"
    stored <- bytesOf dmi >>= either (fault <<< Rejected dmi) pure <<< Interface.decode
    when (stored.interface.name /= m.module) (fault (OfAnother dmi m.module stored.interface.name))
    object <- bytesOf dmo >>= either (fault <<< Rejected dmo) pure <<< Bytecode.decode
    when (object.name /= m.module) (fault (OfAnother dmo m.module object.name))
    pure { built: { module: m.module, interface: file m.module "dmi", object: file m.module "dmo", imports: object.imports, entrypoint: stored.interface.entrypoint }, interface: stored.interface }
  env <- either (\err -> fault (CompilerFault ("the modules built make no environment: " <> show err))) pure
    (foldM (flip addInterface) linked (map _.interface read))
  hosted <- for read \r -> either (\why -> fault (CompilerFault (fmt @"`{m}`: {why}" { m: nameOf r.built.module, why }))) (pure <<< Tuple r.built.module) (hostForeigns env r.interface)
  let
    coverage = hosted >>= \(Tuple m foreigns) -> case foreigns, config.target, Array.find (\s -> s.module == m) config.foreigns of
      [], _, Just _ -> [ SuppliesNothing m ]
      [], _, Nothing -> []
      _, Nothing, _ -> [ Untargeted m (map fst foreigns) ]
      _, _, Nothing -> [ Unsupplied m (map fst foreigns) ]
      _, Just _, Just _ -> []
  unless (Array.null coverage) (throw coverage)
  directory <- FS.resolve output
  supplying <- for (Array.filter (not Array.null <<< snd) hosted) \(Tuple m foreigns) -> do
    specifier <- case Array.find (\s -> s.module == m) config.foreigns of
      Just s
        | relativeSpecifier s.written -> FS.resolve s.specifier <#> \located -> relativeSpecifierFrom directory located
        | otherwise -> pure s.specifier
      Nothing -> fault (CompilerFault (fmt @"`{m}` is supplied by no specifier" { m: nameOf m }))
    pure { module: m, specifier, foreigns: map (\(Tuple name s) -> { name, params: s.params, result: s.result }) foreigns }
  let
    manifest = case config.target of
      Just target | not (Array.null supplying) -> Just { target, modules: supplying }
      _ -> Nothing
  FS.writeText (outputPath output) (encode { modules: map _.built read, foreign: manifest }) >>= either (fault <<< Unwritten (outputPath output)) pure
  where
  output = config.options.output

  fault :: forall a r'. OutputError -> Run (EXCEPT (Array OutputError) + r') a
  fault = throw <<< pure

  bytesOf :: forall r'. FilePath -> Run (EXCEPT (Array OutputError) + FS + r') (Array Int)
  bytesOf path = FS.readBytes path >>= either (fault <<< Unreadable path) pure

  file (ModuleName m) extension = fmt @"{m}.{extension}" { m, extension }

-- `./` keeps a target from reading the path as a bare specifier.
relativeSpecifierFrom :: FilePath -> FilePath -> String
relativeSpecifierFrom directory located = case relativeTo directory located of
  path | String.take 3 path == "../" -> path
  path -> "./" <> path

printOutputError :: OutputError -> String
printOutputError = case _ of
  NotJson why -> fmt @"`output.json` is not JSON: {why}" { why }
  Undecodable error -> fmt @"`output.json` is not one this compiler writes: {why}" { why: CA.printJsonDecodeError error }
  Unreadable path why -> fmt @"`{path}`, which the build wrote, could not be read: {why}" { path, why }
  Rejected path err -> fmt @"`{path}`, which the build wrote, could not be decoded: {why}" { path, why: show err }
  OfAnother path m other -> fmt @"`{path}`, which the build wrote for `{m}`, holds `{other}`" { path, m: nameOf m, other: nameOf other }
  Untargeted m names -> fmt @"`{m}` declares foreigns the host supplies, {names}, and `stella.json` names no `target` to supply them for" { m: nameOf m, names: quoted names }
  Unsupplied m names -> fmt @"`{m}` declares foreigns the host supplies, {names}, and `foreigns` gives no specifier for it" { m: nameOf m, names: quoted names }
  SuppliesNothing m -> fmt @"`foreigns` gives a specifier for `{m}`, which declares no foreign the host supplies" { m: nameOf m }
  CompilerFault why -> internal why
  Unwritten path why -> fmt @"`{path}` could not be written: {why}" { path, why }
  Unremoved path why -> fmt @"`{path}`, which an earlier build wrote, could not be removed: {why}" { path, why }
  where
  quoted names = String.joinWith ", " (map (\n -> "`" <> n <> "`") names)

nameOf :: ModuleName -> String
nameOf (ModuleName n) = n
