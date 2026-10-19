-- | The modules the compiler carries, as a build compiles against them:
-- | `Stella.Syntax` and the one module it depends on, `Base.Int`, which a
-- | compile-time session loads before it runs a parser, and `Stella.Elab`,
-- | whose interface a module writing a synthesizer is compiled against.
-- |
-- | **`Stella.Elab` is the session's own to install**, so its bytecode is no
-- | module here: what is here of it is the interface alone, projected from the
-- | Typed Core its bundle holds, which the session installs from the same
-- | bundle.
-- |
-- | **`Base.Int` and `Stella.Syntax` are what a build of their sources writes**
-- | ([Source](../Bootstrap/Source.purs)): each one's interface file and
-- | bytecode file, read as a build reads a module built elsewhere, so the
-- | session loads them as it loads every module, and carries out each entry of
-- | `Base.Int` as the operation the entry is. What is checked against them is
-- | the signature any module importing both reads off their interfaces.
-- |
-- | **What `Stella.Syntax` keeps from source is in its bytecode's exports and in
-- | no export of its interface**: a module compiled against it may refer to
-- | it, and the session link it, while neither source nor a synthesizer, which
-- | reads the catalog the interface's exports make, reaches it.
module Stella.Compiler.Macro.Compiled
  ( Interface
  , Compiled
  , compiled
  ) where

import Prelude

import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Maybe (Maybe(..))
import Data.Int as Int
import Data.Map (Map)
import Data.Map as Map
import Data.String.CodeUnits as SCU
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Bootstrap.Source (Carried)
import Stella.Compiler.Bootstrap.Source as Source
import Stella.Compiler.Bytecode (Dmo, decode, lower)
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Stella.Compiler.Elaborate.Environment.Imported (importedSignature)
import Stella.Compiler.Elaborate.Protocol.Guest as Guest
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Interface (aritiesOf, importsOf)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.Interface.FromCore (interfaceOfCore)
import Stella.Compiler.Interface.Module (ModuleInterface)
import Stella.Compiler.Macro.Bundle (describeSyntax)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore (Export(..), Module, Signature, declareAnnotated, primSignature)
import Stella.Compiler.TypedCore.Name (Ident, ModuleName(..))

-- | What a translation reads of a module it is compiled against.
type Interface = { name :: ModuleName, imports :: Array ModuleName, arities :: Map Ident Int }

-- | The modules a session loads, in the order they load, `Base.Int` first and
-- | `Stella.Syntax` after it; the signature holding both, `IssuedOrigin` among
-- | its types; what a translation reads of each; the interface of each of the
-- | three, `Stella.Elab` last, which a module importing them is resolved and
-- | elaborated against; the interface of each module a compile-time session
-- | opened with `parse` in force holds before a build loads anything, which is
-- | each of the three, closed under imports; and the descriptor of the types a
-- | value of `Stella.Syntax` crossing to the host has.
type Compiled =
  { modules :: Array Dmo
  , signature :: Signature
  , interfaces :: Array Interface
  , moduleInterfaces :: Array ModuleInterface
  , preloaded :: Map ModuleName ModuleInterface
  , descriptor :: Descriptor
  }

-- | The modules read and compiled, or why they could not be: a failure here is
-- | a defect of the compiler.
compiled :: Either String Compiled
compiled = do
  base <- carried (ModuleName "Base.Int") Source.baseInt
  syntax <- carried (ModuleName "Stella.Syntax") Source.stellaSyntax
  env <- lmap (\err -> "the modules the compiler carries are no environment: " <> show err)
    (addInterface base.interface initialEnvironment >>= addInterface syntax.interface)
  view <- lmap (\err -> "the modules the compiler carries have no view: " <> show err) (viewFor [ base.interface.name, syntax.interface.name ] env)
  signature <- lmap (\err -> "the modules the compiler carries have no signature: " <> show err) (importedSignature env view)
  descriptor <- lmap ("Stella.Syntax has no descriptor: " <> _) (describeSyntax syntax.interface)
  guest <- Guest.bundle
  elab <- compile (guest.withSignature primSignature) [] guest.module
  let moduleInterfaces = [ base.interface, syntax.interface, elab.moduleInterface ]
  pure
    { modules: [ base.dmo, syntax.dmo ]
    , signature
    , interfaces: map translated [ base.interface, syntax.interface ]
    , moduleInterfaces
    , preloaded: Map.fromFoldable (map (\i -> Tuple i.name i) moduleInterfaces)
    , descriptor
    }
  where
  translated i = { name: i.name, imports: i.imports, arities: i.arities }

-- | A module the compiler carries, its files decoded as a build decodes them,
-- | and the interface the one of the module named.
carried :: ModuleName -> Carried -> Either String { interface :: ModuleInterface, dmo :: Dmo }
carried name files = do
  stored <- named "interface" (fromHex files.interface) >>= \bytes -> lmap (named' "interface" <<< show) (Interface.decode bytes)
  dmo <- named "bytecode" (fromHex files.bytecode) >>= \bytes -> lmap (named' "bytecode" <<< show) (decode bytes)
  if stored.interface.name == name && dmo.name == name then Right { interface: stored.interface, dmo }
  else Left (show name <> " is carried as files of another module")
  where
  named what = note (show name <> ": its " <> what <> " is no hexadecimal")
  named' what why = show name <> ": its " <> what <> " does not decode: " <> why

-- | The bytes a string of hexadecimal digits spells, two digits to a byte.
fromHex :: String -> Maybe Bytes
fromHex s
  | Int.odd (SCU.length s) = Nothing
  | otherwise = traverse (\i -> Int.fromStringAs Int.hexadecimal (SCU.slice (2 * i) (2 * i + 2) s)) (Array.range 0 (SCU.length s / 2 - 1))

compile
  :: Signature
  -> Array Interface
  -> Module Unit
  -> Either String { dmo :: Dmo, signature :: Signature, interface :: Interface, moduleInterface :: ModuleInterface }
compile signature against m = do
  declared <- case declareAnnotated signature m of
    Left err -> Left (named "does not declare" (show err.error))
    Right declared -> Right declared
  imports <- case importsOf against of
    Left err -> Left (named "has no interfaces" (show err))
    Right imports -> Right imports
  mid <- case translate imports m declared of
    Left err -> Left (named "does not translate" (show err))
    Right mid -> Right mid
  lowered <- case lower mid of
    Left err -> Left (named "does not lower" (show err))
    Right lowered -> Right lowered
  let arities = aritiesOf mid.module
  -- the interface carries the arities of what a module downstream reaches
  moduleInterface <- case interfaceOfCore m declared (Map.filterKeys (\x -> Array.elem (ExportValue x) m.exports) arities) of
    Left err -> Left (named "has no interface" (show err))
    Right i -> Right i
  pure
    { dmo: lowered.dmo
    , signature: declared.signature
    , interface: { name: mid.module.name, imports: mid.module.imports, arities }
    , moduleInterface
    }
  where
  named what why = show m.name <> " " <> what <> ": " <> why
