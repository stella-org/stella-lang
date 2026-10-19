-- | The modules the compiler carries, as a build compiles against them:
-- | `Stella.Syntax` and the one module it depends on, `Base.Int`, which a
-- | compile-time session loads before it runs a parser, and `Stella.Elab`,
-- | whose interface a module writing a synthesizer is compiled against.
-- |
-- | **Each is what a build of its source writes** ([Source](../Bootstrap/Source.purs)):
-- | its interface file and bytecode file, read as a build reads a module built
-- | elsewhere. The session loads `Base.Int` and `Stella.Syntax` as it loads
-- | every module, and carries out each entry of `Base.Int` as the operation the
-- | entry is. **`Stella.Elab` is the session's own to install**, so its bytecode
-- | is no module here a session loads: it is held apart, with the descriptor of
-- | its types, for the session to install. What is checked against a module is
-- | the signature any module importing it reads off its interface.
-- |
-- | **What `Stella.Syntax` keeps from source is in its bytecode's exports and in
-- | no export of its interface**: a module compiled against it may refer to
-- | it, and the session link it, while neither source nor a synthesizer, which
-- | reads the catalog the interface's exports make, reaches it.
module Stella.Compiler.Macro.Compiled
  ( Interface
  , Elaboration
  , Compiled
  , compiled
  ) where

import Prelude

import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Int as Int
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits as SCU
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Bootstrap.Source (Carried)
import Stella.Compiler.Bootstrap.Source as Source
import Stella.Compiler.Bytecode (Dmo, decode)
import Stella.Compiler.Bytecode.Bytes (Bytes)
import Stella.Compiler.Elaborate.Environment.Imported (importedSignature)
import Stella.Compiler.Elaborate.Protocol.Guest (handleTy)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor, describeInterface)
import Stella.Compiler.Interface.Environment (BuildEnvironment, addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Interface.File as Interface
import Stella.Compiler.Interface.Module (ModuleInterface)
import Stella.Compiler.Macro.Bundle (describeSyntax)
import Stella.Compiler.TypedCore (Signature)
import Stella.Compiler.TypedCore.Name (Ident, ModuleName(..))

-- | What a translation reads of a module it is compiled against.
type Interface = { name :: ModuleName, imports :: Array ModuleName, arities :: Map Ident Int }

-- | `Stella.Elab` as a session installs it: its bytecode, the descriptor of its
-- | data types, and the signature a module importing it is checked against.
type Elaboration = { dmo :: Dmo, descriptor :: Descriptor, signature :: Signature }

-- | The modules a session loads, in the order they load, `Base.Int` first and
-- | `Stella.Syntax` after it; the signature holding both, `IssuedOrigin` among
-- | its types; what a translation reads of each; the interface of each of the
-- | three, `Stella.Elab` last, which a module importing them is resolved and
-- | elaborated against; the interface of each module a compile-time session
-- | opened with `parse` in force holds before a build loads anything, which is
-- | each of the three, closed under imports; the descriptor of the types a
-- | value of `Stella.Syntax` crossing to the host has; and `Stella.Elab` as a
-- | session installs it.
type Compiled =
  { modules :: Array Dmo
  , signature :: Signature
  , interfaces :: Array Interface
  , moduleInterfaces :: Array ModuleInterface
  , preloaded :: Map ModuleName ModuleInterface
  , descriptor :: Descriptor
  , elaboration :: Elaboration
  }

-- | The modules read, or why they could not be: a failure here is a defect of
-- | the compiler.
compiled :: Either String Compiled
compiled = do
  base <- carried (ModuleName "Base.Int") Source.baseInt
  syntax <- carried (ModuleName "Stella.Syntax") Source.stellaSyntax
  elab <- carried (ModuleName "Stella.Elab") Source.stellaElab
  env <- lmap (\err -> "the modules the compiler carries are no environment: " <> show err)
    (addInterface base.interface initialEnvironment >>= addInterface syntax.interface >>= addInterface elab.interface)
  signature <- signatureOf env [ base.interface.name, syntax.interface.name ]
  descriptor <- lmap ("Stella.Syntax has no descriptor: " <> _) (describeSyntax syntax.interface)
  elabSignature <- signatureOf env [ elab.interface.name ]
  elabDescriptor <- lmap ("Stella.Elab has no descriptor: " <> _) (describeInterface handleTy (const true) elab.interface)
  let moduleInterfaces = [ base.interface, syntax.interface, elab.interface ]
  pure
    { modules: [ base.dmo, syntax.dmo ]
    , signature
    , interfaces: map translated [ base.interface, syntax.interface ]
    , moduleInterfaces
    , preloaded: Map.fromFoldable (map (\i -> Tuple i.name i) moduleInterfaces)
    , descriptor
    , elaboration: { dmo: elab.dmo, descriptor: elabDescriptor, signature: elabSignature }
    }
  where
  translated i = { name: i.name, imports: i.imports, arities: i.arities }

-- | The signature a module importing the modules given reads off the
-- | environment.
signatureOf :: BuildEnvironment -> Array ModuleName -> Either String Signature
signatureOf env names = do
  view <- lmap (\err -> "the modules the compiler carries have no view: " <> show err) (viewFor names env)
  lmap (\err -> "the modules the compiler carries have no signature: " <> show err) (importedSignature env view)

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
