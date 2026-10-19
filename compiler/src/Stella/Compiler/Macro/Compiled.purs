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
-- | **`Base.Int` is compiled from its source** ([Source](../Bootstrap/Source.purs)),
-- | as a build compiles a module, against `Prim` alone and with no macro run, so
-- | the session loads it as it loads every module, and carries out each of its
-- | entries as the operation the entry is. `Stella.Syntax` is compiled against
-- | the signature any module importing `Base.Int` reads off its interface.
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
import Data.Array.NonEmpty as NonEmptyArray
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Bootstrap.Source as Source
import Stella.Compiler.Build (CompilerAction, compileModule, defaultHooks, printCompileError, withoutSynthesizers)
import Stella.Compiler.Bytecode (Dmo, lower)
import Stella.Compiler.Elaborate.Environment.Imported (importedSignature)
import Stella.Compiler.Elaborate.Protocol.Guest as Guest
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Interface (aritiesOf, importsOf)
import Stella.Compiler.Interface.Environment (addInterface, initialEnvironment, viewFor)
import Stella.Compiler.Interface.FromCore (interfaceOfCore)
import Stella.Compiler.Interface.Module (ModuleInterface)
import Stella.Compiler.Macro.Bundle (bundle)
import Stella.Compiler.Macro.Run (ExecutionReason(..), ParseOutcome(..), defaultSettings)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.TypedCore (Export(..), Module, Signature, declareAnnotated, primSignature)
import Stella.Compiler.TypedCore.Name (Ident, ModuleName, Qualified(..))

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

-- | The modules compiled, or why they could not be: a failure here is a defect
-- | of the compiler.
compiled :: Either String Compiled
compiled = do
  syntax <- bundle
  base <- baseInt
  own <- compile (syntax.withSignature base.signature) [ base.interface ] syntax.module
  guest <- Guest.bundle
  elab <- compile (guest.withSignature primSignature) [] guest.module
  let moduleInterfaces = [ base.moduleInterface, unexported syntax.unexported own.moduleInterface, elab.moduleInterface ]
  pure
    { modules: [ base.dmo, own.dmo ]
    , signature: own.signature
    , interfaces: [ base.interface, own.interface ]
    , moduleInterfaces
    , preloaded: Map.fromFoldable (map (\i -> Tuple i.name i) moduleInterfaces)
    , descriptor: syntax.descriptor
    }

-- | `Base.Int`, compiled from its source as a build compiles a module: against
-- | `Prim` alone, with no macro run and no synthesis job carried out. What a
-- | module compiled against it is checked with is the signature an importer of
-- | it reads, from an environment holding its interface.
baseInt :: Either String { dmo :: Dmo, signature :: Signature, interface :: Interface, moduleInterface :: ModuleInterface }
baseInt = case compileModule action defaultSettings initialEnvironment Map.empty Source.baseInt of
  Identity (Left errors) -> Left ("Base.Int does not compile: " <> joinWith "; " (map printCompileError (NonEmptyArray.toArray errors)))
  Identity (Right made) -> do
    env <- lmap (\err -> "Base.Int has no environment: " <> show err) (addInterface made.interface initialEnvironment)
    view <- lmap (\err -> "Base.Int has no view: " <> show err) (viewFor [ made.interface.name ] env)
    signature <- lmap (\err -> "Base.Int has no signature: " <> show err) (importedSignature env view)
    pure
      { dmo: made.dmo
      , signature
      , interface: { name: made.interface.name, imports: made.interface.imports, arities: made.interface.arities }
      , moduleInterface: made.interface
      }
  where
  action :: CompilerAction Identity
  action =
    { readSource: \_ -> pure (Left "no file is read")
    , runParser: \_ _ _ -> pure (ExecutionFailedAs { reason: NoSuchModule, detail: "no parser runs" })
    , synthesis: withoutSynthesizers
    , hooks: defaultHooks
    }

-- | An interface with the values given in no export table, a constructor among
-- | them in no type's members, and none of them with an arity, an arity being
-- | of a value a module downstream reaches: a call to one is a `callu`.
unexported :: Array Ident -> ModuleInterface -> ModuleInterface
unexported names i = i
  { exports = i.exports
      { values = Map.filter (\e -> not (Array.elem (local e.entity) names)) i.exports.values
      , types = map (\t -> t { members = Array.filter (\m -> not (Array.elem m names)) t.members }) i.exports.types
      }
  , arities = Map.filterKeys (\n -> not (Array.elem n names)) i.arities
  }
  where
  local (Qualified _ n) = n

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
