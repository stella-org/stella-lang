-- | `Stella.Syntax` compiled, with the one module it depends on: what a
-- | compile-time session loads before it runs a parser, and what a module
-- | declaring a parser is compiled against.
-- |
-- | **`Base.Int` is compiled from the ABI table** ([Primitive](../Primitive.purs))
-- | as any `Base` module is, so the session loads it as it loads every module,
-- | and carries out each of its entries as the operation the entry is.
module Stella.Compiler.Macro.Compiled
  ( Interface
  , Compiled
  , compiled
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Map (Map)
import Stella.Compiler.Bytecode (Dmo, lower)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor)
import Stella.Compiler.Interface (aritiesOf, importsOf)
import Stella.Compiler.Macro.Bundle (bundle)
import Stella.Compiler.MiddleEnd (translate)
import Stella.Compiler.Primitive (baseModule, withBaseTypes)
import Stella.Compiler.TypedCore (Module, Signature, declareAnnotated, primSignature)
import Stella.Compiler.TypedCore.Name (Ident, ModuleName(..))

-- | What a translation reads of a module it is compiled against.
type Interface = { name :: ModuleName, imports :: Array ModuleName, arities :: Map Ident Int }

-- | The modules in the order they load, `Base.Int` first; the signature holding
-- | both, `OriginRef` among its types; the interfaces of both; and the
-- | descriptor of the types a value crossing to the host has.
type Compiled =
  { modules :: Array Dmo
  , signature :: Signature
  , interfaces :: Array Interface
  , descriptor :: Descriptor
  }

-- | The two modules compiled, or why they could not be: a failure here is a
-- | defect of the compiler.
compiled :: Either String Compiled
compiled = do
  syntax <- bundle
  base <- compile (withBaseTypes primSignature) [] (baseModule unit (ModuleName "Base.Int"))
  own <- compile (syntax.withSignature base.signature) [ base.interface ] syntax.module
  pure
    { modules: [ base.dmo, own.dmo ]
    , signature: own.signature
    , interfaces: [ base.interface, own.interface ]
    , descriptor: syntax.descriptor
    }

compile
  :: Signature
  -> Array Interface
  -> Module Unit
  -> Either String { dmo :: Dmo, signature :: Signature, interface :: Interface }
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
  pure
    { dmo: lowered.dmo
    , signature: declared.signature
    , interface: { name: mid.module.name, imports: mid.module.imports, arities: aritiesOf mid.module }
    }
  where
  named what why = show m.name <> " " <> what <> ": " <> why
