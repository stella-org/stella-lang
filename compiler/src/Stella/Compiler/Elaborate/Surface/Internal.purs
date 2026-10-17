-- | The entries a desugaring the compiler carries out refers to and no catalog
-- | holds: the elaboration-only entries of a module the compiler writes
-- | ([Modules](../../../../../docs/technical-references/06-Modules/01-Modules.md)).
-- |
-- | **The entries are listed by module, each with the scheme it is expected
-- | at**: `Stella.Syntax.$QuotedOrigin` and `Stella.Syntax.$spliced`, which a
-- | quotation is written with, and `Base.Continuation.$Continuation`, which a
-- | `reifiable full` clause wraps its continuation in. A signature that holds a
-- | module's type — `Stella.Syntax.OriginRef`, `Base.Continuation.Continuation`
-- | — reaches that module, and then holds its entries at the schemes listed;
-- | one it lacks or holds at another scheme is the compiler's fault. A signature
-- | that does not reach a module holds none of its entries. Nothing else of the
-- | signature is reached this way, and no synthesizer, which reads the catalog,
-- | reaches these.
module Stella.Compiler.Elaborate.Surface.Internal
  ( Internal
  , continuationConstructor
  , internalEntries
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.CorePlus.Type (fromCore)
import Stella.Compiler.Elaborate.Environment.Catalog (XScheme)
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..))
import Stella.Compiler.TypedCore.Name (Ident(..), ModuleName(..), Qualified(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (fn, pureFn, stringTy)
import Stella.Compiler.TypedCore.Signature (Signature)
import Stella.Compiler.TypedCore.Type (Type(..), TypeScheme)

-- | The type a `reifiable full` clause's continuation is wrapped at.
continuationType :: Qualified TyName
continuationType = Qualified (ModuleName "Base.Continuation") (TyName "Continuation")

-- | The constructor a `reifiable full` clause wraps its continuation in.
continuationConstructor :: Qualified Ident
continuationConstructor = Qualified (ModuleName "Base.Continuation") (Ident "$Continuation")

-- | Each entry the compiler's desugarings refer to, at its scheme.
type Internal = Map (Qualified Ident) XScheme

-- | The entries the signature holds at the schemes listed, or the first it
-- | lacks or holds at another, which is the compiler's fault.
internalEntries :: Signature -> Either (Qualified Ident) Internal
internalEntries sig = Map.fromFoldable <$> traverse entry (Array.concatMap reached listed)
  where
  reached m = if Map.member m.reaching sig.types then m.entries else []

  entry e = case e.held of
    Just scheme | scheme == e.expected -> Right (Tuple e.name { kindVars: scheme.kindVars, body: fromCore scheme.body })
    _ -> Left e.name

  listed =
    [ { reaching: Qualified syntaxModuleName (TyName "OriginRef")
      , entries:
          [ { name: quotedOrigin, held: _.scheme <$> Map.lookup quotedOrigin sig.ctors, expected: mono (fns [ string, syntax "Position", syntax "Position" ] (syntax "OriginRef")) }
          , { name: spliced, held: _.scheme <$> Map.lookup spliced sig.values, expected: mono (TForall c KType (fns [ syntax "OriginRef", TApp (syntax "List") (syntax "Trivia"), TApp (syntax "Syntax") (TVar c) ] (syntax "SyntaxNode"))) }
          ]
      }
    , { reaching: continuationType
      , entries:
          [ { name: continuationConstructor
            , held: _.scheme <$> Map.lookup continuationConstructor sig.ctors
            , expected: mono (TForall a KType (TForall b KType (TForall r (KRow RowEffect) (pureFn (fn (TVar a) (TVar r) (TVar b)) (TApp (TApp (TApp (TCon continuationType []) (TVar a)) (TVar b)) (TVar r))))))
            }
          ]
      }
    ]

  quotedOrigin = Qualified syntaxModuleName (Ident "$QuotedOrigin")
  spliced = Qualified syntaxModuleName (Ident "$spliced")
  a = TyVar "a"
  b = TyVar "b"
  c = TyVar "c"
  r = TyVar "r"
  string = TCon stringTy []
  syntax n = TCon (Qualified syntaxModuleName (TyName n)) []
  fns args result = foldr pureFn result args

  mono :: Type -> TypeScheme
  mono body = { kindVars: [], body }
