-- | The entries a desugaring the compiler carries out refers to and no catalog
-- | holds: the elaboration-only entries the compiler lists
-- | ([Modules](../../../../../docs/technical-references/06-Modules/01-Modules.md)).
-- |
-- | **The entries are listed by module, each with the scheme it is expected
-- | at**: `Stella.Syntax.$QuotedOrigin` and `Stella.Syntax.$spliced`, which a
-- | quotation is written with, and `Base.Continuation.$Continuation`, which a
-- | `reifiable full` clause wraps its continuation in. A signature that holds a
-- | module's type — `Stella.Syntax.OriginRef`, `Base.Continuation.Continuation`
-- | — reaches that module, and then holds its entries at the schemes listed, up
-- | to the names the schemes bind. **The module declaring them is held to them
-- | as it is declared**, so a declaration at another scheme is refused where it is
-- | compiled; one a module importing it lacks or holds at another scheme is the
-- | compiler's fault. A signature that does not reach a module holds none of
-- | its entries. Nothing else of the signature is reached this way, and no
-- | synthesizer, which reads the catalog, reaches these.
module Stella.Compiler.Elaborate.Surface.Internal
  ( Internal
  , continuationConstructor
  , internalEntries
  , EntryMismatch
  , declaredEntryMismatches
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
import Stella.Compiler.TypedCore.Equality (schemeEquiv)
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

-- | The entries the signature holds at the schemes listed, up to the names the
-- | schemes bind, or the first it lacks or holds at another, which is the
-- | compiler's fault. **The module given is held to none of its own here**: its
-- | values are not yet in the signature its declarations are elaborated
-- | against, and what it declares is held to the schemes once it is declared
-- | (`declaredEntryMismatches`).
internalEntries :: ModuleName -> Signature -> Either (Qualified Ident) Internal
internalEntries self sig = Map.fromFoldable <$> traverse entry (Array.concatMap (reached (_ /= self) sig) listed)
  where
  entry e = case heldIn sig e of
    Just scheme | schemeEquiv scheme e.expected -> Right (Tuple e.name { kindVars: scheme.kindVars, body: fromCore scheme.body })
    _ -> Left e.name

-- | An entry the module declares that is not the one listed: absent from what
-- | the module declares, or declared at another scheme.
type EntryMismatch = { name :: Qualified Ident, expected :: TypeScheme, declared :: Maybe TypeScheme }

-- | The entries of its own the module given declares otherwise than listed,
-- | read off the signature it is declared to: a module whose type reaches its
-- | entries declares each of them, at the scheme listed up to the names the
-- | schemes bind. What a module importing it is compiled with then holds them.
declaredEntryMismatches :: ModuleName -> Signature -> Array EntryMismatch
declaredEntryMismatches self sig = Array.mapMaybe mismatch (Array.concatMap (reached (_ == self) sig) listed)
  where
  mismatch e = case heldIn sig e of
    Just scheme | schemeEquiv scheme e.expected -> Nothing
    declared -> Just { name: e.name, expected: e.expected, declared }

-- | An entry the compiler lists: its name, whether it is a constructor or a
-- | value, and the scheme it is expected at.
type Listed = { name :: Qualified Ident, constructor :: Boolean, expected :: TypeScheme }

-- | The entries of the modules a signature reaches by a type of theirs, of the
-- | modules the predicate admits.
reached :: (ModuleName -> Boolean) -> Signature -> { reaching :: Qualified TyName, entries :: Array Listed } -> Array Listed
reached admits sig m = case m.reaching of
  Qualified owner _ | admits owner && Map.member m.reaching sig.types -> m.entries
  _ -> []

-- | The scheme the signature holds an entry at, where it holds it.
heldIn :: Signature -> Listed -> Maybe TypeScheme
heldIn sig e
  | e.constructor = _.scheme <$> Map.lookup e.name sig.ctors
  | otherwise = _.scheme <$> Map.lookup e.name sig.values

-- | The entries, each under the type of its module that reaches them.
listed :: Array { reaching :: Qualified TyName, entries :: Array Listed }
listed =
  [ { reaching: Qualified syntaxModuleName (TyName "OriginRef")
    , entries:
        [ { name: quotedOrigin, constructor: true, expected: mono (fns [ string, syntax "Position", syntax "Position" ] (syntax "OriginRef")) }
        , { name: spliced, constructor: false, expected: mono (TForall c KType (fns [ syntax "OriginRef", TApp (syntax "List") (syntax "Trivia"), TApp (syntax "Syntax") (TVar c) ] (syntax "SyntaxNode"))) }
        ]
    }
  , { reaching: continuationType
    , entries:
        [ { name: continuationConstructor
          , constructor: true
          , expected: mono (TForall a KType (TForall b KType (TForall r (KRow RowEffect) (pureFn (fn (TVar a) (TVar r) (TVar b)) (TApp (TApp (TApp (TCon continuationType []) (TVar a)) (TVar b)) (TVar r))))))
          }
        ]
    }
  ]
  where
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
