-- | The entries the compiler knows by name, which its desugarings refer to: the
-- | elaboration-only entries, which no catalog holds, and the standard entry
-- | `Base.IO.Effect.runIO`, which keeps its source identity, is exported, and
-- | is in the catalog as any exported value is
-- | ([Modules](../../../../../docs/technical-references/06-Modules/01-Modules.md)).
-- |
-- | **The entries are listed by module, each with the scheme it is expected
-- | at**: `Stella.Syntax.$QuotedOrigin` and `Stella.Syntax.$spliced`, which a
-- | quotation is written with, `Base.Continuation.$Continuation`, which a
-- | `reifiable full` clause wraps its continuation in, and `Base.IO.Effect.runIO`,
-- | the standard runner, which the stub running an entry point applies. A
-- | signature that holds a module's type or effect — `Stella.Syntax.OriginRef`,
-- | `Base.Continuation.Continuation`, `Base.IO.Effect.LiftIO` — reaches that
-- | module, and then holds its entries at the schemes listed, up to the names
-- | the schemes bind. **The module declaring them is held to them as it is
-- | declared**, so a declaration at another scheme, or a standard entry left
-- | unexported, is refused where it is compiled; an entry a module importing it
-- | lacks or holds at another scheme, or a standard one it does not find
-- | exported as a value, is the compiler's fault. A signature that does not
-- | reach a module holds none of its entries. Nothing else of the signature is
-- | reached this way, and no synthesizer, which reads the catalog, reaches an
-- | elaboration-only entry.
module Stella.Compiler.Elaborate.Surface.Internal
  ( Internal
  , continuationConstructor
  , standardRunner
  , liftIOEffect
  , entrypointStub
  , internalEntries
  , EntryMismatch
  , EntryDeclaration(..)
  , declaredEntryMismatches
  ) where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.CorePlus.Type (fromCore)
import Stella.Compiler.Elaborate.Environment.Catalog (XScheme)
import Stella.Compiler.Macro.Bundle (syntaxModuleName)
import Stella.Compiler.TypedCore.Kind (Kind(..), RowElemKind(..))
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), ModuleName(..), Qualified(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (fn, ioTy, pureFn, stringTy, unitTy)
import Stella.Compiler.TypedCore.Equality (schemeEquiv)
import Stella.Compiler.TypedCore.Signature (Signature)
import Stella.Compiler.TypedCore.Type (RowEntry(..), Type(..), TypeScheme)

-- | The type a `reifiable full` clause's continuation is wrapped at.
continuationType :: Qualified TyName
continuationType = Qualified (ModuleName "Base.Continuation") (TyName "Continuation")

-- | The constructor a `reifiable full` clause wraps its continuation in.
continuationConstructor :: Qualified Ident
continuationConstructor = Qualified (ModuleName "Base.Continuation") (Ident "$Continuation")

-- | The module declaring the standard runner and the effect it handles.
ioEffectModule :: ModuleName
ioEffectModule = ModuleName "Base.IO.Effect"

-- | The standard runner, which runs a computation performing `LiftIO` alone as
-- | an `IO` action.
standardRunner :: Qualified Ident
standardRunner = Qualified ioEffectModule (Ident "runIO")

-- | The effect the standard runner handles.
liftIOEffect :: Qualified EffName
liftIOEffect = Qualified ioEffectModule (EffName "LiftIO")

-- | The value elaboration declares to run an entry point that is a computation,
-- | under a name no source writes, one in a module.
entrypointStub :: Ident
entrypointStub = Ident "$entrypoint"

-- | Each entry the compiler's desugarings refer to, at its scheme.
type Internal = Map (Qualified Ident) XScheme

-- | The entries the signature holds at the schemes listed, up to the names the
-- | schemes bind, or the first it lacks or holds at another, which is the
-- | compiler's fault; a standard entry must also be among the values given,
-- | those the modules the imports reach export. **The module given is held to
-- | none of its own here**: its values are not yet in the signature its
-- | declarations are elaborated against, and what it declares is held to the
-- | schemes once it is declared (`declaredEntryMismatches`).
internalEntries :: ModuleName -> Signature -> Set (Qualified Ident) -> Either (Qualified Ident) Internal
internalEntries self sig exported = Map.fromFoldable <$> traverse entry (Array.concatMap (reached (_ /= self) sig) listed)
  where
  entry e = case heldIn sig e of
    Just scheme | schemeEquiv scheme e.expected && (not e.standard || Set.member e.name exported) -> Right (Tuple e.name { kindVars: scheme.kindVars, body: fromCore scheme.body })
    _ -> Left e.name

-- | An entry the module declares that is not the one listed.
type EntryMismatch = { name :: Qualified Ident, expected :: TypeScheme, declared :: EntryDeclaration }

-- | How a module declares an entry otherwise than listed.
data EntryDeclaration
  -- | Not at all.
  = EntryAbsent
  -- | At another scheme.
  | EntryAt TypeScheme
  -- | A standard entry at the scheme listed, which the module does not declare
  -- | as a value and export.
  | EntryUnexported

-- | The entries of its own the module given declares otherwise than listed,
-- | read off the signature it is declared to: a module whose type or effect
-- | reaches its entries declares each of them at the scheme listed, up to the
-- | names the schemes bind, and declares each standard one as a value and
-- | exports it, as the values given record. What a module importing it is
-- | compiled with then holds them.
declaredEntryMismatches :: ModuleName -> Signature -> Set (Qualified Ident) -> Array EntryMismatch
declaredEntryMismatches self sig exported = Array.mapMaybe mismatch (Array.concatMap (reached (_ == self) sig) listed)
  where
  mismatch e = (\declared -> { name: e.name, expected: e.expected, declared }) <$> case heldIn sig e of
    Just scheme
      | not (schemeEquiv scheme e.expected) -> Just (EntryAt scheme)
      | e.standard && not (Set.member e.name exported) -> Just EntryUnexported
      | otherwise -> Nothing
    Nothing -> Just EntryAbsent

-- | An entry the compiler lists: its name, whether it is a constructor or a
-- | value, whether it is a standard entry, which keeps its source identity and
-- | is exported, and the scheme it is expected at.
type Listed = { name :: Qualified Ident, constructor :: Boolean, standard :: Boolean, expected :: TypeScheme }

-- | What of its module reaches an entry: a type, or an effect.
data Reaching
  = ByType (Qualified TyName)
  | ByEffect (Qualified EffName)

-- | The entries of the modules a signature reaches by a type or an effect of
-- | theirs, of the modules the predicate admits.
reached :: (ModuleName -> Boolean) -> Signature -> { reaching :: Reaching, entries :: Array Listed } -> Array Listed
reached admits sig m = case m.reaching of
  ByType t@(Qualified owner _) | admits owner && Map.member t sig.types -> m.entries
  ByEffect e@(Qualified owner _) | admits owner && Map.member e sig.effects -> m.entries
  _ -> []

-- | The scheme the signature holds an entry at, where it holds it.
heldIn :: Signature -> Listed -> Maybe TypeScheme
heldIn sig e
  | e.constructor = _.scheme <$> Map.lookup e.name sig.ctors
  | otherwise = _.scheme <$> Map.lookup e.name sig.values

-- | The entries, each under the type or effect of its module that reaches them.
listed :: Array { reaching :: Reaching, entries :: Array Listed }
listed =
  [ { reaching: ByType (Qualified syntaxModuleName (TyName "OriginRef"))
    , entries:
        [ { name: quotedOrigin, constructor: true, standard: false, expected: mono (fns [ string, syntax "Position", syntax "Position" ] (syntax "OriginRef")) }
        , { name: spliced, constructor: false, standard: false, expected: mono (TForall c KType (fns [ syntax "OriginRef", TApp (syntax "List") (syntax "Trivia"), TApp (syntax "Syntax") (TVar c) ] (syntax "SyntaxNode"))) }
        ]
    }
  , { reaching: ByType continuationType
    , entries:
        [ { name: continuationConstructor
          , constructor: true
          , standard: false
          , expected: mono (TForall a KType (TForall b KType (TForall r (KRow RowEffect) (pureFn (fn (TVar a) (TVar r) (TVar b)) (TApp (TApp (TApp (TCon continuationType []) (TVar a)) (TVar b)) (TVar r))))))
          }
        ]
    }
  , { reaching: ByEffect liftIOEffect
    , entries:
        [ { name: standardRunner
          , constructor: false
          , standard: true
          , expected: mono (TForall a KType (pureFn (fn (TCon unitTy []) (TRowExtend (RowEffectEntry liftIOEffect []) TRowEmpty) (TVar a)) (TApp (TCon ioTy []) (TVar a))))
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
