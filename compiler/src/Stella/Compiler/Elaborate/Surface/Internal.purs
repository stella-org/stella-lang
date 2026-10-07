-- | The entries a desugaring the compiler carries out refers to and no catalog
-- | holds: the elaboration-only entries of a module the compiler writes
-- | ([Modules](../../../../../docs/technical-references/06-Modules/01-Modules.md)).
-- |
-- | **The entries are listed, each with the scheme it is expected at**:
-- | `Stella.Syntax.$QuotedOrigin` and `Stella.Syntax.$spliced`, which a
-- | quotation is written with. A signature that holds `Stella.Syntax.OriginRef`
-- | reaches `Stella.Syntax`, and then holds both entries at the schemes listed;
-- | one it lacks or holds at another scheme is the compiler's fault. A signature
-- | that does not reach `Stella.Syntax` holds none. Nothing else of the
-- | signature is reached this way, and no synthesizer, which reads the catalog,
-- | reaches these.
module Stella.Compiler.Elaborate.Surface.Internal
  ( Internal
  , internalEntries
  ) where

import Prelude
import Prim hiding (Type)

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
import Stella.Compiler.TypedCore.Kind (Kind(..))
import Stella.Compiler.TypedCore.Name (Ident(..), Qualified(..), TyName(..), TyVar(..))
import Stella.Compiler.TypedCore.Prim (pureFn, stringTy)
import Stella.Compiler.TypedCore.Signature (Signature)
import Stella.Compiler.TypedCore.Type (Type(..), TypeScheme)

-- | Each entry the compiler's desugarings refer to, at its scheme.
type Internal = Map (Qualified Ident) XScheme

-- | The entries the signature holds at the schemes listed, or the first it
-- | lacks or holds at another, which is the compiler's fault.
internalEntries :: Signature -> Either (Qualified Ident) Internal
internalEntries sig =
  if Map.member (Qualified syntaxModuleName (TyName "OriginRef")) sig.types then Map.fromFoldable <$> traverse entry listed
  else Right Map.empty
  where
  entry e = case e.held of
    Just scheme | scheme == e.expected -> Right (Tuple e.name { kindVars: scheme.kindVars, body: fromCore scheme.body })
    _ -> Left e.name

  listed =
    [ { name: quotedOrigin, held: _.scheme <$> Map.lookup quotedOrigin sig.ctors, expected: mono (fns [ string, syntax "Position", syntax "Position" ] (syntax "OriginRef")) }
    , { name: spliced, held: _.scheme <$> Map.lookup spliced sig.values, expected: mono (TForall c KType (fns [ syntax "OriginRef", TApp (syntax "List") (syntax "Trivia"), TApp (syntax "Syntax") (TVar c) ] (syntax "SyntaxNode"))) }
    ]

  quotedOrigin = Qualified syntaxModuleName (Ident "$QuotedOrigin")
  spliced = Qualified syntaxModuleName (Ident "$spliced")
  c = TyVar "c"
  string = TCon stringTy []
  syntax n = TCon (Qualified syntaxModuleName (TyName n)) []
  fns args result = foldr pureFn result args

  mono :: Type -> TypeScheme
  mono body = { kindVars: [], body }
