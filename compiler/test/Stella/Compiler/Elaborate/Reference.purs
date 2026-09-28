-- | The reference synthesizer: a policy written in the host against the kernel
-- | facade alone.
-- |
-- | It sees handles, views, and names, and nothing else: its imports hold no
-- | solver state, no Core⁺ term, and no representation of a script, so what it
-- | does is what a guest on Steam could do.
-- |
-- | **It answers a goal from what the goal's site binds, or else from the
-- | globals it is given**, the first whose type is the goal's. Types are
-- | compared as constructor views only — a type constructor applied to kinds
-- | and to nothing else — which is a candidate test for the goals it answers,
-- | and not type equality: a goal at any other type, or at a metavariable, it
-- | cannot answer, and it fails.
module Test.Stella.Compiler.Elaborate.Reference
  ( reference
  , sameConstructorView
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Protocol.Facade (Facade, Synthesizer)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Vocabulary.View (TypeView(..))
import Stella.Compiler.TypedCore (Ident, Qualified)
import Data.Array as Array
import Data.Maybe (Maybe(..))

-- | The reference synthesizer, trying the globals given, in order, after what
-- | the site binds.
reference :: P.Array (Qualified Ident) -> Synthesizer
reference globals goal = do
  root <- F.rootScope
  goalType <- F.goalType goal
  wanted <- F.viewType goalType
  bound <- F.localContext
  local <- findFirst (\entry -> sameConstructorView wanted <$> F.viewType entry.type) bound
  case local of
    Just entry -> F.localVariable root entry.name
    Nothing -> findFirst (monomorphicAt wanted) globals >>= case _ of
      Just name -> F.globalRef root name []
      Nothing -> F.throw [ TextPart "nothing in scope, and no global given, has the type", TypePart goalType ]

-- | Whether two views are the same type constructor applied to the same kinds.
-- | Any other view is not compared.
sameConstructorView :: TypeView -> TypeView -> P.Boolean
sameConstructorView (ConType leftName leftKinds) (ConType rightName rightKinds) =
  leftName == rightName && leftKinds == rightKinds
sameConstructorView _ _ = false

-- Whether the global named is one the catalog holds, with no kind variable to
-- instantiate, at the type the view given shows.
monomorphicAt :: TypeView -> Qualified Ident -> Facade P.Boolean
monomorphicAt wanted name = F.lookupGlobal name >>= case _ of
  Just decl | Array.null decl.kindVars -> sameConstructorView wanted <$> F.viewType decl.scheme
  _ -> pure false

-- The first of the values given the test holds of, tried in order.
findFirst :: forall a. (a -> Facade P.Boolean) -> P.Array a -> Facade (Maybe a)
findFirst test values = case Array.uncons values of
  Nothing -> pure Nothing
  Just { head, tail } -> test head >>= if _ then pure (Just head) else findFirst test tail
