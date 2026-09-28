-- | The reference synthesizer: a policy written in the host against the kernel
-- | facade alone.
-- |
-- | It sees handles, views, and names, and nothing else: its imports hold no
-- | solver state, no Core⁺ term, and no representation of a script, so what it
-- | does is what a guest on Steam could do.
-- |
-- | **It answers a goal from what the goal's site binds, or else from the
-- | globals it is given**, the first whose type is the goal's. A goal whose type
-- | is an unsolved metavariable it waits on: the goal is run again once the
-- | metavariable is solved. Types are compared as constructor views only — a
-- | type constructor applied to kinds and to nothing else — which is a
-- | candidate test for the goals it answers, and not type equality: a goal at
-- | any other type it cannot answer, and it fails.
module Test.Stella.Compiler.Elaborate.Reference
  ( reference
  , workingWhileWaiting
  , sameConstructorView
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Protocol.Facade (Facade, Synthesizer)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Vocabulary.View (ConstraintView(..), KindView(..), TypeView(..))
import Stella.Compiler.TypedCore (Ident, Literal(..), Qualified, RowElemKind(..), RowKey(..), Symbol(..))
import Data.Array as Array
import Data.Maybe (Maybe(..))

-- | The reference synthesizer, trying the globals given, in order, after what
-- | the site binds.
reference :: P.Array (Qualified Ident) -> Synthesizer
reference globals goal = do
  root <- F.rootScope
  goalType <- F.goalType goal
  F.viewType goalType >>= case _ of
    MetaType m -> F.postpone [ m ]
    wanted -> do
      bound <- F.localContext
      local <- findFirst (\entry -> sameConstructorView wanted <$> F.viewType entry.type) bound
      case local of
        Just entry -> F.localVariable root entry.name
        Nothing -> findFirst (monomorphicAt wanted) globals >>= case _ of
          Just name -> F.globalRef root name []
          Nothing -> F.throw [ TextPart "nothing in scope, and no global given, has the type", TypePart goalType ]

-- | The synthesizer given, except where the goal's type is an unsolved
-- | metavariable: there it first builds what an attempt can build — a
-- | metavariable, a constraint on it that stays open, a term, and a warning —
-- | and then waits on the goal's own metavariable, so that everything it built
-- | is what the attempt's rollback discards.
workingWhileWaiting :: Synthesizer -> Synthesizer
workingWhileWaiting answer goal = F.goalType goal >>= F.viewType >>= case _ of
  MetaType m -> do
    root <- F.rootScope
    row <- F.freshMetaType root (KindRow RowType)
    F.require root (LacksView (SymbolKey (Symbol "waiting")) row)
    _ <- F.literal root (LitInt 0)
    F.warn [ TextPart "waiting" ]
    F.postpone [ m ]
  _ -> answer goal

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
