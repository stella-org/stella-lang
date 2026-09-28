-- | The reference synthesizer: a policy written in the host against the kernel
-- | facade alone.
-- |
-- | It sees handles, views, and names, and nothing else: its imports hold no
-- | solver state, no Core⁺ term, and no representation of a script, so what it
-- | does is what a guest on Steam could do.
-- |
-- | **It answers a goal from what the goal's site binds, then from the globals
-- | it is given, then from the monomorphic declarations carrying the attribute
-- | it is given**, the first that fits. A goal whose type is an unsolved metavariable
-- | it waits on: the goal is run again once the metavariable is solved.
-- |
-- | What the site binds and the globals given are compared with the goal's type
-- | as constructor views only — a type constructor applied to kinds and to
-- | nothing else — which is a candidate test and not type equality. **A
-- | declaration carrying the attribute is tried inside a transaction**: where
-- | it has no kind variable to instantiate, its claim is unified with the
-- | goal's type, and a candidate that does not fit is rolled back, everything
-- | it did with it, before the next is tried; one with kind variables is passed
-- | over, and nothing is done for it. A postponement or a defect in a candidate
-- | is not caught, and ends the attempt.
module Test.Stella.Compiler.Elaborate.Reference
  ( Policy
  , policy
  , reference
  , workingOnCandidate
  , workingWhileWaiting
  , badApplication
  , sameConstructorView
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Protocol.Facade (Facade, Synthesizer)
import Stella.Compiler.Elaborate.Protocol.Facade as F
import Stella.Compiler.Elaborate.Vocabulary.Handle (Handle)
import Stella.Compiler.Elaborate.Vocabulary.Message (MessagePart(..))
import Stella.Compiler.Elaborate.Vocabulary.View (ConstraintView(..), KindView(..), TypeView(..))
import Stella.Compiler.TypedCore (Ident, Literal(..), Qualified, RowElemKind(..), RowKey(..), Symbol(..))
import Stella.Compiler.TypedCore.Prim (intTy)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

-- | What the reference synthesizer answers from, beyond what the site binds:
-- | the globals given, in order, and the key of the attribute that marks a
-- | declaration as a candidate. `beforeTrying` runs inside the transaction of
-- | each candidate that is tried, given the root scope, the goal's type, and
-- | the candidate, just before the candidate is referred to.
type Policy =
  { globals :: P.Array (Qualified Ident)
  , attribute :: P.String
  , beforeTrying :: Handle -> Handle -> Qualified Ident -> Facade Unit
  }

-- | The policy answering from the globals and the attribute given, doing
-- | nothing before a candidate is tried.
policy :: P.Array (Qualified Ident) -> P.String -> Policy
policy globals attribute = { globals, attribute, beforeTrying: \_ _ _ -> pure unit }

reference :: Policy -> Synthesizer
reference given goal = do
  root <- F.rootScope
  goalType <- F.goalType goal
  F.viewType goalType >>= case _ of
    MetaType m -> F.postpone [ m ]
    wanted -> do
      bound <- F.localContext
      local <- findFirst (\entry -> sameConstructorView wanted <$> F.viewType entry.type) bound
      case local of
        Just entry -> F.localVariable root entry.name
        Nothing -> findFirst (monomorphicAt wanted) given.globals >>= case _ of
          Just name -> F.globalRef root name []
          Nothing -> F.declsWithAttr given.attribute >>= search given root goalType >>= case _ of
            Just found -> pure found
            Nothing -> F.throw
              [ TextPart "nothing the site binds, no global given, and no monomorphic declaration carrying the attribute"
              , TextPart given.attribute
              , TextPart "fits the type"
              , TypePart goalType
              ]

-- Try each candidate in its own transaction, in order, and take the first
-- that fits.
search :: Policy -> Handle -> Handle -> P.Array (Qualified Ident) -> Facade (Maybe Handle)
search given root goalType candidates = case Array.uncons candidates of
  Nothing -> pure Nothing
  Just { head, tail } -> F.transact (trying given root goalType head) >>= case _ of
    Right (Just found) -> pure (Just found)
    Right Nothing -> search given root goalType tail
    Left _ -> search given root goalType tail

-- One candidate: its declaration read and, where it has no kind variable to
-- instantiate, a reference to it built and its claim unified with the goal's
-- type. `Nothing` is a candidate the policy does not try.
trying :: Policy -> Handle -> Handle -> Qualified Ident -> Facade (Maybe Handle)
trying given root goalType name =
  F.lookupGlobal name >>= case _ of
    Just decl | Array.null decl.kindVars -> do
      given.beforeTrying root goalType name
      e <- F.globalRef root name []
      claimed <- F.typeOf e
      F.unify root claimed goalType
      pure (Just e)
    _ -> pure Nothing

-- | The policy given, except that where the candidate named is tried it first
-- | builds what a candidate can leave behind — a metavariable, a constraint on
-- | it that stays open, and a warning — so that a candidate that does not fit
-- | is seen to leave none of it.
workingOnCandidate :: Qualified Ident -> Policy -> Policy
workingOnCandidate candidate given = given
  { beforeTrying = \root goalType name -> do
      given.beforeTrying root goalType name
      when (name == candidate) (leaveBehind root "trying")
  }

-- | The synthesizer given, except where the goal's type is an unsolved
-- | metavariable: there it first builds what an attempt can build — a
-- | metavariable, a constraint on it that stays open, a term, and a warning —
-- | and then waits on the goal's own metavariable, so that everything it built
-- | is what the attempt's rollback discards.
workingWhileWaiting :: Synthesizer -> Synthesizer
workingWhileWaiting answer goal = F.goalType goal >>= F.viewType >>= case _ of
  MetaType m -> do
    root <- F.rootScope
    leaveBehind root "waiting"
    _ <- F.literal root (LitInt 0)
    F.postpone [ m ]
  _ -> answer goal

-- | `(λ(x : Int). x) true`, whatever the goal. Its claim is derived from its
-- | parts — the function's result, `Int` — and says nothing of whether the
-- | argument is at the function's parameter type, which it is not.
badApplication :: Synthesizer
badApplication _ = do
  root <- F.rootScope
  int <- F.typeConstructor root intTy []
  lambda <- F.openLambda root "x" int
  function <- F.emptyRow root >>= F.closeLambda root lambda.binder lambda.variable
  F.literal root (LitBoolean true) >>= F.termApply root function

-- A row metavariable, a Lacks on it that stays open, and a warning, all
-- named by the word given.
leaveBehind :: Handle -> P.String -> Facade Unit
leaveBehind root word = do
  row <- F.freshMetaType root (KindRow RowType)
  F.require root (LacksView (SymbolKey (Symbol word)) row)
  F.warn [ TextPart word ]

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
