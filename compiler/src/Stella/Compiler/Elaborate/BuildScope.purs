-- | What the kernel's requests over types share: resolving a build scope's
-- | types, kinding what is built in one, and the site an obligation raised in
-- | one carries.
-- |
-- | A request takes a build scope as a handle the host issued, and everything
-- | here reads the scope and nothing the caller states: the types it may use are
-- | the ones built in it or in its ancestors, what is built in it is kinded under
-- | what it binds, and an obligation raised in it is decided against its context.
module Stella.Compiler.Elaborate.BuildScope
  ( usableIn
  , built
  , kinded
  , issueBuilt
  , siteOf
  , requiredIn
  , constraintIn
  , kindingScopeOf
  , kindIn
  , rejected
  ) where

import Prelude

import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..))
import Stella.Compiler.Elaborate.Elab (Elab, askEnv, break, currentMetas, issue, require, resolveType)
import Stella.Compiler.Elaborate.Handle (Handle, HandleObject(..), ScopeObject, TypeObject)
import Stella.Compiler.Elaborate.Kind (XKind(..))
import Stella.Compiler.Elaborate.Kinding (KindEvidence, KindingScope, checkConstraint, settledIn, synthKind)
import Stella.Compiler.Elaborate.Pending (Site)
import Stella.Compiler.Elaborate.Type (XConstraint(..), XType)
import Stella.Compiler.Elaborate.Unify (substitute)
import Stella.Compiler.Elaborate.View (ConstraintView(..), KindView(..))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Set as Set

-- | A type the scope may use: one built in it or in one of its ancestors.
usableIn :: ScopeObject -> Handle -> Elab TypeObject
usableIn scope handle = do
  object <- resolveType handle
  case object.builtIn of
    Just id | id == scope.id || Set.member id scope.ancestors -> pure object
    _ -> rejected (ScopeViolation handle)

-- | Issue a type built in the scope, once the kinding judgement admits it.
built :: ScopeObject -> XType -> Elab Handle
built scope ty = kinded scope ty >>= issueBuilt scope

-- | A type zonked, with the kind evidence the judgement gives it in the scope.
kinded :: ScopeObject -> XType -> Elab { type :: XType, kind :: KindEvidence }
kinded scope ty = do
  env <- askEnv
  metas <- currentMetas
  let
    zonked = substitute metas ty
  case synthKind env.session.kinding (kindingScopeOf scope) metas zonked of
    Left fault -> rejected (IllKinded fault)
    Right kind -> pure { type: zonked, kind }

issueBuilt :: ScopeObject -> { type :: XType, kind :: KindEvidence } -> Elab Handle
issueBuilt scope typed =
  issue (TypeObject { type: typed.type, kind: typed.kind, scope: kindingScopeOf scope, builtIn: Just scope.id })

-- | The site an obligation built in the scope carries: the scope's context, which
-- | holds every assumption opened around it, and the origin of the running job.
siteOf :: ScopeObject -> Elab Site
siteOf scope = do
  env <- askEnv
  case env.frame of
    Nothing -> break NoFrame
    Just frame -> pure { context: scope.context, origin: frame.site.origin }

-- | Require what a row being built needs, of the scope it is built in.
requiredIn :: ScopeObject -> XConstraint -> Elab Unit
requiredIn scope constraint = do
  site <- siteOf scope
  require site constraint

-- | A constraint from types the scope may use, judged well-formed there.
constraintIn :: ScopeObject -> ConstraintView -> Elab XConstraint
constraintIn scope view = do
  constraint <- case view of
    LacksView key row -> XLacks key <<< _.type <$> usableIn scope row
    DisjointView l r -> XDisjoint <$> (_.type <$> usableIn scope l) <*> (_.type <$> usableIn scope r)
  env <- askEnv
  metas <- currentMetas
  case checkConstraint env.session.kinding (kindingScopeOf scope) metas constraint of
    Left fault -> rejected (IllKinded fault)
    Right _ -> pure constraint

kindingScopeOf :: ScopeObject -> KindingScope
kindingScopeOf scope = { kindVars: scope.context.kindVars, tyVars: scope.context.tyVars }

-- | A kind view as a kind the scope can write.
kindIn :: ScopeObject -> KindView -> Elab XKind
kindIn scope view = case toKind view of
  Nothing -> rejected AnyRowAsKind
  Just kind -> do
    metas <- currentMetas
    case settledIn (kindingScopeOf scope) metas kind of
      Left fault -> rejected (IllKinded fault)
      Right k -> pure k
  where
  toKind = case _ of
    KindType -> Just XKType
    KindEffect -> Just XKEffect
    KindRow e -> Just (XKRow e)
    KindFun a b -> XKFun <$> toKind a <*> toKind b
    KindVar v -> Just (XKVar v)
    KindAnyRow -> Nothing

rejected :: forall a. BuildError -> Elab a
rejected err = break (BuildRejected err)

