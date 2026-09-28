-- | The kernel's type builders: how a synthesizer assembles a type from the
-- | handles it holds.
-- |
-- | **A type is built in a build scope**, an opaque handle naming what the type
-- | may mention. The root is opened on the site of the running job; opening a
-- | `forall` or a constraint gives a child scope whose body is built in it. A
-- | builder uses a type only where the type was built in the scope given or in
-- | one of its ancestors, and never merges the scopes of the types it is given:
-- | two binders that share a name and a kind are still two binders, and only the
-- | scope a type was built in says which one it mentions.
-- |
-- | **A type observed rather than built carries the scope it came from.** What the
-- | site gives is the root's; a part of a type is the scope of the whole; the body
-- | of a `forall` or of a constraint, and a catalog scheme, belong to no build
-- | scope and reach a builder only through the operation that opens them —
-- | `instantiateForall` for a type, `instantiateScheme` for a scheme.
-- |
-- | **The host ABI is first order.** Opening a binder hands back the binder and
-- | the scope its body is built in, and closing it takes both back, in the scope
-- | it was opened in. No request of the host waits on a guest closure. **Every
-- | binder opened is closed exactly once, inside out, before the attempt
-- | succeeds**: what is built under one — an obligation proved from its assumption, a job, a
-- | metavariable — would otherwise commit without the type carrying it.
-- |
-- | **A row is sharp by construction.** Kinding judges a row's shape; that no key
-- | occurs twice is what extending and joining a row require of it, and each
-- | builder introduces that requirement together with the row, as an obligation
-- | decided against the facts of the scope it is built in. A row it breaks is a
-- | failure, as any constraint a candidate breaks is.
-- |
-- | Every result is kinded by the read-only kinding judgement under its scope. A
-- | builder asked for what cannot be built — a kind that does not fit, a type
-- | from another scope, a binder closed where it was not opened — is a defect of
-- | the synthesizer that asked; whether a candidate fits a goal is `unify`'s to
-- | decide.
module Stella.Compiler.Elaborate.Build
  ( rootScope
  , typeVariable
  , typeConstructor
  , applyType
  , emptyRow
  , extendRow
  , unionRow
  , openForall
  , closeForall
  , openConstraint
  , closeConstraint
  , instantiateForall
  , instantiateScheme
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.BuildScope (built, closedOver, inheritingChild, constraintIn, instantiatedAt, issueBuilt, kindIn, kinded, rejected, requiredIn, schemeAt, siteOf, usableIn)
import Stella.Compiler.Elaborate.Context as Context
import Stella.Compiler.Elaborate.Context (bindTyVar)
import Stella.Compiler.Elaborate.Diagnostic (BuildError(..), Defect(..))
import Stella.Compiler.Elaborate.Elab (Elab, askEnv, assume, break, currentMetas, freshBinderName, holdOpen, issue, resolveBinder, resolveScope, resolveType)
import Stella.Compiler.Elaborate.Handle (BinderObject(..), Handle, HandleObject(..), ScopeId(..), ScopeObject)
import Stella.Compiler.Elaborate.Kinding (quantifiable)
import Stella.Compiler.Elaborate.Type (XConstraint(..), XRowEntry(..), XType(..), xRowEntryKey)
import Stella.Compiler.Elaborate.Unify (substitute)
import Stella.Compiler.Elaborate.View (ConstraintView, KindView, PayloadView(..))
import Stella.Compiler.TypedCore (Ident, Qualified, RowKey(..), TyName, TyVar)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (traverse)

-- | The root build scope, opened on the site of the running job.
rootScope :: Elab Handle
rootScope = do
  env <- askEnv
  case env.frame of
    Nothing -> break NoFrame
    Just frame -> issue (ScopeObject { id: ScopeId 0, ancestors: Set.empty, context: frame.site.context, joins: Map.empty, tree: Nothing })

-- | A type variable the scope binds.
typeVariable :: Handle -> TyVar -> Elab Handle
typeVariable scopeHandle name = do
  scope <- resolveScope scopeHandle
  if Map.member name scope.context.tyVars then built scope (XVar name)
  else rejected (UnboundTypeVariable name)

-- | A type constructor at the kinds given.
typeConstructor :: Handle -> Qualified TyName -> P.Array KindView -> Elab Handle
typeConstructor scopeHandle name kinds = do
  scope <- resolveScope scopeHandle
  ks <- traverse (kindIn scope) kinds
  built scope (XCon name ks)

-- | `f a`.
applyType :: Handle -> Handle -> Handle -> Elab Handle
applyType scopeHandle f a = do
  scope <- resolveScope scopeHandle
  head <- usableIn scope f
  argument <- usableIn scope a
  built scope (XApp head.type argument.type)

-- | `()`, standing at any row kind.
emptyRow :: Handle -> Elab Handle
emptyRow scopeHandle = do
  scope <- resolveScope scopeHandle
  built scope XRowEmpty

-- | `( key : payload | rest )`, requiring `key ∉ rest`.
-- |
-- | The key says which element the payload makes: a structural key a field of a
-- | type, `EffectKey E` an unlabelled `E`, and a `SymbolKey` over an effect a
-- | labelled one. A region element is refused: only the handler owning a region
-- | introduces or removes one.
extendRow :: Handle -> RowKey -> PayloadView -> Handle -> Elab Handle
extendRow scopeHandle key payload restHandle = do
  scope <- resolveScope scopeHandle
  entry <- entryIn scope key payload
  rest <- usableIn scope restHandle
  row <- kinded scope (XRowExtend entry rest.type)
  requiredIn scope (XLacks (xRowEntryKey entry) rest.type)
  issueBuilt scope row

-- | `left ⊎ right`, requiring `left # right`.
unionRow :: Handle -> Handle -> Handle -> Elab Handle
unionRow scopeHandle leftHandle rightHandle = do
  scope <- resolveScope scopeHandle
  left <- usableIn scope leftHandle
  right <- usableIn scope rightHandle
  row <- kinded scope (XRowUnion left.type right.type)
  requiredIn scope (XDisjoint left.type right.type)
  issueBuilt scope row

-- | Open `forall (a : κ)`: a binder, the variable it binds as a type built in the
-- | body's scope, and that scope.
-- |
-- | The variable is named after the hint and made fresh by the host, so it
-- | captures no name the scope already binds.
openForall
  :: Handle
  -> P.String
  -> KindView
  -> Elab { binder :: Handle, variable :: Handle, bodyScope :: Handle }
openForall scopeHandle hint kindView = do
  scope <- resolveScope scopeHandle
  kind <- kindIn scope kindView
  case quantifiable kind of
    Left fault -> rejected (IllKinded fault)
    Right _ -> pure unit
  name <- freshBinderName (Map.keys scope.context.tyVars) hint
  child <- inheritingChild scope (bindTyVar scope.context name kind)
  binder <- issue (BinderObject (ForallBinder { name, kind, parent: scope.id, body: child.id }))
  holdOpen child.id child.ancestors
  variable <- built child (XVar name)
  bodyScope <- issue (ScopeObject child)
  pure { binder, variable, bodyScope }

-- | Close a `forall` opened in this scope, over a body built in the body's scope
-- | or in one this scope can use.
closeForall :: Handle -> Handle -> Handle -> Elab Handle
closeForall scopeHandle binderHandle bodyHandle = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    ForallBinder b -> do
      body <- resolveType bodyHandle
      closedOver scope binderHandle b body.builtIn bodyHandle
      built scope (XForall b.name b.kind body.type)
    AssumedConstraint _ -> misuse
    LambdaBinder _ -> misuse
    TypeAbsBinder _ -> misuse
    ConstraintAbsBinder _ -> misuse
    LetBinder _ -> misuse
    LetRecGroup _ -> misuse
    JoinBinder _ -> misuse
    CaseBinder _ -> misuse
    BindBinder _ -> misuse
    SwitchBinder _ -> misuse
  where
  misuse = rejected (BinderMisuse binderHandle)

-- | Open `constraint =>`: a binder, and the scope its body is built in, which
-- | assumes the constraint.
-- |
-- | The constraint is judged well-formed here, and nothing more. **Whether it
-- | can hold is decided where it is closed**, where the assumption is held as an
-- | obligation; a constraint that cannot hold makes every requirement built
-- | under it fail on the facts of its scope, and the binder must be closed
-- | before the attempt succeeds.
openConstraint :: Handle -> ConstraintView -> Elab { assumption :: Handle, bodyScope :: Handle }
openConstraint scopeHandle view = do
  scope <- resolveScope scopeHandle
  constraint <- constraintIn scope view
  child <- inheritingChild scope (Context.assume scope.context constraint)
  assumption <- issue (BinderObject (AssumedConstraint { constraint, parent: scope.id, body: child.id }))
  holdOpen child.id child.ancestors
  bodyScope <- issue (ScopeObject child)
  pure { assumption, bodyScope }

-- | Close a constraint opened in this scope, over a body built in the body's
-- | scope or in one this scope can use, holding the assumption from here on.
-- |
-- | **The assumption is held as an obligation where it is closed**: an
-- | assignment making it unsatisfiable is refused from then on, and one it
-- | already cannot satisfy is a failure now.
closeConstraint :: Handle -> Handle -> Handle -> Elab Handle
closeConstraint scopeHandle binderHandle bodyHandle = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    AssumedConstraint b -> do
      body <- resolveType bodyHandle
      closedOver scope binderHandle b body.builtIn bodyHandle
      constrained <- kinded scope (XConstrained b.constraint body.type)
      site <- siteOf scope
      _ <- assume site b.constraint
      issueBuilt scope constrained
    ForallBinder _ -> misuse
    LambdaBinder _ -> misuse
    TypeAbsBinder _ -> misuse
    ConstraintAbsBinder _ -> misuse
    LetBinder _ -> misuse
    LetRecGroup _ -> misuse
    JoinBinder _ -> misuse
    CaseBinder _ -> misuse
    BindBinder _ -> misuse
    SwitchBinder _ -> misuse
  where
  misuse = rejected (BinderMisuse binderHandle)

-- | `forall (a : κ). body` applied to a type at `κ`: `body[a := argument]`, both
-- | zonked first, by the capture-avoiding substitution `instantiatedAt` makes,
-- | which waits on a metavariable it cannot see past.
instantiateForall :: Handle -> Handle -> Handle -> Elab Handle
instantiateForall scopeHandle forallHandle argumentHandle = do
  scope <- resolveScope scopeHandle
  whole <- usableIn scope forallHandle
  argument <- usableIn scope argumentHandle
  metas <- currentMetas
  case substitute metas whole.type of
    XForall a kind body ->
      instantiatedAt scope a kind body (substitute metas argument.type) >>= built scope
    _ -> rejected (NotAForall forallHandle)

-- | A catalog entry's scheme at the kinds given: `forall k̄. τ` with `k̄ := κ̄`.
-- |
-- | The entry is read from the catalog by name. The kinds must be quantifiable
-- | and mention only kind variables the scope binds.
-- |
-- | **The scheme is judged in its own scope before the caller's is involved**:
-- | at `Type`, under the kind variables it declares and no type variable, as
-- | `lookupGlobal` judges it. Judged only after substitution, in the caller's
-- | scope, a variable free in the scheme would be taken for one of the caller's
-- | that happens to share its name. A scheme failing that is the host's defect,
-- | the catalog being the host's.
instantiateScheme :: Handle -> Qualified Ident -> P.Array KindView -> Elab Handle
instantiateScheme scopeHandle name kinds = do
  scope <- resolveScope scopeHandle
  instantiated <- schemeAt scope name kinds
  built scope instantiated.type

-- The element a key and a payload make, from types the scope may use.
entryIn :: ScopeObject -> RowKey -> PayloadView -> Elab XRowEntry
entryIn scope key = case _ of
  RegionPayload _ _ -> rejected RegionEntryForbidden
  TypePayload h -> case key of
    SymbolKey _ -> XRowTypeEntry key <$> typeIn h
    TagKey _ -> XRowTypeEntry key <$> typeIn h
    PositionKey _ -> XRowTypeEntry key <$> typeIn h
    _ -> rejected (EntryMismatch key)
  EffectPayload e args -> case key of
    EffectKey e' | e' == e -> XRowEffectEntry e <$> traverse typeIn args
    SymbolKey s -> XRowLabelledEffectEntry s e <$> traverse typeIn args
    _ -> rejected (EntryMismatch key)
  where
  typeIn h = _.type <$> usableIn scope h
