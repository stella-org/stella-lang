-- | The kernel's builders of `case` and its decision tree.
-- |
-- | **A decision tree is built in scopes of its own.** Opening a `case` gives the
-- | scope its tree is built in, and the occurrences of its scrutinees; opening a
-- | `bind` or a switch gives the scopes below it. A tree node is built only in
-- | such a scope, and an occurrence is read only in the tree of the `case` it
-- | belongs to, under the branch that established it — a constructor's fields
-- | under that constructor's branch, a variant's payload under its key's — as
-- | the occurrence typing of the Core type checker has it.
-- |
-- | **What an occurrence stands at is the host's to say**, read off what it was
-- | reached from: a scrutinee at what it is claimed at, a constructor's field at
-- | the field of the data type's declaration instantiated at the occurrence's
-- | type, a record's field and a variant's payload at the element of the row. A
-- | synthesizer is given occurrences and never states one, so it cannot project
-- | what a branch has not established.
-- |
-- | A tree is claimed at nothing; it carries the type the first leaf it reaches
-- | is claimed at, which is what a `case` without a written result type is
-- | claimed at. That every leaf agrees is the Core type checker's.
module Stella.Compiler.Elaborate.Kernel.Builder.DecisionTree
  ( openCase
  , closeCase
  , leaf
  , guard
  , openBind
  , closeBind
  , recordField
  , openSwitchCtor
  , openSwitchLit
  , openSwitchKey
  , closeSwitch
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Kernel.Builder.Common (Shape(..), appliedShape, caseRoot, closedOver, closedOverParts, instantiateConstructorFields, issueTerm, issueTree, rejected, recordShape, rowAt, treeChild, treeOfCase, treeScopeOf, usableIn, usableOccurrenceIn, usableTermIn, usableTreeIn, variantShape)
import Stella.Compiler.Elaborate.Environment.Catalog (EntrySort(..), lookupEntry)
import Stella.Compiler.Elaborate.Environment.Constructors (ConstructorShape, lookupConstructor)
import Stella.Compiler.Elaborate.CorePlus.Context (bindVar)
import Stella.Compiler.Elaborate.Vocabulary.Diagnostic (BuildError(..), Defect(..))
import Stella.Compiler.Elaborate.Kernel.Elab (Elab, askEnv, break, currentMetas, freshIdent, holdOpen, issue, postpone, resolveBinder, resolveScope)
import Stella.Compiler.Elaborate.Vocabulary.Handle (BinderObject(..), Handle, HandleObject(..), ScopeId, ScopeObject, SwitchBranches(..))
import Stella.Compiler.Elaborate.CorePlus.Kind (XKind(..))
import Stella.Compiler.Elaborate.Mechanism.Kinding (KindEvidence(..))
import Stella.Compiler.Elaborate.CorePlus.Row (rebuild, xnf)
import Stella.Compiler.Elaborate.CorePlus.Term (XDecisionTree(..), XExpr(..))
import Stella.Compiler.Elaborate.CorePlus.Type (XType(..))
import Stella.Compiler.Elaborate.Mechanism.Unify (substitute)
import Stella.Compiler.TypedCore (Ident, Literal, Occurrence(..), Qualified, RowKey)
import Stella.Compiler.TypedCore.Prim (variantTy)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl, for_)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))

-- | Open `case (ē) of`: a binder, an occurrence for each scrutinee, at what it
-- | is claimed at, and the scope the decision tree is built in. The scrutinees
-- | are terms this scope may use.
openCase :: Handle -> P.Array Handle -> Elab { binder :: Handle, scrutinees :: P.Array Handle, treeScope :: Handle }
openCase scopeHandle scrutineeHandles = do
  scope <- resolveScope scopeHandle
  scrutinees <- traverse (usableTermIn scope) scrutineeHandles
  root <- caseRoot scope
  binder <- issue (BinderObject (CaseBinder { scrutinees: map _.term scrutinees, parent: scope.id, body: root.id }))
  holdOpen root.id root.ancestors
  occurrences <- traverse
    (\(Tuple i s) -> issueOccurrence root.id root (OccScrutinee i) s.claimed)
    (Array.mapWithIndex Tuple scrutinees)
  treeScope <- issue (ScopeObject root)
  pure { binder, scrutinees: occurrences, treeScope }

-- | Close a `case` opened in this scope over a tree built in its tree's scope,
-- | claimed at the result type given, or else at what the first leaf the tree
-- | reaches is claimed at. A tree that reaches no leaf needs the type given.
closeCase :: Handle -> Handle -> Maybe Handle -> Handle -> Elab Handle
closeCase scopeHandle binderHandle resultHandle treeHandle = do
  scope <- resolveScope scopeHandle
  resolveBinder binderHandle >>= case _ of
    CaseBinder b -> do
      tree <- treeOfCase b.body treeHandle
      closedOver scope binderHandle b tree.builtIn treeHandle
      claimed <- case resultHandle, tree.inferred of
        Just handle, _ -> do
          result <- usableIn scope handle
          case result.kind of
            ExactKind XKType -> pure result.type
            _ -> rejected (NotAType handle)
        Nothing, Just inferred -> pure inferred
        Nothing, Nothing -> rejected (NoLeaf treeHandle)
      issueTerm scope (ECase unit b.scrutinees tree.tree) claimed
    ForallBinder _ -> misuse
    AssumedConstraint _ -> misuse
    LambdaBinder _ -> misuse
    TypeAbsBinder _ -> misuse
    ConstraintAbsBinder _ -> misuse
    LetBinder _ -> misuse
    LetRecGroup _ -> misuse
    JoinBinder _ -> misuse
    BindBinder _ -> misuse
    SwitchBinder _ -> misuse
    HandleBinder _ -> misuse
    RegionBinder _ -> misuse
  where
  misuse = rejected (BinderMisuse binderHandle)

-- | `leaf e`, reaching what `e` is claimed at.
leaf :: Handle -> Handle -> Elab Handle
leaf scopeHandle termHandle = do
  { scope, caseId } <- treeScopeOf scopeHandle
  term <- usableTermIn scope termHandle
  issueTree scope caseId (XLeaf term.term) (Just term.claimed)

-- | `guard e dt1 dt2`, reaching what the first of the two that reaches a leaf
-- | does. What `e` is claimed at is the Core type checker's.
guard :: Handle -> Handle -> Handle -> Handle -> Elab Handle
guard scopeHandle conditionHandle thenHandle elseHandle = do
  { scope, caseId } <- treeScopeOf scopeHandle
  condition <- usableTermIn scope conditionHandle
  consequent <- usableTreeIn scope caseId thenHandle
  alternative <- usableTreeIn scope caseId elseHandle
  issueTree scope caseId (XGuard condition.term consequent.tree alternative.tree) (orElse consequent.inferred alternative.inferred)

-- | Open `bind x = o in`: a binder, the variable it binds as a term built in the
-- | body's scope, at what the occurrence stands at, and that scope.
openBind :: Handle -> Handle -> P.String -> Elab { binder :: Handle, variable :: Handle, bodyScope :: Handle }
openBind scopeHandle occurrenceHandle hint = do
  { scope } <- treeScopeOf scopeHandle
  occurrence <- usableOccurrenceIn scope occurrenceHandle
  name <- freshIdent (Map.keys scope.context.vars) hint
  child <- treeChild scope (bindVar scope.context name occurrence.type)
  binder <- issue (BinderObject (BindBinder { name, occurrence: occurrence.path, parent: scope.id, body: child.id }))
  holdOpen child.id child.ancestors
  variable <- issueTerm child (EVar unit name) occurrence.type
  bodyScope <- issue (ScopeObject child)
  pure { binder, variable, bodyScope }

-- | Close a `bind` opened in this scope over a tree visible under it.
closeBind :: Handle -> Handle -> Handle -> Elab Handle
closeBind scopeHandle binderHandle treeHandle = do
  { scope, caseId } <- treeScopeOf scopeHandle
  resolveBinder binderHandle >>= case _ of
    BindBinder b -> do
      tree <- treeOfCase caseId treeHandle
      closedOver scope binderHandle b tree.builtIn treeHandle
      issueTree scope caseId (XBind b.name b.occurrence tree.tree) tree.inferred
    ForallBinder _ -> misuse
    AssumedConstraint _ -> misuse
    LambdaBinder _ -> misuse
    TypeAbsBinder _ -> misuse
    ConstraintAbsBinder _ -> misuse
    LetBinder _ -> misuse
    LetRecGroup _ -> misuse
    JoinBinder _ -> misuse
    CaseBinder _ -> misuse
    SwitchBinder _ -> misuse
    HandleBinder _ -> misuse
    RegionBinder _ -> misuse
  where
  misuse = rejected (BinderMisuse binderHandle)

-- | `o . k`, the element of a record at a key, which needs no dispatch: at the
-- | payload the record's row carries at `k`.
-- |
-- | Where the row does not carry `k` and a flexible tail could, the tails are
-- | waited on; a rigid tail says nothing of what it carries, so a key absent
-- | from the rest is a misuse.
recordField :: Handle -> Handle -> RowKey -> Elab Handle
recordField scopeHandle occurrenceHandle key = do
  { scope } <- treeScopeOf scopeHandle
  occurrence <- usableOccurrenceIn scope occurrenceHandle
  metas <- currentMetas
  row <- case recordShape metas occurrence.type of
    Seen row -> pure row
    Blocked ms -> postpone ms
    Otherwise -> rejected (NotARecord occurrenceHandle)
  ty <- elementAt (NotARecord occurrenceHandle) occurrenceHandle row key
  issueOccurrence occurrence.case scope (OccRecordField occurrence.path key) ty

-- | Open `switchCtor o { C̄ }`, with a default or without: a binder, each
-- | branch's scope with the occurrences of its constructor's fields, and the
-- | default's scope.
-- |
-- | The constructors must be distinct and build one data type, the one the
-- | occurrence stands at. A field stands at the declaration's field
-- | instantiated at the kinds and the arguments of that type. Whether the
-- | constructors exhaust it, and whether it is a data type rather than an
-- | intrinsic one, are the Core type checker's.
openSwitchCtor
  :: Handle
  -> Handle
  -> P.Array (Qualified Ident)
  -> P.Boolean
  -> Elab
       { binder :: Handle
       , branches :: P.Array { scope :: Handle, fields :: P.Array Handle }
       , fallback :: Maybe Handle
       }
openSwitchCtor scopeHandle occurrenceHandle ctors withDefault = do
  { scope } <- treeScopeOf scopeHandle
  occurrence <- usableOccurrenceIn scope occurrenceHandle
  distinct occurrenceHandle ctors
  shapes <- traverse constructorShape ctors
  fieldTypes <- case Array.head shapes of
    Nothing -> pure []
    Just first -> do
      for_ (Array.zip ctors shapes) \(Tuple ctor shape) ->
        when (shape.owner /= first.owner) (rejected (NotAConstructorOf first.owner ctor))
      metas <- currentMetas
      applied <- case appliedShape metas first.owner (map _.kind first.params) occurrence.type of
        Seen applied -> pure applied
        Blocked ms -> postpone ms
        Otherwise -> rejected (NotOfDataType occurrenceHandle)
      traverse (\shape -> instantiateConstructorFields scope shape applied.kinds applied.args) shapes
  hub <- treeChild scope scope.context
  branchScopes <- traverse (\_ -> treeChild hub scope.context) ctors
  fallbackScope <- if withDefault then Just <$> treeChild hub scope.context else pure Nothing
  binder <- issue
    ( BinderObject
        ( SwitchBinder
            { occurrence: occurrence.path
            , branches: CtorBranches (Array.zipWith (\ctor s -> { ctor, scope: s.id }) ctors branchScopes)
            , fallback: map _.id fallbackScope
            , parent: scope.id
            , body: hub.id
            }
        )
    )
  holdOpen hub.id hub.ancestors
  branches <- traverse
    ( \(Tuple (Tuple ctor fields) branch) -> do
        occurrences <- traverse
          (\(Tuple j ty) -> issueOccurrence occurrence.case branch (OccField occurrence.path ctor j) ty)
          (Array.mapWithIndex Tuple fields)
        branchHandle <- issue (ScopeObject branch)
        pure { scope: branchHandle, fields: occurrences }
    )
    (Array.zip (Array.zip ctors fieldTypes) branchScopes)
  fallback <- traverse (issue <<< ScopeObject) fallbackScope
  pure { binder, branches, fallback }

-- | Open `switchLit o { c̄ } default`: a binder, each branch's scope, and the
-- | default's, which a switch on literals always has, literals being too many to
-- | exhaust. The literals must be distinct; that they are of the occurrence's
-- | type is the Core type checker's.
openSwitchLit
  :: Handle
  -> Handle
  -> P.Array Literal
  -> Elab { binder :: Handle, branches :: P.Array Handle, fallback :: Handle }
openSwitchLit scopeHandle occurrenceHandle lits = do
  { scope } <- treeScopeOf scopeHandle
  occurrence <- usableOccurrenceIn scope occurrenceHandle
  distinct occurrenceHandle lits
  hub <- treeChild scope scope.context
  branchScopes <- traverse (\_ -> treeChild hub scope.context) lits
  fallbackScope <- treeChild hub scope.context
  binder <- issue
    ( BinderObject
        ( SwitchBinder
            { occurrence: occurrence.path
            , branches: LitBranches (Array.zipWith (\lit s -> { lit, scope: s.id }) lits branchScopes)
            , fallback: Just fallbackScope.id
            , parent: scope.id
            , body: hub.id
            }
        )
    )
  holdOpen hub.id hub.ancestors
  branches <- traverse (issue <<< ScopeObject) branchScopes
  fallback <- issue (ScopeObject fallbackScope)
  pure { binder, branches, fallback }

-- | Open `switchKey o { k̄ }`, with a default or without: a binder, each branch's
-- | scope with the occurrence of its key's payload, and the default's scope with
-- | the occurrence as the residual variant.
-- |
-- | The keys must be distinct, and each one the variant's row carries with a
-- | type as its payload; where the row does not carry one and a flexible tail
-- | could, the tails are waited on. The residual is the row with the keys taken
-- | out of its known part and its tails kept, which is not waited on. Whether
-- | the keys exhaust the row is the Core type checker's.
openSwitchKey
  :: Handle
  -> Handle
  -> P.Array RowKey
  -> P.Boolean
  -> Elab
       { binder :: Handle
       , branches :: P.Array { scope :: Handle, payload :: Handle }
       , fallback :: Maybe { scope :: Handle, residual :: Handle }
       }
openSwitchKey scopeHandle occurrenceHandle keys withDefault = do
  { scope } <- treeScopeOf scopeHandle
  occurrence <- usableOccurrenceIn scope occurrenceHandle
  distinct occurrenceHandle keys
  metas <- currentMetas
  row <- case variantShape metas occurrence.type of
    Seen row -> pure row
    Blocked ms -> postpone ms
    Otherwise -> rejected (NotAVariant occurrenceHandle)
  payloads <- traverse (elementAt (NotAVariant occurrenceHandle) occurrenceHandle row) keys
  hub <- treeChild scope scope.context
  branchScopes <- traverse (\_ -> treeChild hub scope.context) keys
  fallbackScope <- if withDefault then Just <$> treeChild hub scope.context else pure Nothing
  binder <- issue
    ( BinderObject
        ( SwitchBinder
            { occurrence: occurrence.path
            , branches: KeyBranches (Array.zipWith (\key s -> { key, scope: s.id }) keys branchScopes)
            , fallback: map _.id fallbackScope
            , parent: scope.id
            , body: hub.id
            }
        )
    )
  holdOpen hub.id hub.ancestors
  branches <- traverse
    ( \(Tuple (Tuple key ty) branch) -> do
        payload <- issueOccurrence occurrence.case branch (OccVariantPayload occurrence.path key) ty
        branchHandle <- issue (ScopeObject branch)
        pure { scope: branchHandle, payload }
    )
    (Array.zip (Array.zip keys payloads) branchScopes)
  fallback <- for fallbackScope \s -> do
    residual <- residualOf occurrenceHandle row keys
    residualHandle <- issueOccurrence occurrence.case s occurrence.path residual
    scopeHandle' <- issue (ScopeObject s)
    pure { scope: scopeHandle', residual: residualHandle }
  pure { binder, branches, fallback }

-- | Close a switch opened in this scope with a tree for each branch, in the
-- | order it was opened with, each visible under its own branch, and a tree for
-- | the default where it was opened with one. What it reaches is what the first
-- | branch reaching a leaf reaches, and otherwise the default.
closeSwitch :: Handle -> Handle -> P.Array Handle -> Maybe Handle -> Elab Handle
closeSwitch scopeHandle binderHandle treeHandles fallbackHandle = do
  { scope, caseId } <- treeScopeOf scopeHandle
  resolveBinder binderHandle >>= case _ of
    SwitchBinder b -> do
      let
        scopes = branchScopes b.branches
      when (Array.length treeHandles /= Array.length scopes)
        (rejected (BranchCount binderHandle (Array.length scopes) (Array.length treeHandles)))
      trees <- traverse (treeOfCase caseId) treeHandles
      fallback <- case b.fallback, fallbackHandle of
        Just s, Just h -> treeOfCase caseId h <#> \t -> Just { scope: s, handle: h, tree: t }
        Nothing, Nothing -> pure Nothing
        _, _ -> rejected (DefaultMismatch binderHandle)
      closedOverParts scope binderHandle b
        ( Array.zipWith (\s (Tuple h t) -> { within: s, builtIn: t.builtIn, handle: h }) scopes (Array.zip treeHandles trees)
            <> Array.fromFoldable (map (\f -> { within: f.scope, builtIn: f.tree.builtIn, handle: f.handle }) fallback)
        )
      let
        subtrees = map _.tree trees
        fallbackTree = map (_.tree.tree) fallback
        inferred = orElse (foldl orElse Nothing (map _.inferred trees)) (fallback >>= _.tree.inferred)
      node <- case b.branches of
        CtorBranches bs ->
          pure (XSwitchCtor b.occurrence (Array.zipWith (\br t -> { ctor: br.ctor, tree: t }) bs subtrees) fallbackTree)
        KeyBranches bs ->
          pure (XSwitchKey b.occurrence (Array.zipWith (\br t -> { key: br.key, tree: t }) bs subtrees) fallbackTree)
        LitBranches bs -> case fallbackTree of
          Just t0 -> pure (XSwitchLit b.occurrence (Array.zipWith (\br t -> { lit: br.lit, tree: t }) bs subtrees) t0)
          Nothing -> rejected (DefaultMismatch binderHandle)
      issueTree scope caseId node inferred
    ForallBinder _ -> misuse
    AssumedConstraint _ -> misuse
    LambdaBinder _ -> misuse
    TypeAbsBinder _ -> misuse
    ConstraintAbsBinder _ -> misuse
    LetBinder _ -> misuse
    LetRecGroup _ -> misuse
    JoinBinder _ -> misuse
    CaseBinder _ -> misuse
    BindBinder _ -> misuse
    HandleBinder _ -> misuse
    RegionBinder _ -> misuse
  where
  misuse :: forall a. Elab a
  misuse = rejected (BinderMisuse binderHandle)

  branchScopes = case _ of
    CtorBranches bs -> map _.scope bs
    LitBranches bs -> map _.scope bs
    KeyBranches bs -> map _.scope bs

-- An occurrence of the `case` named, established in the scope given.
issueOccurrence :: ScopeId -> ScopeObject -> Occurrence -> XType -> Elab Handle
issueOccurrence c scope path ty = do
  metas <- currentMetas
  issue (OccurrenceObject { path, type: substitute metas ty, case: c, builtIn: Just scope.id })

-- The constructor a switch names: in the table, or a misuse. A name the catalog
-- calls a constructor and the table lacks is the host's own inconsistency.
constructorShape :: Qualified Ident -> Elab ConstructorShape
constructorShape name = do
  env <- askEnv
  case lookupConstructor env.session.constructors name of
    Just shape -> pure shape
    Nothing -> case lookupEntry env.session.catalog name of
      Just entry | entry.sort == ConstructorEntry -> break (ConstructorTableMismatch name)
      _ -> rejected (UnknownConstructor name)

-- The type a row carries at a key, by `rowAt`.
elementAt :: BuildError -> Handle -> XType -> RowKey -> Elab XType
elementAt notARow occurrenceHandle row key = _.payload <$> rowAt notARow occurrenceHandle row key

-- `Variant r'`, where `r'` is the row with the keys taken out of its known part
-- and its tails kept.
residualOf :: Handle -> XType -> P.Array RowKey -> Elab XType
residualOf occurrenceHandle row keys = do
  metas <- currentMetas
  case xnf (substitute metas row) of
    Left _ -> rejected (NotAVariant occurrenceHandle)
    Right n ->
      pure (XApp (XCon variantTy []) (rebuild (n { known = foldl (flip Map.delete) n.known keys })))

-- Branch labels given twice are a misuse.
distinct :: forall a. Eq a => Handle -> P.Array a -> Elab Unit
distinct handle labels =
  when (Array.length (Array.nubEq labels) /= Array.length labels) (rejected (DuplicateBranch handle))

-- The first of the two that is there.
orElse :: forall a. Maybe a -> Maybe a -> Maybe a
orElse first second = case first of
  Just _ -> first
  Nothing -> second
