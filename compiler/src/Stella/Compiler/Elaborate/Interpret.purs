-- | Answering a kernel request: the operation it names, run in the attempt
-- | and under the frame the runner has set, its result in the shape the request
-- | is answered in.
-- |
-- | Each part of the kernel has an interpreter of its own, and each matches
-- | every request of its part, so a request added to the vocabulary is answered
-- | before anything compiles.
module Stella.Compiler.Elaborate.Interpret
  ( interpret
  ) where

import Prelude

import Stella.Compiler.Elaborate.Build as Build
import Stella.Compiler.Elaborate.BuildHandler as BuildHandler
import Stella.Compiler.Elaborate.BuildRecord as BuildRecord
import Stella.Compiler.Elaborate.BuildTerm as BuildTerm
import Stella.Compiler.Elaborate.BuildTree as BuildTree
import Stella.Compiler.Elaborate.Diagnostic (Defect(..))
import Stella.Compiler.Elaborate.Elab (Elab, break)
import Stella.Compiler.Elaborate.Observe as Observe
import Stella.Compiler.Elaborate.Report as Report
import Stella.Compiler.Elaborate.Request (BuildRequest(..), HandlerRequest(..), KernelAnswer(..), KernelRequest(..), ObserveRequest(..), RecordRequest(..), ReportRequest(..), SolveRequest(..), TermRequest(..), TreeRequest(..), answersAs)
import Stella.Compiler.Elaborate.Solve as Solve

-- | Answer the request, and hold the answer to the shape `expectedAnswerShape`
-- | gives the request: every answer the host gives, to a script or on the wire,
-- | passes here.
interpret :: KernelRequest -> Elab KernelAnswer
interpret request = do
  answer <- answered request
  if answersAs request answer then pure answer
  else break (AnswerShapeMismatch request answer)

answered :: KernelRequest -> Elab KernelAnswer
answered = case _ of
  BuildRequest request -> build request
  TermRequest request -> term request
  TreeRequest request -> tree request
  RecordRequest request -> record request
  HandlerRequest request -> handler request
  SolveRequest request -> solve request
  ObserveRequest request -> observe request
  ReportRequest request -> report request

build :: BuildRequest -> Elab KernelAnswer
build = case _ of
  RootScope -> HandleAnswer <$> Build.rootScope
  TypeVariable scope name -> HandleAnswer <$> Build.typeVariable scope name
  TypeConstructor scope name kinds -> HandleAnswer <$> Build.typeConstructor scope name kinds
  ApplyType scope f a -> HandleAnswer <$> Build.applyType scope f a
  EmptyRow scope -> HandleAnswer <$> Build.emptyRow scope
  ExtendRow scope key payload rest -> HandleAnswer <$> Build.extendRow scope key payload rest
  UnionRow scope left right -> HandleAnswer <$> Build.unionRow scope left right
  OpenForall scope hint kind -> BinderAnswer <$> Build.openForall scope hint kind
  CloseForall scope binder body -> HandleAnswer <$> Build.closeForall scope binder body
  OpenConstraint scope constraint -> AssumptionAnswer <$> Build.openConstraint scope constraint
  CloseConstraint scope assumption body -> HandleAnswer <$> Build.closeConstraint scope assumption body
  InstantiateForall scope quantified argument -> HandleAnswer <$> Build.instantiateForall scope quantified argument
  InstantiateScheme scope name kinds -> HandleAnswer <$> Build.instantiateScheme scope name kinds

term :: TermRequest -> Elab KernelAnswer
term = case _ of
  LocalVariable scope name -> HandleAnswer <$> BuildTerm.localVariable scope name
  GlobalRef scope name kinds -> HandleAnswer <$> BuildTerm.globalRef scope name kinds
  LiteralTerm scope lit -> HandleAnswer <$> BuildTerm.literal scope lit
  TermApply scope f a -> HandleAnswer <$> BuildTerm.termApply scope f a
  TypeApply scope e t -> HandleAnswer <$> BuildTerm.typeApply scope e t
  ConstraintApply scope e -> HandleAnswer <$> BuildTerm.constraintApply scope e
  OpenLambda scope hint ty -> BinderAnswer <$> BuildTerm.openLambda scope hint ty
  CloseLambda scope binder body row -> HandleAnswer <$> BuildTerm.closeLambda scope binder body row
  OpenTypeAbs scope hint kind -> BinderAnswer <$> BuildTerm.openTypeAbs scope hint kind
  CloseTypeAbs scope binder body -> HandleAnswer <$> BuildTerm.closeTypeAbs scope binder body
  OpenConstraintAbs scope constraint -> ConstraintAbsAnswer <$> BuildTerm.openConstraintAbs scope constraint
  CloseConstraintAbs scope binder body -> HandleAnswer <$> BuildTerm.closeConstraintAbs scope binder body
  OpenLet scope hint value -> BinderAnswer <$> BuildTerm.openLet scope hint value
  CloseLet scope binder body -> HandleAnswer <$> BuildTerm.closeLet scope binder body
  OpenLetRec scope bindings -> LetRecAnswer <$> BuildTerm.openLetRec scope bindings
  CloseLetRec scope binder rhss body -> HandleAnswer <$> BuildTerm.closeLetRec scope binder rhss body
  OpenJoin scope hint params result -> JoinAnswer <$> BuildTerm.openJoin scope hint params result
  CloseJoin scope binder definition body -> HandleAnswer <$> BuildTerm.closeJoin scope binder definition body
  Jump scope join args -> HandleAnswer <$> BuildTerm.jump scope join args

tree :: TreeRequest -> Elab KernelAnswer
tree = case _ of
  OpenCase scope scrutinees -> CaseAnswer <$> BuildTree.openCase scope scrutinees
  CloseCase scope binder result decision -> HandleAnswer <$> BuildTree.closeCase scope binder result decision
  Leaf scope e -> HandleAnswer <$> BuildTree.leaf scope e
  Guard scope condition yes no -> HandleAnswer <$> BuildTree.guard scope condition yes no
  OpenBind scope occurrence hint -> BinderAnswer <$> BuildTree.openBind scope occurrence hint
  CloseBind scope binder decision -> HandleAnswer <$> BuildTree.closeBind scope binder decision
  RecordField scope occurrence key -> HandleAnswer <$> BuildTree.recordField scope occurrence key
  OpenSwitchCtor scope occurrence ctors withDefault -> SwitchCtorAnswer <$> BuildTree.openSwitchCtor scope occurrence ctors withDefault
  OpenSwitchLit scope occurrence lits -> SwitchLitAnswer <$> BuildTree.openSwitchLit scope occurrence lits
  OpenSwitchKey scope occurrence keys withDefault -> SwitchKeyAnswer <$> BuildTree.openSwitchKey scope occurrence keys withDefault
  CloseSwitch scope binder trees fallback -> HandleAnswer <$> BuildTree.closeSwitch scope binder trees fallback

record :: RecordRequest -> Elab KernelAnswer
record = case _ of
  RecordEmpty scope -> HandleAnswer <$> BuildRecord.recordEmpty scope
  RecordExtend scope key value rest -> HandleAnswer <$> BuildRecord.recordExtend scope key value rest
  RecordSelect scope key e -> HandleAnswer <$> BuildRecord.recordSelect scope key e
  RecordRestrict scope key e -> HandleAnswer <$> BuildRecord.recordRestrict scope key e
  RecordUpdate scope key e value -> HandleAnswer <$> BuildRecord.recordUpdate scope key e value
  RecordMerge scope left right -> HandleAnswer <$> BuildRecord.recordMerge scope left right
  VariantInject scope key value -> HandleAnswer <$> BuildRecord.variantInject scope key value
  VariantWeaken scope key payload e -> HandleAnswer <$> BuildRecord.variantWeaken scope key payload e
  VariantAbsurd scope result e -> HandleAnswer <$> BuildRecord.variantAbsurd scope result e
  OpenEff scope row e -> HandleAnswer <$> BuildRecord.openEff scope row e

handler :: HandlerRequest -> Elab KernelAnswer
handler = case _ of
  Perform scope key payload op typeArgs argument -> HandleAnswer <$> BuildHandler.perform scope key payload op typeArgs argument
  OpenHandle scope computation key payload layout answer residual clauses ->
    HandlerAnswer <$> BuildHandler.openHandle scope computation key payload layout answer residual clauses
  CloseHandle scope binder returnBody clauseBodies initials -> HandleAnswer <$> BuildHandler.closeHandle scope binder returnBody clauseBodies initials
  ReadCell scope key -> HandleAnswer <$> BuildHandler.readCell scope key
  WriteCell scope key value -> HandleAnswer <$> BuildHandler.writeCell scope key value

solve :: SolveRequest -> Elab KernelAnswer
solve = case _ of
  FreshMetaType scope kind -> HandleAnswer <$> Solve.freshMetaType scope kind
  IsAssigned meta -> BooleanAnswer <$> Solve.isAssigned meta
  Unify scope left right -> UnitAnswer <$ Solve.unify scope left right
  Entails scope constraint -> BooleanAnswer <$> Solve.entails scope constraint
  Require scope constraint -> UnitAnswer <$ Solve.require scope constraint
  Subgoal scope ty synthesizer -> HandleAnswer <$> Solve.subgoal scope ty synthesizer

observe :: ObserveRequest -> Elab KernelAnswer
observe = case _ of
  GoalType goal -> HandleAnswer <$> Observe.goalType goal
  ViewType ty -> TypeViewAnswer <$> Observe.viewType ty
  Whnf ty -> HandleAnswer <$> Observe.whnf ty
  NormalizeRow row -> RowViewAnswer <$> Observe.normalizeRow row
  KindOf ty -> KindViewAnswer <$> Observe.kindOf ty
  TypeOf e -> HandleAnswer <$> Observe.typeOf e
  LocalContext -> ContextAnswer <$> Observe.localContext
  LocalConstraints -> ConstraintsAnswer <$> Observe.localConstraints
  LookupGlobal name -> DeclAnswer <$> Observe.lookupGlobal name
  DeclsWithAttr attribute -> NamesAnswer <$> Observe.declsWithAttr attribute

report :: ReportRequest -> Elab KernelAnswer
report = case _ of
  Throw message -> Report.throw message
  Warn message -> UnitAnswer <$ Report.warn message
  Postpone metas -> Report.postpone metas
