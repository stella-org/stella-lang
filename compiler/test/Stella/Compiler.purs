module Test.Stella.Compiler where

import Prelude

import Effect (Effect)
import Test.Stella.Compiler.TypedCore as TypedCore
import Test.Stella.Compiler.Primitive as Primitive
import Test.Stella.Compiler.Interface as Interface
import Test.Stella.Compiler.Bytecode.Effects as BytecodeEffects
import Test.Stella.Compiler.Bytecode.Lower as BytecodeLower
import Test.Stella.Compiler.Bytecode.Serialize as BytecodeSerialize
import Test.Stella.Compiler.MiddleEnd.Regression as MidRegression
import Test.Stella.Compiler.MiddleEnd.Translate as MidTranslate
import Test.Stella.Compiler.MiddleEnd.Effects as MidEffects
import Test.Stella.Compiler.MiddleEnd.Verify as MidVerify
import Test.Stella.Compiler.TypedCore.Annotation as Annotation
import Test.Stella.Compiler.TypedCore.Check as Check
import Test.Stella.Compiler.TypedCore.Declare as Declare
import Test.Stella.Compiler.TypedCore.Domain as Domain
import Test.Stella.Compiler.TypedCore.Kinding as Kinding
import Test.Stella.Compiler.TypedCore.Row as Row
import Test.Stella.Compiler.Elaborate.Catalog as ElaborateCatalog
import Test.Stella.Compiler.Elaborate.Context as ElaborateContext
import Test.Stella.Compiler.Elaborate.Elab as ElaborateElab
import Test.Stella.Compiler.Elaborate.Handle as ElaborateHandle
import Test.Stella.Compiler.Elaborate.Kinding as ElaborateKinding
import Test.Stella.Compiler.Elaborate.Loop as ElaborateLoop
import Test.Stella.Compiler.Elaborate.Obligation as ElaborateObligation
import Test.Stella.Compiler.Elaborate.Build as ElaborateBuild
import Test.Stella.Compiler.Elaborate.Solve as ElaborateSolve
import Test.Stella.Compiler.Elaborate.BuildTerm as ElaborateBuildTerm
import Test.Stella.Compiler.Elaborate.Binders as ElaborateBinders
import Test.Stella.Compiler.Elaborate.Joins as ElaborateJoins
import Test.Stella.Compiler.Elaborate.Trees as ElaborateTrees
import Test.Stella.Compiler.Elaborate.Records as ElaborateRecords
import Test.Stella.Compiler.Elaborate.Handlers as ElaborateHandlers
import Test.Stella.Compiler.Elaborate.Coverage as ElaborateCoverage
import Test.Stella.Compiler.Elaborate.KernelVertical as ElaborateKernelVertical
import Test.Stella.Compiler.Elaborate.Reports as ElaborateReports
import Test.Stella.Compiler.Elaborate.Conversations as ElaborateConversations
import Test.Stella.Compiler.Elaborate.Observe as ElaborateObserve
import Test.Stella.Compiler.Elaborate.Run as ElaborateRun
import Test.Stella.Compiler.Elaborate.Scheduler as ElaborateScheduler
import Test.Stella.Compiler.Elaborate.Term as ElaborateTerm
import Test.Stella.Compiler.Elaborate.TermMeta as ElaborateTermMeta
import Test.Stella.Compiler.Elaborate.Vertical as ElaborateVertical
import Test.Stella.Compiler.Elaborate.Unify as Unify
import Test.Stella.Compiler.TypedCore.RowProperties as RowProperties
import Test.Stella.Compiler.TypedCore.EffectSlice as EffectSlice
import Test.Stella.Compiler.TypedCore.HandlerSlice as HandlerSlice
import Test.Stella.Compiler.TypedCore.Reference as TypedCoreReference
import Test.Stella.Compiler.TypedCore.VerticalSlice as VerticalSlice
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  TypedCore.spec
  Row.spec
  Kinding.spec
  Declare.spec
  Domain.spec
  Check.spec
  Annotation.spec
  MidTranslate.spec
  MidRegression.spec
  MidVerify.spec
  MidEffects.spec
  Primitive.spec
  BytecodeLower.spec
  BytecodeEffects.spec
  BytecodeSerialize.spec
  Interface.spec
  VerticalSlice.spec
  TypedCoreReference.spec
  EffectSlice.spec
  HandlerSlice.spec
  RowProperties.spec
  Unify.spec
  ElaborateContext.spec
  ElaborateObligation.spec
  ElaborateScheduler.spec
  ElaborateElab.spec
  ElaborateRun.spec
  ElaborateLoop.spec
  ElaborateTerm.spec
  ElaborateTermMeta.spec
  ElaborateVertical.spec
  ElaborateCatalog.spec
  ElaborateHandle.spec
  ElaborateKinding.spec
  ElaborateObserve.spec
  ElaborateBuild.spec
  ElaborateSolve.spec
  ElaborateBuildTerm.spec
  ElaborateBinders.spec
  ElaborateJoins.spec
  ElaborateTrees.spec
  ElaborateRecords.spec
  ElaborateHandlers.spec
  ElaborateCoverage.spec
  ElaborateKernelVertical.spec
  ElaborateReports.spec
  ElaborateConversations.spec
