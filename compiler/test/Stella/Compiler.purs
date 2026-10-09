module Test.Stella.Compiler where

import Prelude

import Effect (Effect)
import Test.Stella.Compiler.TypedCore as TypedCore
import Test.Stella.Compiler.Primitive as Primitive
import Test.Stella.Compiler.Interface as Interface
import Test.Stella.Compiler.Interface.Environment as InterfaceEnvironment
import Test.Stella.Compiler.Elaborate.Imported as ElaborateImported
import Test.Stella.Compiler.Elaborate.Equate as ElaborateEquate
import Test.Stella.Compiler.Elaborate.Fit as ElaborateFit
import Test.Stella.Compiler.Elaborate.Resolve as ElaborateResolve
import Test.Stella.Compiler.Elaborate.SurfaceType as ElaborateSurfaceType
import Test.Stella.Compiler.Elaborate.Group as ElaborateGroup
import Test.Stella.Compiler.Build as Build
import Test.Stella.Compiler.ForeignBoundary as ForeignBoundary
import Test.Stella.Compiler.Interface.FromCore as InterfaceFromCore
import Test.Stella.Compiler.Elaborate.SurfaceModule as ElaborateSurfaceModule
import Test.Stella.Compiler.Macro.Bundle as MacroBundle
import Test.Stella.Compiler.Macro.Check as MacroCheck
import Test.Stella.Compiler.Macro.Expand as MacroExpand
import Test.Stella.Compiler.Macro.Tree as MacroTree
import Test.Stella.Compiler.Interface.File as InterfaceFile
import Test.Stella.Compiler.Interface.Assemble as InterfaceAssemble
import Test.Stella.Compiler.Bytecode.Effects as BytecodeEffects
import Test.Stella.Compiler.Bytecode.Lower as BytecodeLower
import Test.Stella.Compiler.Bytecode.Serialize as BytecodeSerialize
import Test.Stella.Compiler.Fixtures as Fixtures
import Test.Stella.Compiler.MiddleEnd.Regression as MidRegression
import Test.Stella.Compiler.MiddleEnd.Translate as MidTranslate
import Test.Stella.Compiler.MiddleEnd.Effects as MidEffects
import Test.Stella.Compiler.MiddleEnd.Verify as MidVerify
import Test.Stella.Compiler.TypedCore.Annotation as Annotation
import Test.Stella.Compiler.TypedCore.Check as Check
import Test.Stella.Compiler.TypedCore.Declare as Declare
import Test.Stella.Compiler.TypedCore.AttributeCheck as AttributeCheck
import Test.Stella.Compiler.TypedCore.Substitution as Substitution
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
import Test.Stella.Compiler.Elaborate.GuestBundle as ElaborateGuestBundle
import Test.Stella.Compiler.Elaborate.KernelVertical as ElaborateKernelVertical
import Test.Stella.Compiler.CST.Lexer as CSTLexer
import Test.Stella.Compiler.CST.Layout as CSTLayout
import Test.Stella.Compiler.CST.Parser as CSTParser
import Test.Stella.Compiler.CST.Tour as CSTTour
import Test.Stella.Compiler.CST.Check as CSTCheck
import Test.Stella.Compiler.CST.Range as CSTRange
import Test.Stella.Compiler.Resolve.Group as ResolveGroup
import Test.Stella.Compiler.Resolve.Module as ResolveModule
import Test.Stella.Compiler.Resolve.Binder as ResolveBinder
import Test.Stella.Compiler.Resolve.Expr as ResolveExpr
import Test.Stella.Compiler.Resolve.Scope as ResolveScope
import Test.Stella.Compiler.Resolve.Type as ResolveType
import Test.Stella.Compiler.Elaborate.Reports as ElaborateReports
import Test.Stella.Compiler.Elaborate.Conversations as ElaborateConversations
import Test.Stella.Compiler.Elaborate.Facade as ElaborateFacade
import Test.Stella.Compiler.Elaborate.Traces as ElaborateTraces
import Test.Stella.Compiler.Elaborate.Synthesis as ElaborateSynthesis
import Test.Stella.Compiler.Elaborate.SynthesisVertical as ElaborateSynthesisVertical
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
  CSTLexer.spec
  CSTLayout.spec
  CSTParser.spec
  CSTTour.spec
  CSTCheck.spec
  CSTRange.spec
  ResolveGroup.spec
  ResolveScope.spec
  ResolveType.spec
  ResolveBinder.spec
  ResolveExpr.spec
  ResolveModule.spec
  TypedCore.spec
  Row.spec
  Kinding.spec
  Declare.spec
  AttributeCheck.spec
  Substitution.spec
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
  Fixtures.spec
  Interface.spec
  InterfaceEnvironment.spec
  MacroTree.spec
  MacroBundle.spec
  ElaborateImported.spec
  ElaborateEquate.spec
  ElaborateFit.spec
  ElaborateResolve.spec
  ElaborateSurfaceType.spec
  ElaborateGroup.spec
  Build.spec
  ForeignBoundary.spec
  InterfaceFromCore.spec
  ElaborateSurfaceModule.spec
  MacroCheck.spec
  MacroExpand.spec
  InterfaceFile.spec
  InterfaceAssemble.spec
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
  ElaborateGuestBundle.spec
  ElaborateKernelVertical.spec
  ElaborateReports.spec
  ElaborateConversations.spec
  ElaborateFacade.spec
  ElaborateTraces.spec
  ElaborateSynthesis.spec
  ElaborateSynthesisVertical.spec
