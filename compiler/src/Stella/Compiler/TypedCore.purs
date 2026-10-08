-- | Typed Core.
-- |
-- | Core defines the semantics of the language: it makes type abstraction and
-- | application, evidence arguments, record and variant operations, the
-- | decision structure of pattern matching, and effect operations and handlers
-- | explicit. Surface features elaborate into it, and an independent type
-- | checker validates every term elaboration produces.
-- |
-- | This module re-exports the syntax together with the decisions the trusted
-- | core makes over it — row normalization, kinding, type equality, and
-- | entailment — which the specification lists as one trusted set.
-- |
-- | The forms that arise only during reduction — `match θ dt`, `openEffC`, and
-- | `rec_i` — belong to the evaluator and are not produced by elaboration, so
-- | they are absent here.
module Stella.Compiler.TypedCore
  ( module Stella.Compiler.TypedCore.Domain
  , module Stella.Compiler.TypedCore.Name
  , module Stella.Compiler.TypedCore.Kind
  , module Stella.Compiler.TypedCore.Type
  , module Stella.Compiler.TypedCore.Term
  , module Stella.Compiler.TypedCore.Decl
  , module Stella.Compiler.TypedCore.Prim
  , module Stella.Compiler.TypedCore.Signature
  , module Stella.Compiler.TypedCore.Context
  , module Stella.Compiler.TypedCore.Row
  , module Stella.Compiler.TypedCore.Kinding
  , module Stella.Compiler.TypedCore.Check
  , module Stella.Compiler.TypedCore.Declare
  , module Stella.Compiler.TypedCore.Equality
  , module Stella.Compiler.TypedCore.Entailment
  , module Stella.Compiler.TypedCore.Reference
  ) where

-- Re-exporting `Type` and `Constraint` shadows the `Prim` names of those
-- spellings, so `Prim` is imported qualified here as well.
import Prim as P

import Stella.Compiler.TypedCore.Check (CheckError(..), CheckFailure, Env, JoinInfo, Typed, check, envOf, infer, isFunVal, isValueForm, typeOf)
import Stella.Compiler.TypedCore.Context (Context, assume, bindKindVars, bindRegion, bindTyVar, emptyContext, kindVarInScope, lookupRegion, lookupTyVar)
import Stella.Compiler.TypedCore.Declare (CheckedGroup, DeclError(..), DeclFailure, Declared, checkAttributeEntries, checkEffectEntries, checkTyConEntries, collectTypes, declare, declareAnnotated, initialSignature)
import Stella.Compiler.TypedCore.Domain (ScalarString, ScalarValue, codePointOf, compareNumber, sameNumber, scalarString, scalarStringOf, scalarValue, textOf)
import Stella.Compiler.TypedCore.Decl (Attribute, AttributeDecl, Constant(..), CtorDecl, DataDecl, Decl(..), declAnnotation, EffectDecl, Export(..), ForeignDecl, KeywordArgument, KeywordParameter, Module, OpDecl, ValueBinding)
import Stella.Compiler.TypedCore.Entailment (AtomicFacts, DecomposeError(..), addAssumption, decompose, entails, noFacts)
import Stella.Compiler.TypedCore.Equality (constraintEquiv, rowEquiv, typeEquiv)
import Stella.Compiler.TypedCore.Kind (Kind(..), KindScheme, RowElemKind(..), Scheme, kindVarsOf, monoScheme, substituteKind)
import Stella.Compiler.TypedCore.Kinding (KindError(..), Synthesized(..), checkKind, kindOf, producesType, quantifiableKind, rowElemKindOf, wellFormedConstraint, wellFormedKey, wellFormedKind)
import Stella.Compiler.TypedCore.Name (EffName(..), Ident(..), JoinName(..), KindVar(..), ModuleName(..), OpName(..), Qualified(..), RegionName(..), Symbol(..), Tag(..), TyName(..), TyVar(..), qualifier, unqualified)
import Stella.Compiler.TypedCore.Prim (asFunction, booleanTy, charTy, fn, functionTy, intTy, ioTy, litType, numberTy, primModule, primSignature, pureFn, recordTy, stringTy, unitCtor, unitTy, variantTy)
import Stella.Compiler.TypedCore.Reference (globalsOf)
import Stella.Compiler.TypedCore.Row (RowError(..), RowNormalForm, emptyNormalForm, nf)
import Stella.Compiler.TypedCore.Signature (CanonicalClass(..), CtorInfo, EffectInfo, Signature, TyConInfo(..), ValueInfo, effectParamKinds, emptySignature, lookupCtor, lookupEffect, lookupOperation, lookupTyCon, lookupValue, tyConKind)
import Stella.Compiler.TypedCore.Term (Binding, CtorBranch, DecisionTree(..), Expr(..), Handler, Cell, KeyBranch, LitBranch, Literal(..), OpClause(..), Occurrence(..), Param, ReturnClause, exprAnnotation, opClauseBody, opClauseOp, withAnnotation)
import Stella.Compiler.TypedCore.Type (Constraint(..), RowEntry(..), RowKey(..), RowPayload(..), TyBinder, Type(..), TypeScheme, freeRegionNames, rowEntryKey, rowEntryPayload)
