-- | `Stella.Elab`: what a guest synthesizer running on Steam is written against,
-- | as the compiler and a host refer to it. The module is written in source
-- | (`stella-packages/compiler-lib/src/Stella/Elab.stel`), and the compiler
-- | carries what a build of it writes ([Compiled](../../Macro/Compiled.purs)).
-- |
-- | A guest asks the host through one effect operation, `command`, and the values
-- | it sends and receives are data types of the module. They mirror the kernel's
-- | vocabulary constructor for constructor, so that a request a guest builds is the
-- | request a host script makes ([Request](../Vocabulary/Request.purs)).
-- |
-- | **A guest is written against typed operations, not against `command`.** Each
-- | kernel operation has a function of the host facade's name, taking the request's
-- | fields in order and giving back what its answer carries; `transact` runs a
-- | candidate, and `synthesizer` makes a policy into what an invocation calls.
-- | The operations and `transact` run at `( Abort, Breach, Kernel )`, and so does a
-- | policy written with them; `synthesizer` narrows it to `( Kernel )`, the one
-- | effect the root boundary answers.
-- |
-- | **`Abort` is how a candidate fails, and `Breach` how a host answers outside its
-- | contract.** An operation answered `CandidateFailed` raises `Abort`, which the
-- | innermost `transact` handles; any other answer it does not expect raises
-- | `Breach`, which `transact` leaves in its residual row for `synthesizer`
-- | ([Elaborator API](../../../../../../docs/technical-references/02-Surface-Language/03-Elaborator-API.md)).
-- |
-- | **Which request and which answer each operation stands for is written here
-- | too**, as the protocol a host conforms to: the operations' types are read
-- | off the module's interface, and the module is held to them.
module Stella.Compiler.Elaborate.Protocol.Guest
  ( elabModule
  , handleTy
  , nameTy
  , kernelEffect
  , commandOp
  , abortEffect
  , failedOp
  , breachEffect
  , breachedOp
  , elabRow
  , synthesizerType
  , guestCommandTy
  , guestAnswerTy
  , Operation
  , operations
  , operationType
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either(..), note)
import Data.Foldable (foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Stella.Compiler.Interface.Module (ModuleInterface, TypeSort(..))
import Stella.Compiler.TypedCore (EffName(..), Ident(..), Kind(..), ModuleName(..), OpName(..), Qualified(..), RowEntry(..), TyName(..), TyVar(..), Type(..))
import Stella.Compiler.TypedCore.Prim (fn, pureFn, unitTy)

elabModule :: ModuleName
elabModule = ModuleName "Stella.Elab"

-- | `Stella.Elab.Handle`, an opaque foreign type: a host token, which nothing a
-- | guest writes can take apart.
handleTy :: Qualified TyName
handleTy = Qualified elabModule (TyName "Handle")

-- | A qualified name, as a guest holds one.
nameTy :: Qualified TyName
nameTy = Qualified elabModule (TyName "Name")

guestCommandTy :: Qualified TyName
guestCommandTy = Qualified elabModule (TyName "GuestCommand")

guestAnswerTy :: Qualified TyName
guestAnswerTy = Qualified elabModule (TyName "GuestAnswer")

kernelEffect :: Qualified EffName
kernelEffect = Qualified elabModule (EffName "Kernel")

commandOp :: OpName
commandOp = OpName "command"

-- | `Stella.Elab.Abort`: a candidate failed, and the innermost `transact` is to
-- | answer `Nothing`.
abortEffect :: Qualified EffName
abortEffect = Qualified elabModule (EffName "Abort")

failedOp :: OpName
failedOp = OpName "failed"

-- | `Stella.Elab.Breach`: the host answered as its contract says it never does.
-- | Only `synthesizer` handles it.
breachEffect :: Qualified EffName
breachEffect = Qualified elabModule (EffName "Breach")

breachedOp :: OpName
breachedOp = OpName "breached"

-- | `( Abort, Breach, Kernel )`, the row every operation of the facade runs at.
elabRow :: Type
elabRow = effectRow [ abortEffect, breachEffect, kernelEffect ]

-- | The type a synthesizer is invoked at: from the handle of its goal to the
-- | handle of the term it fills the goal with, answering `Kernel` alone.
synthesizerType :: Type
synthesizerType = fn handle (effectRow [ kernelEffect ]) handle

-- The facade ---------------------------------------------------------------------------------

-- | One kernel operation as a guest calls it: its name, the request it makes by its
-- | family and constructor, and the constructor of the `KernelAnswer` it takes back.
-- | `throw` and `postpone` take none back: the host ends the attempt.
type Operation =
  { name :: P.String
  , family :: P.String
  , request :: P.String
  , answer :: Maybe P.String
  }

-- | Every kernel operation, in the order the requests are declared.
operations :: P.Array Operation
operations =
  [ op "rootScope" "BuildRequest" "RootScope" handleAnswer
  , op "typeVariable" "BuildRequest" "TypeVariable" handleAnswer
  , op "typeConstructor" "BuildRequest" "TypeConstructor" handleAnswer
  , op "applyType" "BuildRequest" "ApplyType" handleAnswer
  , op "emptyRow" "BuildRequest" "EmptyRow" handleAnswer
  , op "extendRow" "BuildRequest" "ExtendRow" handleAnswer
  , op "unionRow" "BuildRequest" "UnionRow" handleAnswer
  , op "openForall" "BuildRequest" "OpenForall" (Just "BinderAnswer")
  , op "closeForall" "BuildRequest" "CloseForall" handleAnswer
  , op "openConstraint" "BuildRequest" "OpenConstraint" (Just "AssumptionAnswer")
  , op "closeConstraint" "BuildRequest" "CloseConstraint" handleAnswer
  , op "instantiateForall" "BuildRequest" "InstantiateForall" handleAnswer
  , op "instantiateScheme" "BuildRequest" "InstantiateScheme" handleAnswer
  , op "localVariable" "TermRequest" "LocalVariable" handleAnswer
  , op "globalRef" "TermRequest" "GlobalRef" handleAnswer
  , op "literal" "TermRequest" "LiteralTerm" handleAnswer
  , op "termApply" "TermRequest" "TermApply" handleAnswer
  , op "typeApply" "TermRequest" "TypeApply" handleAnswer
  , op "constraintApply" "TermRequest" "ConstraintApply" handleAnswer
  , op "openLambda" "TermRequest" "OpenLambda" (Just "BinderAnswer")
  , op "closeLambda" "TermRequest" "CloseLambda" handleAnswer
  , op "openTypeAbs" "TermRequest" "OpenTypeAbs" (Just "BinderAnswer")
  , op "closeTypeAbs" "TermRequest" "CloseTypeAbs" handleAnswer
  , op "openConstraintAbs" "TermRequest" "OpenConstraintAbs" (Just "ConstraintAbsAnswer")
  , op "closeConstraintAbs" "TermRequest" "CloseConstraintAbs" handleAnswer
  , op "openLet" "TermRequest" "OpenLet" (Just "BinderAnswer")
  , op "closeLet" "TermRequest" "CloseLet" handleAnswer
  , op "openLetRec" "TermRequest" "OpenLetRec" (Just "LetRecAnswer")
  , op "closeLetRec" "TermRequest" "CloseLetRec" handleAnswer
  , op "openJoin" "TermRequest" "OpenJoin" (Just "JoinAnswer")
  , op "closeJoin" "TermRequest" "CloseJoin" handleAnswer
  , op "jump" "TermRequest" "Jump" handleAnswer
  , op "openCase" "TreeRequest" "OpenCase" (Just "CaseAnswer")
  , op "closeCase" "TreeRequest" "CloseCase" handleAnswer
  , op "leaf" "TreeRequest" "Leaf" handleAnswer
  , op "guard" "TreeRequest" "Guard" handleAnswer
  , op "openBind" "TreeRequest" "OpenBind" (Just "BinderAnswer")
  , op "closeBind" "TreeRequest" "CloseBind" handleAnswer
  , op "recordField" "TreeRequest" "RecordField" handleAnswer
  , op "openSwitchCtor" "TreeRequest" "OpenSwitchCtor" (Just "SwitchCtorAnswer")
  , op "openSwitchLit" "TreeRequest" "OpenSwitchLit" (Just "SwitchLitAnswer")
  , op "openSwitchKey" "TreeRequest" "OpenSwitchKey" (Just "SwitchKeyAnswer")
  , op "closeSwitch" "TreeRequest" "CloseSwitch" handleAnswer
  , op "recordEmpty" "RecordRequest" "RecordEmpty" handleAnswer
  , op "recordExtend" "RecordRequest" "RecordExtend" handleAnswer
  , op "recordSelect" "RecordRequest" "RecordSelect" handleAnswer
  , op "recordRestrict" "RecordRequest" "RecordRestrict" handleAnswer
  , op "recordUpdate" "RecordRequest" "RecordUpdate" handleAnswer
  , op "recordMerge" "RecordRequest" "RecordMerge" handleAnswer
  , op "variantInject" "RecordRequest" "VariantInject" handleAnswer
  , op "variantWeaken" "RecordRequest" "VariantWeaken" handleAnswer
  , op "variantAbsurd" "RecordRequest" "VariantAbsurd" handleAnswer
  , op "openEff" "RecordRequest" "OpenEff" handleAnswer
  , op "perform" "HandlerRequest" "Perform" handleAnswer
  , op "openHandle" "HandlerRequest" "OpenHandle" (Just "HandlerAnswer")
  , op "closeHandle" "HandlerRequest" "CloseHandle" handleAnswer
  , op "openRegion" "HandlerRequest" "OpenRegion" (Just "RegionAnswer")
  , op "closeRegion" "HandlerRequest" "CloseRegion" handleAnswer
  , op "readCell" "HandlerRequest" "ReadCell" handleAnswer
  , op "writeCell" "HandlerRequest" "WriteCell" handleAnswer
  , op "freshMetaType" "SolveRequest" "FreshMetaType" handleAnswer
  , op "isAssigned" "SolveRequest" "IsAssigned" (Just "BooleanAnswer")
  , op "unify" "SolveRequest" "Unify" (Just "UnitAnswer")
  , op "entails" "SolveRequest" "Entails" (Just "BooleanAnswer")
  , op "require" "SolveRequest" "Require" (Just "UnitAnswer")
  , op "subgoal" "SolveRequest" "Subgoal" handleAnswer
  , op "goalType" "ObserveRequest" "GoalType" handleAnswer
  , op "viewType" "ObserveRequest" "ViewType" (Just "TypeViewAnswer")
  , op "whnf" "ObserveRequest" "Whnf" handleAnswer
  , op "normalizeRow" "ObserveRequest" "NormalizeRow" (Just "RowViewAnswer")
  , op "kindOf" "ObserveRequest" "KindOf" (Just "KindViewAnswer")
  , op "typeOf" "ObserveRequest" "TypeOf" handleAnswer
  , op "localContext" "ObserveRequest" "LocalContext" (Just "ContextAnswer")
  , op "localConstraints" "ObserveRequest" "LocalConstraints" (Just "ConstraintsAnswer")
  , op "lookupGlobal" "ObserveRequest" "LookupGlobal" (Just "DeclAnswer")
  , op "declsWithAttr" "ObserveRequest" "DeclsWithAttr" (Just "NamesAnswer")
  , op "throw" "ReportRequest" "Throw" Nothing
  , op "warn" "ReportRequest" "Warn" (Just "UnitAnswer")
  , op "postpone" "ReportRequest" "Postpone" Nothing
  ]
  where
  op n family request answer = { name: n, family, request, answer }
  handleAnswer = Just "HandleAnswer"

-- | The type of an operation, read off the interface of `Stella.Elab`: its
-- | request's fields in order, each arrow but the last pure, and the last at
-- | `elabRow`, giving back what its answer carries, or `Unit` for an answer that
-- | carries nothing. An operation of no field takes `Unit`, and `throw` and
-- | `postpone`, answered by none, give back whatever is asked of them. A family,
-- | a request, or an answer the interface does not declare is refused, and so is
-- | an answer carrying more than one value.
operationType :: ModuleInterface -> Operation -> Either P.String Type
operationType i o = do
  parameters <- fieldsOf o.family o.request
  result <- traverse answered o.answer
  pure case result of
    Just r -> arrows parameters r
    Nothing -> TForall anyVar KType (arrows parameters (TVar anyVar))
  where
  answered answer = fieldsOf "KernelAnswer" answer >>= case _ of
    [] -> Right unitType
    [ carried ] -> Right carried
    _ -> Left ("the answer " <> answer <> " carries more than one value")

  arrows parameters result = case Array.unsnoc parameters of
    Just { init, last } -> foldr pureFn (fn last elabRow result) init
    Nothing -> fn unitType elabRow result

  fieldsOf typeName ctorName = do
    entry <- note ("no type " <> typeName) (Map.lookup (TyName typeName) i.declarations.types)
    constructors <- case entry.sort of
      DataType d -> Right d.constructors
      _ -> Left (typeName <> " is no data type")
    _.fields <$> note ("no constructor " <> ctorName <> " of " <> typeName) (Array.find (\c -> c.name == Ident ctorName) constructors)

-- Type shorthands ---------------------------------------------------------------------------

handle :: Type
handle = TCon handleTy []

unitType :: Type
unitType = TCon unitTy []

anyVar :: TyVar
anyVar = TyVar "a"

effectRow :: P.Array (Qualified EffName) -> Type
effectRow = foldr (\e rest -> TRowExtend (RowEffectEntry e []) rest) TRowEmpty
