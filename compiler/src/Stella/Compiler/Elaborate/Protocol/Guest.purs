-- | `Stella.Elab`: what a guest synthesizer running on Steam is written against.
-- |
-- | A guest asks the host through one effect operation, `command`, and the values
-- | it sends and receives are data types of this module. They mirror the kernel's
-- | vocabulary constructor for constructor, so that a request a guest builds is the
-- | request a host script makes ([Request](../Vocabulary/Request.purs)). Only the
-- | control a guest has any use for is exposed: the attempt is finished by the
-- | guest returning, not by a command, and transactions are opened and closed
-- | without the guest ever holding their tokens.
-- |
-- | **Three things come together and are trusted together**: the Core module, the
-- | signature fragment that gives `Handle` its type, and the shape descriptor read
-- | off the module. The bundle belongs to the elaboration profile alone, and
-- | `Handle` is an intrinsic of that profile: neither `Prim` nor the ABI manifest
-- | supplies it, and only `withGuest` puts it in a signature.
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
-- | Both are raised by the operations here and handled by `transact` and
-- | `synthesizer` alone: a policy that performs or handles either itself is out of
-- | contract, and gains nothing by it — the host's transactions and the result it
-- | finishes with are checked where it holds them.
-- |
-- | The module depends on nothing, `Prelude` included, so it has lists and optional
-- | values of its own.
module Stella.Compiler.Elaborate.Protocol.Guest
  ( Bundle
  , bundle
  , guestModule
  , withGuest
  , elabModule
  , handleTy
  , nameTy
  , kernelEffect
  , commandOp
  , abortEffect
  , failedOp
  , breachEffect
  , breachedOp
  , elabRow
  , guestCommandTy
  , guestAnswerTy
  , Operation
  , operations
  , operationType
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either)
import Data.Foldable (foldl, foldr)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..), snd)
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor, describe)
import Stella.Compiler.TypedCore (CanonicalClass(..), DecisionTree(..), Decl(..), EffName(..), Export(..), Expr(..), Ident(..), Kind(..), Module, ModuleName(..), OpClause(..), OpName(..), Occurrence(..), Qualified(..), RowEntry(..), RowKey(..), Signature, Symbol(..), TyName(..), TyConInfo(..), TyVar(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Prim (booleanTy, charTy, fn, intTy, numberTy, pureFn, recordTy, stringTy, unitCtor, unitTy)

-- | The three that are trusted together.
type Bundle =
  { module :: Module Unit
  , withSignature :: Signature -> Signature
  , descriptor :: Descriptor
  }

-- | The bundle, or why the descriptor could not be read off the module — which is a
-- | defect of this file, and what the tests hold it to.
bundle :: Either P.String Bundle
bundle = describe handleTy guestModule <#> \descriptor ->
  { module: guestModule, withSignature: withGuest, descriptor }

elabModule :: ModuleName
elabModule = ModuleName "Stella.Elab"

-- | `Stella.Elab.Handle`, an intrinsic opaque type: a host token, which nothing a
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

-- | A signature with `Stella.Elab.Handle` in it, which is what checking the module,
-- | and a guest over it, needs.
withGuest :: Signature -> Signature
withGuest sig = sig
  { types = Map.insert handleTy (IntrinsicTyCon (monoScheme KType) CanonicalOpaque) sig.types }

-- The module ---------------------------------------------------------------------------

guestModule :: Module Unit
guestModule =
  { annotation: unit
  , name: elabModule
  , imports: []
  , exports:
      map (ExportType <<< TyName) (map _.name types)
        <> map (ExportCtor <<< Ident) (Array.concatMap (map ctorName <<< _.ctors) types)
        <> map ExportEffect [ EffName "Kernel", EffName "Abort", EffName "Breach" ]
        <> map (ExportValue <<< Ident) (map _.name operations <> [ "transact", "synthesizer" ])
  , decls:
      map dataDecl types
        <>
          [ DeclEffect unit
              { name: EffName "Kernel"
              , params: []
              , operations:
                  [ { name: commandOp
                    , tyBinders: []
                    , argument: con "GuestCommand"
                    , resumesWith: con "GuestAnswer"
                    }
                  ]
              , attributes: []
              }
          , escape "Abort" failedOp
          , escape "Breach" breachedOp
          , askDecl
          ]
        <> map operationDecl operations
        <> [ transactDecl, synthesizerDecl ]
  }
  where
  ctorName (Tuple c _) = c

  -- an effect of one operation, `forall a. Unit ->* a`, which never resumes
  escape n op = DeclEffect unit
    { name: EffName n
    , params: []
    , operations:
        [ { name: op
          , tyBinders: [ { name: TyVar "a", kind: KType } ]
          , argument: unitType
          , resumesWith: TVar (TyVar "a")
          }
        ]
    , attributes: []
    }

type DataType = { name :: P.String, params :: P.Array P.String, ctors :: P.Array (Tuple P.String (P.Array Type)) }

dataDecl :: DataType -> Decl Unit
dataDecl d = DeclData unit
  { name: TyName d.name
  , kindVars: []
  , params: map (\p -> { name: TyVar p, kind: KType }) d.params
  , constructors: Array.mapWithIndex
      (\tag (Tuple c fields) -> { name: Ident c, tag, fields })
      d.ctors
  , isNewtype: false
  , attributes: []
  }

-- Type shorthands ------------------------------------------------------------------------

con :: P.String -> Type
con n = TCon (Qualified elabModule (TyName n)) []

handle :: Type
handle = TCon handleTy []

name :: Type
name = con "Name"

string :: Type
string = TCon stringTy []

int :: Type
int = TCon intTy []

number :: Type
number = TCon numberTy []

char :: Type
char = TCon charTy []

boolean :: Type
boolean = TCon booleanTy []

list :: Type -> Type
list = TApp (con "List")

maybe :: Type -> Type
maybe = TApp (con "Maybe")

record :: P.Array (Tuple P.String Type) -> Type
record fields = TApp (TCon recordTy [])
  (foldr (\(Tuple k t) row -> TRowExtend (RowTypeEntry (SymbolKey (Symbol k)) t) row) TRowEmpty fields)

ctor :: P.String -> P.Array Type -> Tuple P.String (P.Array Type)
ctor = Tuple

simple :: P.String -> P.Array (Tuple P.String (P.Array Type)) -> DataType
simple n ctors = { name: n, params: [], ctors }

-- The data types ----------------------------------------------------------------------------

types :: P.Array DataType
types =
  [ { name: "List"
    , params: [ "a" ]
    , ctors: [ ctor "Nil" [], ctor "Cons" [ TVar (TyVar "a"), list (TVar (TyVar "a")) ] ]
    }
  , { name: "Maybe"
    , params: [ "a" ]
    , ctors: [ ctor "Nothing" [], ctor "Just" [ TVar (TyVar "a") ] ]
    }
  , simple "Name" [ ctor "Name" [ string, string ] ]
  , simple "RowElemKind" [ ctor "RowType" [], ctor "RowEffect" [] ]
  , simple "KindView"
      [ ctor "KindType" []
      , ctor "KindEffect" []
      , ctor "KindRow" [ con "RowElemKind" ]
      , ctor "KindFun" [ con "KindView", con "KindView" ]
      , ctor "KindVar" [ string ]
      , ctor "KindAnyRow" []
      ]
  , simple "RowKey"
      [ ctor "SymbolKey" [ string ]
      , ctor "TagKey" [ string ]
      , ctor "PositionKey" [ int ]
      , ctor "EffectKey" [ name ]
      , ctor "RegionKey" []
      ]
  , simple "Literal"
      [ ctor "LitInt" [ int ]
      , ctor "LitNumber" [ number ]
      , ctor "LitString" [ string ]
      , ctor "LitChar" [ char ]
      , ctor "LitBoolean" [ boolean ]
      ]
  , simple "PayloadView"
      [ ctor "TypePayload" [ handle ]
      , ctor "EffectPayload" [ name, list handle ]
      , ctor "RegionPayload" [ handle, handle ]
      ]
  , simple "ConstraintView"
      [ ctor "LacksView" [ con "RowKey", handle ]
      , ctor "DisjointView" [ handle, handle ]
      ]
  , simple "TypeView"
      [ ctor "VarType" [ string ]
      , ctor "MetaType" [ handle ]
      , ctor "ConType" [ name, list (con "KindView") ]
      , ctor "AppType" [ handle, handle ]
      , ctor "ForallType" [ string, con "KindView", handle ]
      , ctor "ConstrainedType" [ con "ConstraintView", handle ]
      , ctor "NormalRow" [ rowView ]
      ]
  , simple "EntrySort" [ ctor "ValueEntry" [], ctor "ForeignEntry" [], ctor "ConstructorEntry" [] ]
  , simple "AttrValue"
      [ ctor "AttrUnit" []
      , ctor "AttrBoolean" [ boolean ]
      , ctor "AttrInt" [ int ]
      , ctor "AttrString" [ string ]
      , ctor "AttrArray" [ list (con "AttrValue") ]
      , ctor "AttrObject" [ list (record [ Tuple "key" string, Tuple "value" (con "AttrValue") ]) ]
      ]
  , simple "MessagePart"
      [ ctor "TextPart" [ string ]
      , ctor "TypePart" [ handle ]
      , ctor "TermPart" [ handle ]
      , ctor "NamePart" [ name ]
      ]
  , simple "KernelRequest"
      [ ctor "BuildRequest" [ con "BuildRequest" ]
      , ctor "TermRequest" [ con "TermRequest" ]
      , ctor "TreeRequest" [ con "TreeRequest" ]
      , ctor "RecordRequest" [ con "RecordRequest" ]
      , ctor "HandlerRequest" [ con "HandlerRequest" ]
      , ctor "SolveRequest" [ con "SolveRequest" ]
      , ctor "ObserveRequest" [ con "ObserveRequest" ]
      , ctor "ReportRequest" [ con "ReportRequest" ]
      ]
  , simple "BuildRequest"
      [ ctor "RootScope" []
      , ctor "TypeVariable" [ handle, string ]
      , ctor "TypeConstructor" [ handle, name, list (con "KindView") ]
      , ctor "ApplyType" [ handle, handle, handle ]
      , ctor "EmptyRow" [ handle ]
      , ctor "ExtendRow" [ handle, con "RowKey", con "PayloadView", handle ]
      , ctor "UnionRow" [ handle, handle, handle ]
      , ctor "OpenForall" [ handle, string, con "KindView" ]
      , ctor "CloseForall" [ handle, handle, handle ]
      , ctor "OpenConstraint" [ handle, con "ConstraintView" ]
      , ctor "CloseConstraint" [ handle, handle, handle ]
      , ctor "InstantiateForall" [ handle, handle, handle ]
      , ctor "InstantiateScheme" [ handle, name, list (con "KindView") ]
      ]
  , simple "TermRequest"
      [ ctor "LocalVariable" [ handle, string ]
      , ctor "GlobalRef" [ handle, name, list (con "KindView") ]
      , ctor "LiteralTerm" [ handle, con "Literal" ]
      , ctor "TermApply" [ handle, handle, handle ]
      , ctor "TypeApply" [ handle, handle, handle ]
      , ctor "ConstraintApply" [ handle, handle ]
      , ctor "OpenLambda" [ handle, string, handle ]
      , ctor "CloseLambda" [ handle, handle, handle, handle ]
      , ctor "OpenTypeAbs" [ handle, string, con "KindView" ]
      , ctor "CloseTypeAbs" [ handle, handle, handle ]
      , ctor "OpenConstraintAbs" [ handle, con "ConstraintView" ]
      , ctor "CloseConstraintAbs" [ handle, handle, handle ]
      , ctor "OpenLet" [ handle, string, handle ]
      , ctor "CloseLet" [ handle, handle, handle ]
      , ctor "OpenLetRec" [ handle, list hinted ]
      , ctor "CloseLetRec" [ handle, handle, list handle, handle ]
      , ctor "OpenJoin" [ handle, string, list hinted, handle ]
      , ctor "CloseJoin" [ handle, handle, handle, handle ]
      , ctor "Jump" [ handle, handle, list handle ]
      ]
  , simple "TreeRequest"
      [ ctor "OpenCase" [ handle, list handle ]
      , ctor "CloseCase" [ handle, handle, maybe handle, handle ]
      , ctor "Leaf" [ handle, handle ]
      , ctor "Guard" [ handle, handle, handle, handle ]
      , ctor "OpenBind" [ handle, handle, string ]
      , ctor "CloseBind" [ handle, handle, handle ]
      , ctor "RecordField" [ handle, handle, con "RowKey" ]
      , ctor "OpenSwitchCtor" [ handle, handle, list name, boolean ]
      , ctor "OpenSwitchLit" [ handle, handle, list (con "Literal") ]
      , ctor "OpenSwitchKey" [ handle, handle, list (con "RowKey"), boolean ]
      , ctor "CloseSwitch" [ handle, handle, list handle, maybe handle ]
      ]
  , simple "RecordRequest"
      [ ctor "RecordEmpty" [ handle ]
      , ctor "RecordExtend" [ handle, con "RowKey", handle, handle ]
      , ctor "RecordSelect" [ handle, con "RowKey", handle ]
      , ctor "RecordRestrict" [ handle, con "RowKey", handle ]
      , ctor "RecordUpdate" [ handle, con "RowKey", handle, handle ]
      , ctor "RecordMerge" [ handle, handle, handle ]
      , ctor "VariantInject" [ handle, con "RowKey", handle ]
      , ctor "VariantWeaken" [ handle, con "RowKey", handle, handle ]
      , ctor "VariantAbsurd" [ handle, handle, handle ]
      , ctor "OpenEff" [ handle, handle, handle ]
      ]
  , simple "HandlerRequest"
      [ ctor "Perform" [ handle, con "RowKey", con "PayloadView", string, list handle, handle ]
      , ctor "OpenHandle"
          [ handle
          , handle
          , con "RowKey"
          , con "PayloadView"
          , maybe (list (record [ Tuple "key" (con "RowKey"), Tuple "type" handle ]))
          , handle
          , handle
          , list (record [ Tuple "op" string, Tuple "full" boolean ])
          ]
      , ctor "CloseHandle" [ handle, handle, handle, list handle, list handle ]
      , ctor "ReadCell" [ handle, con "RowKey" ]
      , ctor "WriteCell" [ handle, con "RowKey", handle ]
      ]
  , simple "SolveRequest"
      [ ctor "FreshMetaType" [ handle, con "KindView" ]
      , ctor "IsAssigned" [ handle ]
      , ctor "Unify" [ handle, handle, handle ]
      , ctor "Entails" [ handle, con "ConstraintView" ]
      , ctor "Require" [ handle, con "ConstraintView" ]
      , ctor "Subgoal" [ handle, handle, name ]
      ]
  , simple "ObserveRequest"
      [ ctor "GoalType" [ handle ]
      , ctor "ViewType" [ handle ]
      , ctor "Whnf" [ handle ]
      , ctor "NormalizeRow" [ handle ]
      , ctor "KindOf" [ handle ]
      , ctor "TypeOf" [ handle ]
      , ctor "LocalContext" []
      , ctor "LocalConstraints" []
      , ctor "LookupGlobal" [ name ]
      , ctor "DeclsWithAttr" [ string ]
      ]
  , simple "ReportRequest"
      [ ctor "Throw" [ list (con "MessagePart") ]
      , ctor "Warn" [ list (con "MessagePart") ]
      , ctor "Postpone" [ list handle ]
      ]
  , simple "KernelAnswer"
      [ ctor "UnitAnswer" []
      , ctor "HandleAnswer" [ handle ]
      , ctor "BooleanAnswer" [ boolean ]
      , ctor "TypeViewAnswer" [ con "TypeView" ]
      , ctor "RowViewAnswer" [ rowView ]
      , ctor "KindViewAnswer" [ con "KindView" ]
      , ctor "ContextAnswer" [ list (record [ Tuple "name" string, Tuple "type" handle ]) ]
      , ctor "ConstraintsAnswer" [ list (con "ConstraintView") ]
      , ctor "DeclAnswer" [ maybe declView ]
      , ctor "NamesAnswer" [ list name ]
      , ctor "BinderAnswer"
          [ record [ Tuple "binder" handle, Tuple "variable" handle, Tuple "bodyScope" handle ] ]
      , ctor "AssumptionAnswer" [ record [ Tuple "assumption" handle, Tuple "bodyScope" handle ] ]
      , ctor "ConstraintAbsAnswer" [ record [ Tuple "binder" handle, Tuple "bodyScope" handle ] ]
      , ctor "LetRecAnswer"
          [ record [ Tuple "binder" handle, Tuple "variables" (list handle), Tuple "bodyScope" handle ] ]
      , ctor "JoinAnswer"
          [ record
              [ Tuple "binder" handle
              , Tuple "join" handle
              , Tuple "params" (list handle)
              , Tuple "definitionScope" handle
              , Tuple "bodyScope" handle
              ]
          ]
      , ctor "CaseAnswer"
          [ record [ Tuple "binder" handle, Tuple "scrutinees" (list handle), Tuple "treeScope" handle ] ]
      , ctor "SwitchCtorAnswer"
          [ record
              [ Tuple "binder" handle
              , Tuple "branches" (list (record [ Tuple "scope" handle, Tuple "fields" (list handle) ]))
              , Tuple "fallback" (maybe handle)
              ]
          ]
      , ctor "SwitchLitAnswer"
          [ record [ Tuple "binder" handle, Tuple "branches" (list handle), Tuple "fallback" handle ] ]
      , ctor "SwitchKeyAnswer"
          [ record
              [ Tuple "binder" handle
              , Tuple "branches" (list (record [ Tuple "scope" handle, Tuple "payload" handle ]))
              , Tuple "fallback" (maybe (record [ Tuple "scope" handle, Tuple "residual" handle ]))
              ]
          ]
      , ctor "HandlerAnswer"
          [ record
              [ Tuple "binder" handle
              , Tuple "returnClause" (record [ Tuple "variable" handle, Tuple "scope" handle ])
              , Tuple "clauses"
                  ( list
                      ( record
                          [ Tuple "typeVariables" (list handle)
                          , Tuple "argument" handle
                          , Tuple "continuation" (maybe handle)
                          , Tuple "scope" handle
                          ]
                      )
                  )
              ]
          ]
      ]
  , simple "GuestCommand"
      [ ctor "Kernel" [ con "KernelRequest" ]
      , ctor "BeginTransaction" []
      , ctor "CommitTransaction" []
      ]
  , simple "GuestAnswer"
      [ ctor "Returned" [ con "KernelAnswer" ]
      , ctor "TransactionBegun" []
      , ctor "TransactionCommitted" []
      , ctor "CandidateFailed" []
      ]
  ]
  where
  hinted = record [ Tuple "hint" string, Tuple "type" handle ]

  rowView = record
    [ Tuple "elementKind" (maybe (con "RowElemKind"))
    , Tuple "known" (list (record [ Tuple "key" (con "RowKey"), Tuple "payload" (con "PayloadView") ]))
    , Tuple "rigid" (list string)
    , Tuple "flexible" (list (record [ Tuple "meta" handle, Tuple "type" handle ]))
    ]

  declView = record
    [ Tuple "name" name
    , Tuple "sort" (con "EntrySort")
    , Tuple "kindVars" (list string)
    , Tuple "scheme" handle
    , Tuple "attributes" (list (record [ Tuple "key" string, Tuple "value" (con "AttrValue") ]))
    ]

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

-- | The fields of a constructor of a data type of the module, in order. A name the
-- | module does not declare has none, and the operation built from it does not check.
fieldsOf :: P.String -> P.String -> P.Array Type
fieldsOf typeName ctorName =
  fromMaybe [] do
    d <- Array.find (\t -> t.name == typeName) types
    snd <$> Array.find (\(Tuple c _) -> c == ctorName) d.ctors

-- | What an operation gives back: what its answer carries, `Unit` for an answer
-- | carrying nothing, and nothing for an operation answered by none.
resultOf :: Operation -> Maybe Type
resultOf o = o.answer <#> \answer -> case fieldsOf "KernelAnswer" answer of
  [ carried ] -> carried
  _ -> unitType

-- | The type of an operation: its request's fields in order, each arrow but the
-- | last pure, and the last at `elabRow`. An operation of no field takes `Unit`.
-- | `throw` and `postpone`, answered by none, give back whatever is asked of them.
operationType :: Operation -> Type
operationType o = case resultOf o of
  Just result -> arrows result
  Nothing -> TForall anyVar KType (arrows (TVar anyVar))
  where
  arrows result = case Array.unsnoc (parametersOf o) of
    Just { init, last } -> foldr pureFn (fn last elabRow result) init
    Nothing -> fn unitType elabRow result

parametersOf :: Operation -> P.Array Type
parametersOf o = fieldsOf o.family o.request

-- `ask`: perform a request and give back what its answer is, where it is `Returned`.
-- A candidate failure aborts to the innermost `transact`; any other answer is a
-- breach.
askDecl :: Decl Unit
askDecl = DeclNonRec unit
  { name: Ident "ask"
  , scheme: monoScheme (fn (con "KernelRequest") elabRow (con "KernelAnswer"))
  , value: Lam unit request (con "KernelRequest")
      ( Let unit answered (con "GuestAnswer")
          (command (construct elabRow "Kernel" [] [ Var unit request ]))
          ( Case unit [ Var unit answered ]
              ( SwitchCtor scrutinee
                  [ { ctor: elab "Returned"
                    , tree: Bind carried (OccField scrutinee (elab "Returned") 0) (Leaf (Var unit carried))
                    }
                  , { ctor: elab "CandidateFailed", tree: Leaf (escapeWith abortEffect failedOp (con "KernelAnswer")) }
                  ]
                  (Just (Leaf (breach (con "KernelAnswer"))))
              )
          )
      )
  , attributes: []
  }
  where
  request = Ident "request"
  answered = Ident "answered"
  carried = Ident "carried"

-- One typed operation: the request made from its arguments, asked, and the answer
-- taken apart where it is the one expected. Any other answer is a breach.
operationDecl :: Operation -> Decl Unit
operationDecl o = DeclNonRec unit
  { name: Ident o.name
  , scheme: monoScheme (operationType o)
  , value: case resultOf o of
      Just result -> lambdas (answeredAs result)
      Nothing -> TyLam unit anyVar KType (lambdas (Let unit (Ident "ignored") (con "KernelAnswer") asked (breach (TVar anyVar))))
  , attributes: []
  }
  where
  parameters = Array.mapWithIndex (\i t -> { name: Ident ("x" <> show i), ty: t }) (parametersOf o)

  lambdas body = case Array.null parameters of
    true -> Lam unit (Ident "x") unitType body
    false -> foldr (\p inner -> Lam unit p.name p.ty inner) body parameters

  asked = App unit (Global unit (elab "ask") [])
    ( construct elabRow o.family []
        [ construct elabRow o.request [] (map (\p -> Var unit p.name) parameters) ]
    )

  answeredAs result = Case unit [ asked ]
    ( SwitchCtor scrutinee
        [ { ctor: elab answer, tree: taken } ]
        (Just (Leaf (breach result)))
    )
    where
    answer = fromMaybe "" o.answer
    carried = Ident "carried"
    taken = case fieldsOf "KernelAnswer" answer of
      [ _ ] -> Bind carried (OccField scrutinee (elab answer) 0) (Leaf (Var unit carried))
      _ -> Leaf unitValue

-- `transact`: open a transaction, run the candidate with `Abort` handled, and commit
-- where it returns. **A failure closes nothing here**: the host has closed the
-- innermost transaction as it answered, which is this one, the transactions a
-- guest opens being nested as its calls of `transact` are. The handling stands
-- inside a function annotated at `( Breach, Kernel )` and widened by `Abort`: the
-- row `transact` runs at already holds the `Abort` the handled candidate raises,
-- and a `λ` with no annotation would take that row.
transactDecl :: Decl Unit
transactDecl = DeclNonRec unit
  { name: Ident "transact"
  , scheme: monoScheme
      (TForall a KType (fn (fn unitType elabRow (TVar a)) elabRow (maybeOf (TVar a))))
  , value: TyLam unit a KType
      ( Lam unit candidate (fn unitType elabRow (TVar a))
          ( Let unit begun (con "GuestAnswer") (command (Global unit (elab "BeginTransaction") []))
              ( Case unit [ Var unit begun ]
                  ( SwitchCtor scrutinee
                      [ { ctor: elab "TransactionBegun"
                        , tree: Leaf
                            ( Let unit handling (fn unitType outside (maybeOf (TVar a)))
                                (Lam unit (Ident "u") unitType handled)
                                (App unit (OpenEff unit (effectRow [ abortEffect ]) (Var unit handling)) unitValue)
                            )
                        }
                      ]
                      (Just (Leaf (breach (maybeOf (TVar a)))))
                  )
              )
          )
      )
  , attributes: []
  }
  where
  a = TyVar "a"
  candidate = Ident "candidate"
  begun = Ident "begun"
  handling = Ident "handling"
  committed = Ident "committed"
  result = Ident "result"
  outside = effectRow [ breachEffect, kernelEffect ]

  handled = Handle unit (App unit (Var unit candidate) unitValue)
    { element: RowEffectEntry abortEffect []
    , cells: Nothing
    , returnClause: { binder: result, ty: TVar a, body: committing }
    , opClauses: [ abandoning failedOp outside (maybeOf (TVar a)) (TyApp unit (Global unit (elab "Nothing") []) (TVar a)) ]
    }
    []

  -- the candidate returned: the transaction committed, or failed as it closed
  committing = Let unit committed (con "GuestAnswer") (command (Global unit (elab "CommitTransaction") []))
    ( Case unit [ Var unit committed ]
        ( SwitchCtor scrutinee
            [ { ctor: elab "TransactionCommitted", tree: Leaf (construct outside "Just" [ TVar a ] [ Var unit result ]) }
            , { ctor: elab "CandidateFailed", tree: Leaf (TyApp unit (Global unit (elab "Nothing") []) (TVar a)) }
            ]
            (Just (Leaf (breach (maybeOf (TVar a)))))
        )
    )

-- `synthesizer`: a policy made into what an invocation calls. `Abort` reaching it
-- — a candidate failing outside every transaction — and `Breach` both end the
-- policy with the goal it was given, neither of which a conforming host brings
-- about. The host's checks where the attempt finishes make a defect of it at once,
-- whatever the budget: a transaction a breach left open, or else a result that is
-- no term.
synthesizerDecl :: Decl Unit
synthesizerDecl = DeclNonRec unit
  { name: Ident "synthesizer"
  , scheme: monoScheme (pureFn policyType (fn handle kernelOnly handle))
  , value: Lam unit policy policyType
      ( Lam unit goal handle
          ( Handle unit
              ( Handle unit (App unit (Var unit policy) (Var unit goal))
                  (endingWithGoal abortEffect failedOp (effectRow [ breachEffect, kernelEffect ]))
                  []
              )
              (endingWithGoal breachEffect breachedOp kernelOnly)
              []
          )
      )
  , attributes: []
  }
  where
  policy = Ident "policy"
  goal = Ident "goal"
  policyType = fn handle elabRow handle
  kernelOnly = effectRow [ kernelEffect ]

  endingWithGoal effect escapeOp outside =
    { element: RowEffectEntry effect []
    , cells: Nothing
    , returnClause: { binder: Ident "result", ty: handle, body: Var unit (Ident "result") }
    , opClauses: [ abandoning escapeOp outside handle (Var unit goal) ]
    }

-- A clause for an escape that drops its continuation and answers with the body
-- given. It is `full`: a `fast` clause would resume where the escape was raised.
abandoning :: OpName -> Type -> Type -> Expr Unit -> OpClause Unit
abandoning escapeOp outside answer body = FullClause
  { op: escapeOp
  , tyBinders: [ { name: resumed, kind: KType } ]
  , argBinder: { name: Ident "raised", ty: unitType }
  , contBinder: { name: Ident "dropped", ty: fn (TVar resumed) outside answer }
  , body
  }
  where
  resumed = TyVar "resumed"

-- Term shorthands ---------------------------------------------------------------------------

-- `perform Kernel.command c`.
command :: Expr Unit -> Expr Unit
command = Perform unit (EffectKey kernelEffect) commandOp []

-- An escape raised at the type given.
escapeWith :: Qualified EffName -> OpName -> Type -> Expr Unit
escapeWith effect escapeOp ty = Perform unit (EffectKey effect) escapeOp [ ty ] unitValue

breach :: Type -> Expr Unit
breach = escapeWith breachEffect breachedOp

-- A constructor of the module at the type arguments given, applied to the arguments
-- given where the ambient row is the one given. A constructor's arrows are pure, so
-- each is widened into that row before it is applied (D8).
construct :: Type -> P.String -> P.Array Type -> P.Array (Expr Unit) -> Expr Unit
construct row c tyArgs = foldl (\f x -> App unit (OpenEff unit row f) x)
  (foldl (TyApp unit) (Global unit (elab c) []) tyArgs)

elab :: P.String -> Qualified Ident
elab = Qualified elabModule <<< Ident

scrutinee :: Occurrence
scrutinee = OccScrutinee 0

unitValue :: Expr Unit
unitValue = Global unit unitCtor []

unitType :: Type
unitType = TCon unitTy []

anyVar :: TyVar
anyVar = TyVar "a"

maybeOf :: Type -> Type
maybeOf = maybe

effectRow :: P.Array (Qualified EffName) -> Type
effectRow = foldr (\e rest -> TRowExtend (RowEffectEntry e []) rest) TRowEmpty
