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
  , guestCommandTy
  , guestAnswerTy
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Either (Either)
import Data.Foldable (foldr)
import Data.Map as Map
import Data.Tuple (Tuple(..))
import Stella.Compiler.Elaborate.Protocol.Guest.Shape (Descriptor, describe)
import Stella.Compiler.TypedCore (CanonicalClass(..), Decl(..), EffName(..), Export(..), Ident(..), Kind(..), Module, ModuleName(..), OpName(..), Qualified(..), RowEntry(..), RowKey(..), Signature, Symbol(..), TyName(..), TyConInfo(..), TyVar(..), Type(..), monoScheme)
import Stella.Compiler.TypedCore.Prim (booleanTy, charTy, intTy, numberTy, recordTy, stringTy)

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
        <> [ ExportEffect (EffName "Kernel") ]
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
          ]
  }
  where
  ctorName (Tuple c _) = c

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
