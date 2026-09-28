-- | A synthesizer written in the host, against the kernel's requests alone.
-- |
-- | **A synthesizer is a script**: the requests it makes, each followed by what
-- | it does with the answer. It holds no session, no frame, and no state; the
-- | driver running it answers each request in the attempt it runs, as a guest
-- | on Steam is answered. Every operation here makes exactly the request its
-- | name says, and takes back only the shape of answer that request is answered
-- | in, the table the host holds its answers to.
-- |
-- | `transact` is the one form not made of requests: the driver opens a
-- | transaction where it starts and commits it where it ends, and a failure
-- | answered inside it resumes the script after it with the diagnostic.
module Stella.Compiler.Elaborate.Facade
  ( module Exports
  , Synthesizer
  , rootScope
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
  , localVariable
  , globalRef
  , literal
  , termApply
  , typeApply
  , constraintApply
  , openLambda
  , closeLambda
  , openTypeAbs
  , closeTypeAbs
  , openConstraintAbs
  , closeConstraintAbs
  , openLet
  , closeLet
  , openLetRec
  , closeLetRec
  , openJoin
  , closeJoin
  , jump
  , openCase
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
  , recordEmpty
  , recordExtend
  , recordSelect
  , recordRestrict
  , recordUpdate
  , recordMerge
  , variantInject
  , variantWeaken
  , variantAbsurd
  , openEff
  , perform
  , openHandle
  , closeHandle
  , readCell
  , writeCell
  , freshMetaType
  , isAssigned
  , unify
  , entails
  , require
  , subgoal
  , goalType
  , viewType
  , whnf
  , normalizeRow
  , kindOf
  , typeOf
  , localContext
  , localConstraints
  , lookupGlobal
  , declsWithAttr
  , throw
  , warn
  , postpone
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Handle (Handle)
import Stella.Compiler.Elaborate.Message (MessagePart)
import Stella.Compiler.Elaborate.Pending (SynthRef)
import Stella.Compiler.Elaborate.Request (BuildRequest(..), HandlerRequest(..), KernelAnswer(..), KernelRequest(..), ObserveRequest(..), RecordRequest(..), ReportRequest(..), SolveRequest(..), TermRequest(..), TreeRequest(..))
import Stella.Compiler.Elaborate.View (ConstraintView, ContextEntry, DeclView, KindView, PayloadView, RowView, TypeView)
import Stella.Compiler.TypedCore (Ident, Literal, OpName, Qualified, RowKey, TyName, TyVar)
import Stella.Compiler.Elaborate.Facade.Internal (Facade, kernel)
import Stella.Compiler.Elaborate.Facade.Internal (Facade, transact) as Exports
import Data.Maybe (Maybe(..))

-- | A synthesizer, given its goal as a Goal handle, ending in the Expr handle it
-- | offers as the goal's solution.
type Synthesizer = Handle -> Facade Handle

handleOf :: KernelAnswer -> Maybe Handle
handleOf = case _ of
  HandleAnswer h -> Just h
  _ -> Nothing

unitOf :: KernelAnswer -> Maybe Unit
unitOf = case _ of
  UnitAnswer -> Just unit
  _ -> Nothing

booleanOf :: KernelAnswer -> Maybe P.Boolean
booleanOf = case _ of
  BooleanAnswer b -> Just b
  _ -> Nothing

binderOf :: KernelAnswer -> Maybe { binder :: Handle, variable :: Handle, bodyScope :: Handle }
binderOf = case _ of
  BinderAnswer r -> Just r
  _ -> Nothing

buildHandle :: BuildRequest -> Facade Handle
buildHandle request = kernel (BuildRequest request) handleOf

termHandle :: TermRequest -> Facade Handle
termHandle request = kernel (TermRequest request) handleOf

treeHandle :: TreeRequest -> Facade Handle
treeHandle request = kernel (TreeRequest request) handleOf

recordHandle :: RecordRequest -> Facade Handle
recordHandle request = kernel (RecordRequest request) handleOf

handlerHandle :: HandlerRequest -> Facade Handle
handlerHandle request = kernel (HandlerRequest request) handleOf

rootScope :: Facade Handle
rootScope = buildHandle RootScope

typeVariable :: Handle -> TyVar -> Facade Handle
typeVariable scope name = buildHandle (TypeVariable scope name)

typeConstructor :: Handle -> Qualified TyName -> P.Array KindView -> Facade Handle
typeConstructor scope name kinds = buildHandle (TypeConstructor scope name kinds)

applyType :: Handle -> Handle -> Handle -> Facade Handle
applyType scope f a = buildHandle (ApplyType scope f a)

emptyRow :: Handle -> Facade Handle
emptyRow scope = buildHandle (EmptyRow scope)

extendRow :: Handle -> RowKey -> PayloadView -> Handle -> Facade Handle
extendRow scope key payload rest = buildHandle (ExtendRow scope key payload rest)

unionRow :: Handle -> Handle -> Handle -> Facade Handle
unionRow scope left right = buildHandle (UnionRow scope left right)

openForall :: Handle -> P.String -> KindView -> Facade { binder :: Handle, variable :: Handle, bodyScope :: Handle }
openForall scope hint kind = kernel (BuildRequest (OpenForall scope hint kind)) binderOf

closeForall :: Handle -> Handle -> Handle -> Facade Handle
closeForall scope binder body = buildHandle (CloseForall scope binder body)

openConstraint :: Handle -> ConstraintView -> Facade { assumption :: Handle, bodyScope :: Handle }
openConstraint scope constraint = kernel (BuildRequest (OpenConstraint scope constraint)) case _ of
  AssumptionAnswer r -> Just r
  _ -> Nothing

closeConstraint :: Handle -> Handle -> Handle -> Facade Handle
closeConstraint scope assumption body = buildHandle (CloseConstraint scope assumption body)

instantiateForall :: Handle -> Handle -> Handle -> Facade Handle
instantiateForall scope quantified argument = buildHandle (InstantiateForall scope quantified argument)

instantiateScheme :: Handle -> Qualified Ident -> P.Array KindView -> Facade Handle
instantiateScheme scope name kinds = buildHandle (InstantiateScheme scope name kinds)

localVariable :: Handle -> Ident -> Facade Handle
localVariable scope name = termHandle (LocalVariable scope name)

globalRef :: Handle -> Qualified Ident -> P.Array KindView -> Facade Handle
globalRef scope name kinds = termHandle (GlobalRef scope name kinds)

literal :: Handle -> Literal -> Facade Handle
literal scope lit = termHandle (LiteralTerm scope lit)

termApply :: Handle -> Handle -> Handle -> Facade Handle
termApply scope f a = termHandle (TermApply scope f a)

typeApply :: Handle -> Handle -> Handle -> Facade Handle
typeApply scope e t = termHandle (TypeApply scope e t)

constraintApply :: Handle -> Handle -> Facade Handle
constraintApply scope e = termHandle (ConstraintApply scope e)

openLambda :: Handle -> P.String -> Handle -> Facade { binder :: Handle, variable :: Handle, bodyScope :: Handle }
openLambda scope hint ty = kernel (TermRequest (OpenLambda scope hint ty)) binderOf

closeLambda :: Handle -> Handle -> Handle -> Handle -> Facade Handle
closeLambda scope binder body row = termHandle (CloseLambda scope binder body row)

openTypeAbs :: Handle -> P.String -> KindView -> Facade { binder :: Handle, variable :: Handle, bodyScope :: Handle }
openTypeAbs scope hint kind = kernel (TermRequest (OpenTypeAbs scope hint kind)) binderOf

closeTypeAbs :: Handle -> Handle -> Handle -> Facade Handle
closeTypeAbs scope binder body = termHandle (CloseTypeAbs scope binder body)

openConstraintAbs :: Handle -> ConstraintView -> Facade { binder :: Handle, bodyScope :: Handle }
openConstraintAbs scope constraint = kernel (TermRequest (OpenConstraintAbs scope constraint)) case _ of
  ConstraintAbsAnswer r -> Just r
  _ -> Nothing

closeConstraintAbs :: Handle -> Handle -> Handle -> Facade Handle
closeConstraintAbs scope binder body = termHandle (CloseConstraintAbs scope binder body)

openLet :: Handle -> P.String -> Handle -> Facade { binder :: Handle, variable :: Handle, bodyScope :: Handle }
openLet scope hint value = kernel (TermRequest (OpenLet scope hint value)) binderOf

closeLet :: Handle -> Handle -> Handle -> Facade Handle
closeLet scope binder body = termHandle (CloseLet scope binder body)

openLetRec :: Handle -> P.Array { hint :: P.String, type :: Handle } -> Facade { binder :: Handle, variables :: P.Array Handle, bodyScope :: Handle }
openLetRec scope bindings = kernel (TermRequest (OpenLetRec scope bindings)) case _ of
  LetRecAnswer r -> Just r
  _ -> Nothing

closeLetRec :: Handle -> Handle -> P.Array Handle -> Handle -> Facade Handle
closeLetRec scope binder rhss body = termHandle (CloseLetRec scope binder rhss body)

openJoin
  :: Handle
  -> P.String
  -> P.Array { hint :: P.String, type :: Handle }
  -> Handle
  -> Facade { binder :: Handle, join :: Handle, params :: P.Array Handle, definitionScope :: Handle, bodyScope :: Handle }
openJoin scope hint params result = kernel (TermRequest (OpenJoin scope hint params result)) case _ of
  JoinAnswer r -> Just r
  _ -> Nothing

closeJoin :: Handle -> Handle -> Handle -> Handle -> Facade Handle
closeJoin scope binder definition body = termHandle (CloseJoin scope binder definition body)

jump :: Handle -> Handle -> P.Array Handle -> Facade Handle
jump scope join args = termHandle (Jump scope join args)

openCase :: Handle -> P.Array Handle -> Facade { binder :: Handle, scrutinees :: P.Array Handle, treeScope :: Handle }
openCase scope scrutinees = kernel (TreeRequest (OpenCase scope scrutinees)) case _ of
  CaseAnswer r -> Just r
  _ -> Nothing

closeCase :: Handle -> Handle -> Maybe Handle -> Handle -> Facade Handle
closeCase scope binder result tree = treeHandle (CloseCase scope binder result tree)

leaf :: Handle -> Handle -> Facade Handle
leaf scope e = treeHandle (Leaf scope e)

guard :: Handle -> Handle -> Handle -> Handle -> Facade Handle
guard scope condition yes no = treeHandle (Guard scope condition yes no)

openBind :: Handle -> Handle -> P.String -> Facade { binder :: Handle, variable :: Handle, bodyScope :: Handle }
openBind scope occurrence hint = kernel (TreeRequest (OpenBind scope occurrence hint)) binderOf

closeBind :: Handle -> Handle -> Handle -> Facade Handle
closeBind scope binder tree = treeHandle (CloseBind scope binder tree)

recordField :: Handle -> Handle -> RowKey -> Facade Handle
recordField scope occurrence key = treeHandle (RecordField scope occurrence key)

openSwitchCtor
  :: Handle
  -> Handle
  -> P.Array (Qualified Ident)
  -> P.Boolean
  -> Facade { binder :: Handle, branches :: P.Array { scope :: Handle, fields :: P.Array Handle }, fallback :: Maybe Handle }
openSwitchCtor scope occurrence ctors withDefault = kernel (TreeRequest (OpenSwitchCtor scope occurrence ctors withDefault)) case _ of
  SwitchCtorAnswer r -> Just r
  _ -> Nothing

openSwitchLit :: Handle -> Handle -> P.Array Literal -> Facade { binder :: Handle, branches :: P.Array Handle, fallback :: Handle }
openSwitchLit scope occurrence lits = kernel (TreeRequest (OpenSwitchLit scope occurrence lits)) case _ of
  SwitchLitAnswer r -> Just r
  _ -> Nothing

openSwitchKey
  :: Handle
  -> Handle
  -> P.Array RowKey
  -> P.Boolean
  -> Facade
       { binder :: Handle
       , branches :: P.Array { scope :: Handle, payload :: Handle }
       , fallback :: Maybe { scope :: Handle, residual :: Handle }
       }
openSwitchKey scope occurrence keys withDefault = kernel (TreeRequest (OpenSwitchKey scope occurrence keys withDefault)) case _ of
  SwitchKeyAnswer r -> Just r
  _ -> Nothing

closeSwitch :: Handle -> Handle -> P.Array Handle -> Maybe Handle -> Facade Handle
closeSwitch scope binder trees fallback = treeHandle (CloseSwitch scope binder trees fallback)

recordEmpty :: Handle -> Facade Handle
recordEmpty scope = recordHandle (RecordEmpty scope)

recordExtend :: Handle -> RowKey -> Handle -> Handle -> Facade Handle
recordExtend scope key value rest = recordHandle (RecordExtend scope key value rest)

recordSelect :: Handle -> RowKey -> Handle -> Facade Handle
recordSelect scope key e = recordHandle (RecordSelect scope key e)

recordRestrict :: Handle -> RowKey -> Handle -> Facade Handle
recordRestrict scope key e = recordHandle (RecordRestrict scope key e)

recordUpdate :: Handle -> RowKey -> Handle -> Handle -> Facade Handle
recordUpdate scope key e value = recordHandle (RecordUpdate scope key e value)

recordMerge :: Handle -> Handle -> Handle -> Facade Handle
recordMerge scope left right = recordHandle (RecordMerge scope left right)

variantInject :: Handle -> RowKey -> Handle -> Facade Handle
variantInject scope key value = recordHandle (VariantInject scope key value)

variantWeaken :: Handle -> RowKey -> Handle -> Handle -> Facade Handle
variantWeaken scope key payload e = recordHandle (VariantWeaken scope key payload e)

variantAbsurd :: Handle -> Handle -> Handle -> Facade Handle
variantAbsurd scope result e = recordHandle (VariantAbsurd scope result e)

openEff :: Handle -> Handle -> Handle -> Facade Handle
openEff scope row e = recordHandle (OpenEff scope row e)

perform :: Handle -> RowKey -> PayloadView -> OpName -> P.Array Handle -> Handle -> Facade Handle
perform scope key payload op typeArgs argument = handlerHandle (Perform scope key payload op typeArgs argument)

openHandle
  :: Handle
  -> Handle
  -> RowKey
  -> PayloadView
  -> Maybe (P.Array { key :: RowKey, type :: Handle })
  -> Handle
  -> Handle
  -> P.Array { op :: OpName, full :: P.Boolean }
  -> Facade
       { binder :: Handle
       , returnClause :: { variable :: Handle, scope :: Handle }
       , clauses ::
           P.Array
             { typeVariables :: P.Array Handle
             , argument :: Handle
             , continuation :: Maybe Handle
             , scope :: Handle
             }
       }
openHandle scope computation key payload layout answer residual clauses =
  kernel (HandlerRequest (OpenHandle scope computation key payload layout answer residual clauses)) case _ of
    HandlerAnswer r -> Just r
    _ -> Nothing

closeHandle :: Handle -> Handle -> Handle -> P.Array Handle -> P.Array Handle -> Facade Handle
closeHandle scope binder returnBody clauseBodies initials = handlerHandle (CloseHandle scope binder returnBody clauseBodies initials)

readCell :: Handle -> RowKey -> Facade Handle
readCell scope key = handlerHandle (ReadCell scope key)

writeCell :: Handle -> RowKey -> Handle -> Facade Handle
writeCell scope key value = handlerHandle (WriteCell scope key value)

freshMetaType :: Handle -> KindView -> Facade Handle
freshMetaType scope kind = kernel (SolveRequest (FreshMetaType scope kind)) handleOf

isAssigned :: Handle -> Facade P.Boolean
isAssigned meta = kernel (SolveRequest (IsAssigned meta)) booleanOf

unify :: Handle -> Handle -> Handle -> Facade Unit
unify scope left right = kernel (SolveRequest (Unify scope left right)) unitOf

entails :: Handle -> ConstraintView -> Facade P.Boolean
entails scope constraint = kernel (SolveRequest (Entails scope constraint)) booleanOf

require :: Handle -> ConstraintView -> Facade Unit
require scope constraint = kernel (SolveRequest (Require scope constraint)) unitOf

subgoal :: Handle -> Handle -> SynthRef -> Facade Handle
subgoal scope ty synthesizer = kernel (SolveRequest (Subgoal scope ty synthesizer)) handleOf

goalType :: Handle -> Facade Handle
goalType goal = kernel (ObserveRequest (GoalType goal)) handleOf

viewType :: Handle -> Facade TypeView
viewType ty = kernel (ObserveRequest (ViewType ty)) case _ of
  TypeViewAnswer v -> Just v
  _ -> Nothing

whnf :: Handle -> Facade Handle
whnf ty = kernel (ObserveRequest (Whnf ty)) handleOf

normalizeRow :: Handle -> Facade RowView
normalizeRow row = kernel (ObserveRequest (NormalizeRow row)) case _ of
  RowViewAnswer v -> Just v
  _ -> Nothing

kindOf :: Handle -> Facade KindView
kindOf ty = kernel (ObserveRequest (KindOf ty)) case _ of
  KindViewAnswer v -> Just v
  _ -> Nothing

typeOf :: Handle -> Facade Handle
typeOf e = kernel (ObserveRequest (TypeOf e)) handleOf

localContext :: Facade (P.Array ContextEntry)
localContext = kernel (ObserveRequest LocalContext) case _ of
  ContextAnswer entries -> Just entries
  _ -> Nothing

localConstraints :: Facade (P.Array ConstraintView)
localConstraints = kernel (ObserveRequest LocalConstraints) case _ of
  ConstraintsAnswer constraints -> Just constraints
  _ -> Nothing

lookupGlobal :: Qualified Ident -> Facade (Maybe DeclView)
lookupGlobal name = kernel (ObserveRequest (LookupGlobal name)) case _ of
  DeclAnswer decl -> Just decl
  _ -> Nothing

declsWithAttr :: P.String -> Facade (P.Array (Qualified Ident))
declsWithAttr attribute = kernel (ObserveRequest (DeclsWithAttr attribute)) case _ of
  NamesAnswer names -> Just names
  _ -> Nothing

-- | Fail: this candidate, or this goal, does not hold. It is answered in no
-- | shape.
throw :: forall a. P.Array MessagePart -> Facade a
throw message = kernel (ReportRequest (Throw message)) (const Nothing)

warn :: P.Array MessagePart -> Facade Unit
warn message = kernel (ReportRequest (Warn message)) unitOf

-- | Wait on the metavariables named. It is answered in no shape.
postpone :: forall a. P.Array Handle -> Facade a
postpone metas = kernel (ReportRequest (Postpone metas)) (const Nothing)
