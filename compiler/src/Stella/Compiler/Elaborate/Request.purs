-- | What a synthesizer can ask of the host, and what it is answered: the
-- | vocabulary of a compile-time session.
-- |
-- | **Every request is first-order data.** It holds handles, views, names, and
-- | literals, and never a function or a host representation, so one request is
-- | the same thing whether a host script makes it or a guest running on Steam
-- | sends it. The session and the frame a request is answered under are the
-- | host's: nothing in a request can name another.
-- |
-- | A kernel request is one public kernel operation with its arguments, grouped
-- | by the part of the kernel it belongs to. A command is what a conversation is
-- | driven by: a kernel request, or the opening, closing, and finishing of a
-- | transaction and of the attempt.
-- |
-- | **An answer is classified by its shape, not by the request it answers**, so
-- | operations answering alike share a constructor. Which shape a request is
-- | answered in is fixed by `expectedAnswerShape`, the one table the host's
-- | answers and a script's operations are both held to; an answer in another
-- | shape is a defect of the host.
module Stella.Compiler.Elaborate.Request
  ( KernelRequest(..)
  , BuildRequest(..)
  , TermRequest(..)
  , TreeRequest(..)
  , RecordRequest(..)
  , HandlerRequest(..)
  , SolveRequest(..)
  , ObserveRequest(..)
  , ReportRequest(..)
  , KernelAnswer(..)
  , Command(..)
  , CommandAnswer(..)
  , AnswerShape(..)
  , answerShape
  , expectedAnswerShape
  , answersAs
  ) where

import Prelude

import Prim as P

import Stella.Compiler.Elaborate.Handle (Handle)
import Stella.Compiler.Elaborate.Message (MessagePart)
import Stella.Compiler.Elaborate.Pending (SynthRef)
import Stella.Compiler.Elaborate.Protocol (TransactionToken)
import Stella.Compiler.Elaborate.View (ConstraintView, ContextEntry, DeclView, KindView, PayloadView, RowView, TypeView)
import Stella.Compiler.TypedCore (Ident, Literal, OpName, Qualified, RowKey, TyName, TyVar)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)

data KernelRequest
  = BuildRequest BuildRequest
  | TermRequest TermRequest
  | TreeRequest TreeRequest
  | RecordRequest RecordRequest
  | HandlerRequest HandlerRequest
  | SolveRequest SolveRequest
  | ObserveRequest ObserveRequest
  | ReportRequest ReportRequest

-- | Build scopes and the types built in them.
data BuildRequest
  = RootScope
  | TypeVariable Handle TyVar
  | TypeConstructor Handle (Qualified TyName) (P.Array KindView)
  | ApplyType Handle Handle Handle
  | EmptyRow Handle
  | ExtendRow Handle RowKey PayloadView Handle
  | UnionRow Handle Handle Handle
  | OpenForall Handle P.String KindView
  | CloseForall Handle Handle Handle
  | OpenConstraint Handle ConstraintView
  | CloseConstraint Handle Handle Handle
  | InstantiateForall Handle Handle Handle
  | InstantiateScheme Handle (Qualified Ident) (P.Array KindView)

-- | Terms other than cases, records, variants, and handlers.
data TermRequest
  = LocalVariable Handle Ident
  | GlobalRef Handle (Qualified Ident) (P.Array KindView)
  | LiteralTerm Handle Literal
  | TermApply Handle Handle Handle
  | TypeApply Handle Handle Handle
  | ConstraintApply Handle Handle
  | OpenLambda Handle P.String Handle
  | CloseLambda Handle Handle Handle Handle
  | OpenTypeAbs Handle P.String KindView
  | CloseTypeAbs Handle Handle Handle
  | OpenConstraintAbs Handle ConstraintView
  | CloseConstraintAbs Handle Handle Handle
  | OpenLet Handle P.String Handle
  | CloseLet Handle Handle Handle
  | OpenLetRec Handle (P.Array { hint :: P.String, type :: Handle })
  | CloseLetRec Handle Handle (P.Array Handle) Handle
  | OpenJoin Handle P.String (P.Array { hint :: P.String, type :: Handle }) Handle
  | CloseJoin Handle Handle Handle Handle
  | Jump Handle Handle (P.Array Handle)

-- | Cases and their decision trees.
data TreeRequest
  = OpenCase Handle (P.Array Handle)
  | CloseCase Handle Handle (Maybe Handle) Handle
  | Leaf Handle Handle
  | Guard Handle Handle Handle Handle
  | OpenBind Handle Handle P.String
  | CloseBind Handle Handle Handle
  | RecordField Handle Handle RowKey
  | OpenSwitchCtor Handle Handle (P.Array (Qualified Ident)) P.Boolean
  | OpenSwitchLit Handle Handle (P.Array Literal)
  | OpenSwitchKey Handle Handle (P.Array RowKey) P.Boolean
  | CloseSwitch Handle Handle (P.Array Handle) (Maybe Handle)

-- | Records, variants, and `openEff`.
data RecordRequest
  = RecordEmpty Handle
  | RecordExtend Handle RowKey Handle Handle
  | RecordSelect Handle RowKey Handle
  | RecordRestrict Handle RowKey Handle
  | RecordUpdate Handle RowKey Handle Handle
  | RecordMerge Handle Handle Handle
  | VariantInject Handle RowKey Handle
  | VariantWeaken Handle RowKey Handle Handle
  | VariantAbsurd Handle Handle Handle
  | OpenEff Handle Handle Handle

-- | Effect operations, handlers, and cells.
data HandlerRequest
  = Perform Handle RowKey PayloadView OpName (P.Array Handle) Handle
  | OpenHandle Handle Handle RowKey PayloadView (Maybe (P.Array { key :: RowKey, type :: Handle })) Handle Handle (P.Array { op :: OpName, full :: P.Boolean })
  | CloseHandle Handle Handle Handle (P.Array Handle) (P.Array Handle)
  | ReadCell Handle RowKey
  | WriteCell Handle RowKey Handle

-- | Metavariables, equations, constraints, and subgoals.
data SolveRequest
  = FreshMetaType Handle KindView
  | IsAssigned Handle
  | Unify Handle Handle Handle
  | Entails Handle ConstraintView
  | Require Handle ConstraintView
  | Subgoal Handle Handle SynthRef

-- | Views of types, of the running goal, and of the catalog.
data ObserveRequest
  = GoalType Handle
  | ViewType Handle
  | Whnf Handle
  | NormalizeRow Handle
  | KindOf Handle
  | TypeOf Handle
  | LocalContext
  | LocalConstraints
  | LookupGlobal (Qualified Ident)
  | DeclsWithAttr P.String

-- | Failing, warning, and waiting.
data ReportRequest
  = Throw (P.Array MessagePart)
  | Warn (P.Array MessagePart)
  | Postpone (P.Array Handle)

-- | A kernel request's answer, by shape. `throw` and `postpone` are answered in
-- | none: they end the attempt, or the candidate.
data KernelAnswer
  = UnitAnswer
  | HandleAnswer Handle
  | BooleanAnswer P.Boolean
  | TypeViewAnswer TypeView
  | RowViewAnswer RowView
  | KindViewAnswer KindView
  | ContextAnswer (P.Array ContextEntry)
  | ConstraintsAnswer (P.Array ConstraintView)
  | DeclAnswer (Maybe DeclView)
  | NamesAnswer (P.Array (Qualified Ident))
  -- | A binder opened with one variable: a `forall`, a lambda, a type
  -- | abstraction, a `let`, or a `bind`.
  | BinderAnswer { binder :: Handle, variable :: Handle, bodyScope :: Handle }
  | AssumptionAnswer { assumption :: Handle, bodyScope :: Handle }
  | ConstraintAbsAnswer { binder :: Handle, bodyScope :: Handle }
  | LetRecAnswer { binder :: Handle, variables :: P.Array Handle, bodyScope :: Handle }
  | JoinAnswer
      { binder :: Handle
      , join :: Handle
      , params :: P.Array Handle
      , definitionScope :: Handle
      , bodyScope :: Handle
      }
  | CaseAnswer { binder :: Handle, scrutinees :: P.Array Handle, treeScope :: Handle }
  | SwitchCtorAnswer
      { binder :: Handle
      , branches :: P.Array { scope :: Handle, fields :: P.Array Handle }
      , fallback :: Maybe Handle
      }
  | SwitchLitAnswer { binder :: Handle, branches :: P.Array Handle, fallback :: Handle }
  | SwitchKeyAnswer
      { binder :: Handle
      , branches :: P.Array { scope :: Handle, payload :: Handle }
      , fallback :: Maybe { scope :: Handle, residual :: Handle }
      }
  | HandlerAnswer
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

-- | What drives a conversation.
data Command
  = Kernel KernelRequest
  -- | Open a transaction inside the innermost one.
  | BeginTransaction
  -- | Close the innermost transaction, keeping what was done inside it.
  | CommitTransaction
  -- | End the attempt with the Expr handle given as the goal's result.
  | Finish Handle

-- | A command's answer, where the command leaves the attempt going.
data CommandAnswer
  = KernelAnswered KernelAnswer
  | TransactionBegun TransactionToken
  | TransactionCommitted

derive instance Eq KernelRequest
derive instance Generic KernelRequest _

instance Show KernelRequest where
  show x = genericShow x

derive instance Eq BuildRequest
derive instance Generic BuildRequest _

instance Show BuildRequest where
  show x = genericShow x

derive instance Eq TermRequest
derive instance Generic TermRequest _

instance Show TermRequest where
  show x = genericShow x

derive instance Eq TreeRequest
derive instance Generic TreeRequest _

instance Show TreeRequest where
  show x = genericShow x

derive instance Eq RecordRequest
derive instance Generic RecordRequest _

instance Show RecordRequest where
  show x = genericShow x

derive instance Eq HandlerRequest
derive instance Generic HandlerRequest _

instance Show HandlerRequest where
  show x = genericShow x

derive instance Eq SolveRequest
derive instance Generic SolveRequest _

instance Show SolveRequest where
  show x = genericShow x

derive instance Eq ObserveRequest
derive instance Generic ObserveRequest _

instance Show ObserveRequest where
  show x = genericShow x

derive instance Eq ReportRequest
derive instance Generic ReportRequest _

instance Show ReportRequest where
  show x = genericShow x

derive instance Eq KernelAnswer
derive instance Generic KernelAnswer _

instance Show KernelAnswer where
  show x = genericShow x

derive instance Eq Command
derive instance Generic Command _

instance Show Command where
  show x = genericShow x

derive instance Eq CommandAnswer
derive instance Generic CommandAnswer _

instance Show CommandAnswer where
  show x = genericShow x

-- | The shape of an answer, and nothing it holds.
data AnswerShape
  = UnitShape
  | HandleShape
  | BooleanShape
  | TypeViewShape
  | RowViewShape
  | KindViewShape
  | ContextShape
  | ConstraintsShape
  | DeclShape
  | NamesShape
  | BinderShape
  | AssumptionShape
  | ConstraintAbsShape
  | LetRecShape
  | JoinShape
  | CaseShape
  | SwitchCtorShape
  | SwitchLitShape
  | SwitchKeyShape
  | HandlerShape

answerShape :: KernelAnswer -> AnswerShape
answerShape = case _ of
  UnitAnswer -> UnitShape
  HandleAnswer _ -> HandleShape
  BooleanAnswer _ -> BooleanShape
  TypeViewAnswer _ -> TypeViewShape
  RowViewAnswer _ -> RowViewShape
  KindViewAnswer _ -> KindViewShape
  ContextAnswer _ -> ContextShape
  ConstraintsAnswer _ -> ConstraintsShape
  DeclAnswer _ -> DeclShape
  NamesAnswer _ -> NamesShape
  BinderAnswer _ -> BinderShape
  AssumptionAnswer _ -> AssumptionShape
  ConstraintAbsAnswer _ -> ConstraintAbsShape
  LetRecAnswer _ -> LetRecShape
  JoinAnswer _ -> JoinShape
  CaseAnswer _ -> CaseShape
  SwitchCtorAnswer _ -> SwitchCtorShape
  SwitchLitAnswer _ -> SwitchLitShape
  SwitchKeyAnswer _ -> SwitchKeyShape
  HandlerAnswer _ -> HandlerShape

-- | The shape a request is answered in where it answers: the one table both
-- | the host's answers and a script's operations are held to. `throw` and
-- | `postpone` answer in none.
expectedAnswerShape :: KernelRequest -> Maybe AnswerShape
expectedAnswerShape = case _ of
  BuildRequest r -> Just case r of
    RootScope -> HandleShape
    TypeVariable _ _ -> HandleShape
    TypeConstructor _ _ _ -> HandleShape
    ApplyType _ _ _ -> HandleShape
    EmptyRow _ -> HandleShape
    ExtendRow _ _ _ _ -> HandleShape
    UnionRow _ _ _ -> HandleShape
    OpenForall _ _ _ -> BinderShape
    CloseForall _ _ _ -> HandleShape
    OpenConstraint _ _ -> AssumptionShape
    CloseConstraint _ _ _ -> HandleShape
    InstantiateForall _ _ _ -> HandleShape
    InstantiateScheme _ _ _ -> HandleShape
  TermRequest r -> Just case r of
    LocalVariable _ _ -> HandleShape
    GlobalRef _ _ _ -> HandleShape
    LiteralTerm _ _ -> HandleShape
    TermApply _ _ _ -> HandleShape
    TypeApply _ _ _ -> HandleShape
    ConstraintApply _ _ -> HandleShape
    OpenLambda _ _ _ -> BinderShape
    CloseLambda _ _ _ _ -> HandleShape
    OpenTypeAbs _ _ _ -> BinderShape
    CloseTypeAbs _ _ _ -> HandleShape
    OpenConstraintAbs _ _ -> ConstraintAbsShape
    CloseConstraintAbs _ _ _ -> HandleShape
    OpenLet _ _ _ -> BinderShape
    CloseLet _ _ _ -> HandleShape
    OpenLetRec _ _ -> LetRecShape
    CloseLetRec _ _ _ _ -> HandleShape
    OpenJoin _ _ _ _ -> JoinShape
    CloseJoin _ _ _ _ -> HandleShape
    Jump _ _ _ -> HandleShape
  TreeRequest r -> Just case r of
    OpenCase _ _ -> CaseShape
    CloseCase _ _ _ _ -> HandleShape
    Leaf _ _ -> HandleShape
    Guard _ _ _ _ -> HandleShape
    OpenBind _ _ _ -> BinderShape
    CloseBind _ _ _ -> HandleShape
    RecordField _ _ _ -> HandleShape
    OpenSwitchCtor _ _ _ _ -> SwitchCtorShape
    OpenSwitchLit _ _ _ -> SwitchLitShape
    OpenSwitchKey _ _ _ _ -> SwitchKeyShape
    CloseSwitch _ _ _ _ -> HandleShape
  RecordRequest r -> Just case r of
    RecordEmpty _ -> HandleShape
    RecordExtend _ _ _ _ -> HandleShape
    RecordSelect _ _ _ -> HandleShape
    RecordRestrict _ _ _ -> HandleShape
    RecordUpdate _ _ _ _ -> HandleShape
    RecordMerge _ _ _ -> HandleShape
    VariantInject _ _ _ -> HandleShape
    VariantWeaken _ _ _ _ -> HandleShape
    VariantAbsurd _ _ _ -> HandleShape
    OpenEff _ _ _ -> HandleShape
  HandlerRequest r -> Just case r of
    Perform _ _ _ _ _ _ -> HandleShape
    OpenHandle _ _ _ _ _ _ _ _ -> HandlerShape
    CloseHandle _ _ _ _ _ -> HandleShape
    ReadCell _ _ -> HandleShape
    WriteCell _ _ _ -> HandleShape
  SolveRequest r -> Just case r of
    FreshMetaType _ _ -> HandleShape
    IsAssigned _ -> BooleanShape
    Unify _ _ _ -> UnitShape
    Entails _ _ -> BooleanShape
    Require _ _ -> UnitShape
    Subgoal _ _ _ -> HandleShape
  ObserveRequest r -> Just case r of
    GoalType _ -> HandleShape
    ViewType _ -> TypeViewShape
    Whnf _ -> HandleShape
    NormalizeRow _ -> RowViewShape
    KindOf _ -> KindViewShape
    TypeOf _ -> HandleShape
    LocalContext -> ContextShape
    LocalConstraints -> ConstraintsShape
    LookupGlobal _ -> DeclShape
    DeclsWithAttr _ -> NamesShape
  ReportRequest r -> case r of
    Throw _ -> Nothing
    Warn _ -> Just UnitShape
    Postpone _ -> Nothing

-- | Whether the answer is in the shape the request is answered in.
answersAs :: KernelRequest -> KernelAnswer -> P.Boolean
answersAs request answer = expectedAnswerShape request == Just (answerShape answer)

derive instance Eq AnswerShape
derive instance Ord AnswerShape
derive instance Generic AnswerShape _

instance Show AnswerShape where
  show x = genericShow x
