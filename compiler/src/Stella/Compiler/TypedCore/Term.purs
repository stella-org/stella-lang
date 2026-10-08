-- | Terms, handlers, and decision trees of Typed Core.
-- |
-- | Every node carries an annotation `a`, which the specification fixes as a
-- | source span. Spans have no influence on type checking or semantics, so the
-- | parameter is free: `Unit` erases them, a span type keeps them.
module Stella.Compiler.TypedCore.Term
  ( Literal(..)
  , Expr(..)
  , Param
  , Binding
  , Handler
  , Cell
  , ReturnClause
  , OpClause(..)
  , opClauseOp
  , opClauseBody
  , Occurrence(..)
  , DecisionTree(..)
  , CtorBranch
  , LitBranch
  , KeyBranch
  , exprAnnotation
  , withAnnotation
  ) where

import Prelude

import Prim as P

import Stella.Compiler.TypedCore.Domain (ScalarString, ScalarValue, compareNumber, sameNumber)
import Stella.Compiler.TypedCore.Kind (Kind)
import Stella.Compiler.TypedCore.Name (Ident, JoinName, OpName, Qualified, RegionName, TyVar)
import Stella.Compiler.TypedCore.Type (Constraint, RowEntry, RowKey, TyBinder, Type)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)

-- | A literal. There is no array literal and no record literal: arrays are a
-- | type constructor with primitives, and records are built by iterating
-- | `RecordExtend`.
-- |
-- | Every domain is fixed (D27, D37), and a `Char` carries a Unicode scalar
-- | value rather than a code unit ([Domain](Domain.purs)).
data Literal
  = LitInt P.Int
  | LitNumber P.Number
  | LitString ScalarString
  | LitChar ScalarValue
  | LitBoolean P.Boolean

-- | A Core term, written `e`.
-- |
-- | `fail τ` is absent: it is derived notation for
-- | `perform Partial.abort [τ] Prim.Unit` (D10). So is surface `do`, and so are
-- | implicit arguments, which elaboration turns into ordinary ones (D11).
data Expr a
  -- | A local variable, introduced by a binder.
  = Var a Ident
  -- | A global name with its kind scheme instantiated, `M.x [[κ̄]]`. Data
  -- | constructors and foreigns are reached through this form.
  | Global a (Qualified Ident) (P.Array Kind)
  | Lit a Literal
  | Lam a Ident Type (Expr a)
  | App a (Expr a) (Expr a)
  -- | Type abstraction, `Λ (a : κ). v`. The body is a value form, which is what
  -- | makes the abstraction erasable.
  | TyLam a TyVar Kind (Expr a)
  | TyApp a (Expr a) Type
  -- | Constraint abstraction, `Λ (_ : C). v`, erased at run time.
  | ConstraintLam a Constraint (Expr a)
  -- | Constraint application, `e [•]`, carrying no proof term.
  | ConstraintApp a (Expr a)
  | Let a Ident Type (Expr a) (Expr a)
  -- | A recursive binding group. Each right-hand side is guarded, that is,
  -- | syntactically a function value (D14).
  | LetRec a (P.Array (Binding a)) (Expr a)
  -- | A match over a scrutinee vector, dispatching through a decision tree (D9).
  | Case a (P.Array (Expr a)) (DecisionTree a)
  -- | `letjoin j (x̄ : τ̄) : τ = e1 in e2`. The result type is written: it is
  -- | the type of the whole expression and of every `jump` to `j`, and nothing
  -- | in the two bodies determines it ahead of the other.
  | LetJoin a JoinName (P.Array Param) Type (Expr a) (Expr a)
  -- | A jump to a join point, which occurs in tail position only.
  | Jump a JoinName (P.Array (Expr a))
  | RecordEmpty a
  | RecordExtend a RowKey (Expr a) (Expr a)
  | RecordSelect a RowKey (Expr a)
  | RecordRestrict a RowKey (Expr a)
  -- | `update k e1 e2`, where `e1` is the record and `e2` the value it takes at `k`
  -- | `extend` writes them the other way about, the value first.
  | RecordUpdate a RowKey (Expr a) (Expr a)
  | RecordMerge a (Expr a) (Expr a)
  | VariantInject a RowKey (Expr a)
  | VariantWeaken a RowKey Type (Expr a)
  | VariantAbsurd a Type (Expr a)
  -- | Invocation of an operation, `perform k.op [τ̄] e`. It requires the ambient
  -- | effect row to have `k` as a key, not a handler to be installed. The
  -- | operation's signature comes from the effect the payload at `k` names.
  | Perform a RowKey OpName (P.Array Type) (Expr a)
  -- | `handle e with h`.
  | Handle a (Expr a) (Handler a)
  -- | `region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e` (D36): open a region of cells named
  -- | `ℓ`, one per cell of the layout, holding the initial values `ē` in the
  -- | order the layout writes them, and evaluate `e` in it. `ℓ` is bound in `e`
  -- | alone; the layout and the initial values stand outside it.
  | Region a RegionName (P.Array Cell) (P.Array (Expr a)) (Expr a)
  -- | `readCell ℓ.k` and `writeCell ℓ.k e`, reaching the cell `k` of the region
  -- | named `ℓ`.
  | ReadCell a RegionName RowKey
  | WriteCell a RegionName RowKey (Expr a)
  -- | Effect widening, `openEff [ρ] e`, which is the identity at run time.
  -- | Containment is an explicit term rather than subtyping (D8).
  | OpenEff a Type (Expr a)

-- | A binder together with its type.
type Param =
  { name :: Ident
  , ty :: Type
  }

type Binding a =
  { name :: Ident
  , ty :: Type
  , value :: Expr a
  }

-- | A handler of one element of the effect row.
-- |
-- | The element is written whole. Its key selects which element of the row the
-- | `handle` removes, and its payload names the effect whose operations the
-- | clauses must exhaust — the row being handled is not written anywhere else,
-- | so neither is recoverable from the other.
-- |
-- | The clauses exhaust the operations because `handle` removes the element,
-- | leaving an operation without a clause nowhere to go.
type Handler a =
  { element :: RowEntry
  , returnClause :: ReturnClause a
  , opClauses :: P.Array (OpClause a)
  }

-- | One cell of a region's layout, `k : σ`. A layout is a written sequence and
-- | therefore closed, which is what lets the initial values be given one per
-- | cell.
type Cell =
  { key :: RowKey
  , ty :: Type
  }

type ReturnClause a =
  { binder :: Ident
  , ty :: Type
  , body :: Expr a
  }

-- | A clause for one operation, in one of the two forms Core provides (D28).
-- |
-- | `tyBinders` binds the operation's own type parameters, which a handler must
-- | respect. There is no unmarked form: which of the two a surface clause means
-- | is settled before it reaches Core, so the form is available to the checker,
-- | to reduction, and to a backend without any analysis.
-- |
-- | A `FullClause` binds the continuation, of type `τ' -{ρ}-> β` where `β` is
-- | the result of the `handle` and `ρ` the row outside it: resuming returns
-- | under the same handler, which is what makes handlers deep (D15). Its body
-- | has type `β`, so the clause supplies what the `handle` returns.
-- |
-- | A `FastClause` binds none, and its body has the type the operation resumes
-- | with. Such a clause cannot bypass the evaluation still to come in order to
-- | supply the answer, and has no continuation to invoke zero or several times.
-- | This bounds the clause and not the program around it: where its body
-- | performs an operation of `ρ` whose `full` handler resumes more than once,
-- | that handler's continuation runs the rest of the handled computation again.
data OpClause a
  = FullClause
      { op :: OpName
      , tyBinders :: P.Array TyBinder
      , argBinder :: Param
      , contBinder :: Param
      , body :: Expr a
      }
  | FastClause
      { op :: OpName
      , tyBinders :: P.Array TyBinder
      , argBinder :: Param
      , body :: Expr a
      }

opClauseOp :: forall a. OpClause a -> OpName
opClauseOp = case _ of
  FullClause c -> c.op
  FastClause c -> c.op

opClauseBody :: forall a. OpClause a -> Expr a
opClauseBody = case _ of
  FullClause c -> c.body
  FastClause c -> c.body

-- | A path from a scrutinee, written `o`.
-- |
-- | Occurrences are projections and have no effects, so one may be referenced
-- | any number of times within a tree.
data Occurrence
  -- | The i-th scrutinee, 0-origin.
  = OccScrutinee P.Int
  -- | The j-th field of a constructor, `o ! Ctor . j`.
  | OccField Occurrence (Qualified Ident) P.Int
  -- | The element of a record at a key, `o . k`.
  | OccRecordField Occurrence RowKey
  -- | The payload a variant carries at a key, `o ? k`.
  | OccVariantPayload Occurrence RowKey

-- | A decision tree, written `dt`.
-- |
-- | Every `Switch*` is a single dispatch whose branches are mutually exclusive,
-- | so their written order carries no meaning. `Guard` is the one sequential
-- | test; fall-through is expressed by placing a `Jump` in its else branch.
data DecisionTree a
  = Leaf (Expr a)
  | Bind Ident Occurrence (DecisionTree a)
  | SwitchCtor Occurrence (P.Array (CtorBranch a)) (Maybe (DecisionTree a))
  -- | Literals cannot be exhausted, so the default is mandatory rather than
  -- | optional.
  | SwitchLit Occurrence (P.Array (LitBranch a)) (DecisionTree a)
  -- | Dispatch on the key a variant carries. In the default branch the
  -- | occurrence takes the residual variant type, with the enumerated keys
  -- | removed.
  | SwitchKey Occurrence (P.Array (KeyBranch a)) (Maybe (DecisionTree a))
  | Guard (Expr a) (DecisionTree a) (DecisionTree a)

type CtorBranch a =
  { ctor :: Qualified Ident
  , tree :: DecisionTree a
  }

type LitBranch a =
  { lit :: Literal
  , tree :: DecisionTree a
  }

type KeyBranch a =
  { key :: RowKey
  , tree :: DecisionTree a
  }

exprAnnotation :: forall a. Expr a -> a
exprAnnotation = case _ of
  Var a _ -> a
  Global a _ _ -> a
  Lit a _ -> a
  Lam a _ _ _ -> a
  App a _ _ -> a
  TyLam a _ _ _ -> a
  TyApp a _ _ -> a
  ConstraintLam a _ _ -> a
  ConstraintApp a _ -> a
  Let a _ _ _ _ -> a
  LetRec a _ _ -> a
  Case a _ _ -> a
  LetJoin a _ _ _ _ _ -> a
  Jump a _ _ -> a
  RecordEmpty a -> a
  RecordExtend a _ _ _ -> a
  RecordSelect a _ _ -> a
  RecordRestrict a _ _ -> a
  RecordUpdate a _ _ _ -> a
  RecordMerge a _ _ -> a
  VariantInject a _ _ -> a
  VariantWeaken a _ _ _ -> a
  VariantAbsurd a _ _ -> a
  Perform a _ _ _ _ -> a
  Handle a _ _ -> a
  Region a _ _ _ _ -> a
  ReadCell a _ _ -> a
  WriteCell a _ _ _ -> a
  OpenEff a _ _ -> a

-- | Replace the annotation of the outermost node, leaving those beneath it as
-- | they are. `map` reaches every node; this one reaches the root.
withAnnotation :: forall a. a -> Expr a -> Expr a
withAnnotation a = case _ of
  Var _ x -> Var a x
  Global _ name kinds -> Global a name kinds
  Lit _ literal -> Lit a literal
  Lam _ x ty body -> Lam a x ty body
  App _ f x -> App a f x
  TyLam _ name kind body -> TyLam a name kind body
  TyApp _ e ty -> TyApp a e ty
  ConstraintLam _ c body -> ConstraintLam a c body
  ConstraintApp _ e -> ConstraintApp a e
  Let _ x ty value body -> Let a x ty value body
  LetRec _ bindings body -> LetRec a bindings body
  Case _ scrutinees dt -> Case a scrutinees dt
  LetJoin _ j params result value body -> LetJoin a j params result value body
  Jump _ j args -> Jump a j args
  RecordEmpty _ -> RecordEmpty a
  RecordExtend _ key value rest -> RecordExtend a key value rest
  RecordSelect _ key e -> RecordSelect a key e
  RecordRestrict _ key e -> RecordRestrict a key e
  RecordUpdate _ key rec value -> RecordUpdate a key rec value
  RecordMerge _ left right -> RecordMerge a left right
  VariantInject _ key value -> VariantInject a key value
  VariantWeaken _ key ty e -> VariantWeaken a key ty e
  VariantAbsurd _ ty e -> VariantAbsurd a ty e
  Perform _ key op tyArgs arg -> Perform a key op tyArgs arg
  Handle _ body handler -> Handle a body handler
  Region _ name cells initial body -> Region a name cells initial body
  ReadCell _ name key -> ReadCell a name key
  WriteCell _ name key value -> WriteCell a name key value
  OpenEff _ row e -> OpenEff a row e

-- | **Literal identity is equality of the value** (D37), which `switchLit`
-- | requires to be decidable: its branches are distinct literals
-- | ([Terms and Matching](../../../../docs/technical-references/03-Typed-Core/04-Terms-and-Matching.md)).
-- | For a `Number` that is not IEEE equality, which identifies the two zeros and
-- | separates a NaN from itself, so the instance is written out rather than
-- | derived ([Domain](Domain.purs)).
instance Eq Literal where
  eq = case _, _ of
    LitInt a, LitInt b -> a == b
    LitNumber a, LitNumber b -> sameNumber a b
    LitString a, LitString b -> a == b
    LitChar a, LitChar b -> a == b
    LitBoolean a, LitBoolean b -> a == b
    _, _ -> false

-- | A total order agreeing with the identity above, which is what lets a literal
-- | stand in a set. The order between two constructors is the order they are
-- | written in and carries no meaning of its own.
instance Ord Literal where
  compare = case _, _ of
    LitInt a, LitInt b -> compare a b
    LitNumber a, LitNumber b -> compareNumber a b
    LitString a, LitString b -> compare a b
    LitChar a, LitChar b -> compare a b
    LitBoolean a, LitBoolean b -> compare a b
    a, b -> compare (rank a) (rank b)
    where
    rank = case _ of
      LitInt _ -> 0
      LitNumber _ -> 1
      LitString _ -> 2
      LitChar _ -> 3
      LitBoolean _ -> 4

derive instance Generic Literal _

instance Show Literal where
  show = genericShow

derive instance Eq a => Eq (Expr a)
derive instance Functor Expr
derive instance Generic (Expr a) _

instance Show a => Show (Expr a) where
  show x = genericShow x

derive instance Eq a => Eq (OpClause a)
derive instance Functor OpClause
derive instance Generic (OpClause a) _

instance Show a => Show (OpClause a) where
  show c = genericShow c

derive instance Eq Occurrence
derive instance Ord Occurrence
derive instance Generic Occurrence _

instance Show Occurrence where
  show x = genericShow x

derive instance Eq a => Eq (DecisionTree a)
derive instance Functor DecisionTree
derive instance Generic (DecisionTree a) _

instance Show a => Show (DecisionTree a) where
  show x = genericShow x
