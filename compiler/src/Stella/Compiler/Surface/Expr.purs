-- | Expressions, patterns, and handlers of the Surface AST.
-- |
-- | **Every name is resolved, and what it refers to is told by the node.** A
-- | reference to a value and one to a computation are different nodes, and so
-- | are a constructor, an operation, and a discriminator; what else is known of
-- | the entity — its scheme, its arity, the type a constructor builds — is read
-- | from the module's environment and the interfaces, so no node carries it.
-- |
-- | **The tree is expanded and desugared.** It holds no macro call, no local
-- | open, no parenthesis, no anonymous argument `_`, and no operator chain
-- | waiting for its fixity: an operator is an application of the operator to
-- | its two operands, rebracketed already. The handling forms `handle e with`
-- | and `using … handle e` are one node, and the marker a clause takes is the one
-- | in effect for it, a group's marker and the default resolved.
module Stella.Compiler.Surface.Expr
  ( Expr(..)
  , exprOrigin
  , RecordField(..)
  , LetBinding(..)
  , Alternative
  , AlternativeBody(..)
  , GuardLine(..)
  , Binder(..)
  , binderOrigin
  , RecordBinderField
  , RecordRest
  , HandlerItem(..)
  , Group
  , HandlerBody
  , CellDeclaration
  , OperationClause
  , ClauseForm(..)
  , ReturnClause
  ) where

import Prelude
import Prim hiding (Type, Symbol)

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Stella.Compiler.Surface.Name (CellVar, LocalVar)
import Stella.Compiler.Surface.Origin (Origin)
import Stella.Compiler.Surface.Type (Signature, Type)
import Stella.Compiler.TypedCore.Name (EffName, Ident, Qualified, Symbol, Tag)
import Stella.Compiler.TypedCore.Term (Literal)

data Expr
  = ExprLocal Origin LocalVar
  -- | A top-level value, a foreign, or a handler.
  | ExprValue Origin (Qualified Ident)
  -- | A computation declaration, which runs each time it is referred to
  -- | (proposal 05).
  | ExprComputation Origin (Qualified Ident)
  -- | A data constructor. `()` is `Prim.Unit`.
  | ExprConstructor Origin (Qualified Ident)
  -- | An operation of an effect, called as an ordinary function (D17). The
  -- | label is that of the instance it is performed on, `get@cache`.
  | ExprOperation Origin (Qualified Ident) (Maybe Symbol)
  -- | `C?`, the predicate that holds of a value built with the constructor `C`.
  | ExprDiscriminator Origin (Qualified Ident)
  -- | `'Ok`, injecting its argument into a variant at that tag.
  | ExprTag Origin Tag
  | ExprLiteral Origin Literal
  -- | `?name`, a typed hole. `?_` holds `_`.
  | ExprHole Origin String
  | ExprApp Origin Expr Expr
  -- | An operator applied to its two operands: the operator, then the operands.
  -- | The operator is the reference it stands for, with the origin of where it
  -- | was written.
  | ExprOperator Origin Expr Expr Expr
  | ExprTyped Origin Expr Type
  -- | `e.label`, one label at a time.
  | ExprSelect Origin Expr Symbol
  | ExprTuple Origin (Array Expr)
  | ExprRecord Origin (Array RecordField)
  -- | A lambda over irrefutable patterns.
  | ExprLambda Origin (Array Binder) Expr
  -- | A `let` block, and also what a declaration's `where` is.
  | ExprLet Origin (Array LetBinding) Expr
  | ExprCase Origin (Array Expr) (Array Alternative)
  -- | A handling expression: the handlers installed from the first, outermost,
  -- | to the last, and the computation they handle.
  | ExprHandle Origin (Array HandlerItem) Expr
  | ExprCellRead Origin CellVar
  | ExprCellWrite Origin CellVar Expr
  -- | `resume`, which reaches the continuation of the `full` clause it stands in.
  | ExprResume Origin
  -- | Where resolution reported an error.
  | ExprInvalid Origin

exprOrigin :: Expr -> Origin
exprOrigin = case _ of
  ExprLocal o _ -> o
  ExprValue o _ -> o
  ExprComputation o _ -> o
  ExprConstructor o _ -> o
  ExprOperation o _ _ -> o
  ExprDiscriminator o _ -> o
  ExprTag o _ -> o
  ExprLiteral o _ -> o
  ExprHole o _ -> o
  ExprApp o _ _ -> o
  ExprOperator o _ _ _ -> o
  ExprTyped o _ _ -> o
  ExprSelect o _ _ -> o
  ExprTuple o _ -> o
  ExprRecord o _ -> o
  ExprLambda o _ _ -> o
  ExprLet o _ _ -> o
  ExprCase o _ _ -> o
  ExprHandle o _ _ -> o
  ExprCellRead o _ -> o
  ExprCellWrite o _ _ -> o
  ExprResume o -> o
  ExprInvalid o -> o

-- | A field of a record literal. A pun `{ x }` is the field `x: x`.
data RecordField
  = FieldValue Origin Symbol Expr
  -- | `name = e`, replacing a field the spread record has.
  | FieldUpdate Origin Symbol Expr
  -- | `...e`, which stands last.
  | FieldSpread Origin Expr

-- | A binding of a `let` block or a `where`, its signature joined to it.
data LetBinding
  -- | A value, or a local function where it has parameters.
  = LetValue
      { origin :: Origin
      , var :: LocalVar
      , signature :: Maybe (Signature Type)
      , params :: Array Binder
      , body :: Expr
      }
  -- | An irrefutable pattern bound to a value.
  | LetPattern
      { origin :: Origin
      , binder :: Binder
      , body :: Expr
      }

-- | An alternative of a `case`. Each row holds one pattern per scrutinee, and
-- | the alternative is taken where any row matches.
type Alternative =
  { origin :: Origin
  , patterns :: Array (Array Binder)
  , body :: AlternativeBody
  }

data AlternativeBody
  = Unconditional Expr
  -- | A guard block, its lines in the order written. Where every guard fails,
  -- | matching falls through to the next alternative.
  | Guarded (Array GuardLine)

data GuardLine
  = GuardBinding Origin Binder Expr
  | GuardWhen Origin Expr Expr
  -- | `otherwise -> e`, a guard that always succeeds.
  | GuardOtherwise Origin Expr

data Binder
  = BinderWildcard Origin
  | BinderVar Origin LocalVar
  | BinderAs Origin LocalVar Binder
  -- | A constructor and a pattern for each field. `()` is `Prim.Unit`.
  | BinderConstructor Origin (Qualified Ident) (Array Binder)
  -- | A tag, and a pattern for its payload where one is written.
  | BinderTag Origin Tag (Maybe Binder)
  | BinderLiteral Origin Literal
  | BinderTuple Origin (Array Binder)
  | BinderRecord Origin (Array RecordBinderField) (Maybe RecordRest)
  -- | An or-pattern, which binds no variable.
  | BinderOr Origin (Array Binder)
  | BinderTyped Origin Binder Type
  -- | Where resolution reported an error.
  | BinderInvalid Origin

binderOrigin :: Binder -> Origin
binderOrigin = case _ of
  BinderWildcard o -> o
  BinderVar o _ -> o
  BinderAs o _ _ -> o
  BinderConstructor o _ _ -> o
  BinderTag o _ _ -> o
  BinderLiteral o _ -> o
  BinderTuple o _ -> o
  BinderRecord o _ _ -> o
  BinderOr o _ -> o
  BinderTyped o _ _ -> o
  BinderInvalid o -> o

-- | A field of a record pattern. A pun `{ x }` is the field `x: x`.
type RecordBinderField =
  { origin :: Origin
  , label :: Symbol
  , binder :: Binder
  }

-- | `...` or `...rest`, the fields a record pattern does not name.
type RecordRest =
  { origin :: Origin
  , var :: Maybe LocalVar
  }

-- | An item of a handling expression.
data HandlerItem
  -- | A handler, which is a function applied to the thunk of what it handles.
  = HandlerApplied Expr
  -- | A group written in place.
  | HandlerGroup Group

-- | A group of clauses written in place. A group headed by a label handles that
-- | instance of the effect its operations belong to; one headed by an effect
-- | handles the element the effect keys.
type Group =
  { origin :: Origin
  , label :: Maybe Symbol
  , effect :: Qualified EffName
  , body :: HandlerBody
  }

-- | What a handler holds, whether it is declared or written in place: its
-- | cells, its operation clauses, and its return clause where it has one.
type HandlerBody =
  { cells :: Array CellDeclaration
  , operations :: Array OperationClause
  , return :: Maybe ReturnClause
  }

-- | `var x := e`.
type CellDeclaration =
  { origin :: Origin
  , cell :: CellVar
  , initial :: Expr
  }

-- | A clause for one operation: a pattern for each of its arguments, and the
-- | body.
type OperationClause =
  { origin :: Origin
  , operation :: Qualified Ident
  , form :: ClauseForm
  , arguments :: Array Binder
  , body :: Expr
  }

-- | What becomes of the continuation (D28).
data ClauseForm
  -- | Not captured; the body has the type the operation resumes with.
  = ClauseFast
  -- | Captured, and reached by `resume` in the clause's immediate body.
  | ClauseFull
  -- | Captured, and taken as a value by the pattern given, the clause's last
  -- | parameter.
  | ClauseReifiable Binder

type ReturnClause =
  { origin :: Origin
  , binder :: Binder
  , body :: Expr
  }

derive instance Eq Expr
derive instance Generic Expr _

instance Show Expr where
  show x = genericShow x

derive instance Eq RecordField
derive instance Generic RecordField _

instance Show RecordField where
  show x = genericShow x

derive instance Eq LetBinding
derive instance Generic LetBinding _

instance Show LetBinding where
  show x = genericShow x

derive instance Eq AlternativeBody
derive instance Generic AlternativeBody _

instance Show AlternativeBody where
  show x = genericShow x

derive instance Eq GuardLine
derive instance Generic GuardLine _

instance Show GuardLine where
  show x = genericShow x

derive instance Eq Binder
derive instance Generic Binder _

instance Show Binder where
  show x = genericShow x

derive instance Eq HandlerItem
derive instance Generic HandlerItem _

instance Show HandlerItem where
  show x = genericShow x

derive instance Eq ClauseForm
derive instance Generic ClauseForm _

instance Show ClauseForm where
  show x = genericShow x
