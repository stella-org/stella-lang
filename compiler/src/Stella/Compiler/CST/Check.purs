-- | Concrete syntax well-formedness check
module Stella.Compiler.CST.Check
  ( CheckError(..)
  , CheckReason(..)
  , checkModule
  , printCheckReason
  ) where

import Prelude
import Prim hiding (Type)

import Data.Foldable (foldMap)
import Stella.Compiler.CST.Types (AttributeArg(..), Binder(..), CaseBody(..), Clause(..), Decl(..), Expr(..), GuardLine(..), HandlerItem(..), HandlerListItem(..), Item(..), LetBinding(..), Module(..), Name, RecordBinder(..), RecordField(..), RowItem(..), SourceRange, Type(..))

data CheckError = CheckError SourceRange CheckReason

derive instance Eq CheckError

instance Show CheckError where
  show (CheckError r reason) =
    "CheckError " <> show r.start.line <> ":" <> show r.start.column <> " " <> printCheckReason reason

data CheckReason
  -- | `->*` in a type that is not an operation's signature.
  = OperationArrowOutsideOperation
  -- | A `->*` in an operation's signature off the spine of its arrows
  | OperationArrowMisplaced
  -- | An operation's signature with no `->*`
  | OperationArrowMissing

derive instance Eq CheckReason

instance Show CheckReason where
  show = case _ of
    OperationArrowOutsideOperation -> "OperationArrowOutsideOperation"
    OperationArrowMisplaced -> "OperationArrowMisplaced"
    OperationArrowMissing -> "OperationArrowMissing"

printCheckReason :: CheckReason -> String
printCheckReason = case _ of
  OperationArrowOutsideOperation ->
    "You can put `->*` only in effect operation signatures"
  OperationArrowMisplaced ->
    "An operation's signature should have exactly one `->*`, on the spine of its arrows"
  OperationArrowMissing ->
    "An operation's signature needs exactly one `->*` on the spine of its arrows;\
    \ type synonym is not allowed"

checkModule :: Module -> Array CheckError
checkModule (Module m) = foldMap item m.items

item :: Item -> Array CheckError
item = case _ of
  ItemImport _ -> []
  ItemAttribute a -> foldMap attributeArg a.args
  ItemDirective d -> foldMap (foldMap expr) d.args
  ItemModifier _ -> []
  ItemDecl d -> decl d
  ItemMacro _ -> []
  ItemBroken _ -> []
  where
  attributeArg = case _ of
    AttributePositional e -> expr e
    AttributeKeyed _ e -> expr e

decl :: Decl -> Array CheckError
decl = case _ of
  DeclSignature _ t -> type_ t
  DeclValue _ bs e w -> foldMap binder bs <> expr e <> foldMap (foldMap letBinding) w
  DeclData _ _ cs -> foldMap (foldMap type_ <<< _.fields) cs
  DeclNewtype _ _ _ t -> type_ t
  DeclType _ _ t -> type_ t
  DeclKindSignature _ _ _ -> []
  DeclEffect _ _ os -> foldMap operationSignature os
  DeclHandler _ ps t is -> foldMap binder ps <> type_ t <> foldMap handlerItem is
  DeclForeign _ t -> type_ t
  DeclForeignType _ _ -> []
  DeclFixity _ _ _ _ -> []

-- | An operation's signature: under its quantifiers, a spine of arrows with
-- | exactly one `->*`, arguments to its left, and the resumption type to its
-- | right. Neither side may hold another. The rule is that of first-order
-- | operations.
operationSignature :: { name :: Name, type :: Type } -> Array CheckError
operationSignature op = case spine op.type of
  { found: false, misplaced: [] } -> [ CheckError op.name.range OperationArrowMissing ]
  { misplaced } -> map (\r -> CheckError r OperationArrowMisplaced) misplaced
  where
  -- Whether the spine holds its `->*`, and where every other one stands. A
  -- signature whose `->*` stands in the wrong place is reported there, and not
  -- also as missing one. Parentheses around the rest of the spine change
  -- nothing, arrows associating to the right.
  spine = case _ of
    TypeForall _ t -> spine t
    TypeParens t -> spine t
    TypeArrow a b -> let rest = spine b in rest { misplaced = operationArrows a <> rest.misplaced }
    TypeOperationArrow a _ b -> { found: true, misplaced: operationArrows a <> operationArrows b }
    t -> { found: false, misplaced: operationArrows t }

-- | A type that is not an operation's signature, which holds no `->*`.
type_ :: Type -> Array CheckError
type_ t = map (\r -> CheckError r OperationArrowOutsideOperation) (operationArrows t)

-- | Where `->*` stands in a type, at any depth.
operationArrows :: Type -> Array SourceRange
operationArrows = case _ of
  TypeOperationArrow a r b -> operationArrows a <> [ r ] <> operationArrows b
  TypeApp f a -> operationArrows f <> operationArrows a
  TypeArrow a b -> operationArrows a <> operationArrows b
  TypeEffect t r -> operationArrows t <> operationArrows r
  TypeCapability a b -> operationArrows a <> operationArrows b
  TypeForall _ t -> operationArrows t
  TypeConstrained c t -> operationArrows c <> operationArrows t
  TypeKinded t _ -> operationArrows t
  TypeParens t -> operationArrows t
  TypeTuple ts -> foldMap operationArrows ts
  TypeRecord rs -> foldMap rowItem rs
  TypeEffectRow rs -> foldMap rowItem rs
  TypeVariant rs -> foldMap rowItem rs
  TypeSynthesized _ t _ -> operationArrows t
  TypeDirective _ t -> operationArrows t
  TypeVar _ -> []
  TypeConstructor _ -> []
  TypeWildcard _ -> []
  TypeHole _ -> []
  TypeUnit _ -> []
  where
  rowItem = case _ of
    RowField _ t -> operationArrows t
    RowTag _ t -> operationArrows t
    RowElement t -> operationArrows t
    RowSpread _ t -> foldMap operationArrows t

expr :: Expr -> Array CheckError
expr = case _ of
  ExprParens e -> expr e
  ExprTuple es -> foldMap expr es
  ExprArray es -> foldMap expr es
  ExprRecord fs -> foldMap field fs
  ExprApp f a -> expr f <> expr a
  ExprOp a _ b -> expr a <> expr b
  ExprTyped e t -> expr e <> type_ t
  ExprAccess e _ -> expr e
  ExprLambda bs e -> foldMap binder bs <> expr e
  ExprLet ls e -> foldMap letBinding ls <> expr e
  ExprCase es as -> foldMap expr es <> foldMap alternative as
  ExprHandle e is -> expr e <> foldMap listItem is
  ExprUsing is e -> foldMap listItem is <> expr e
  ExprLocalOpen _ e -> expr e
  ExprImportIn _ e -> expr e
  ExprAt _ e -> expr e
  ExprCellWrite _ e -> expr e
  _ -> []
  where
  field = case _ of
    FieldValue _ e -> expr e
    FieldPun _ -> []
    FieldUpdate _ e -> expr e
    FieldSpread e -> expr e
  alternative a =
    foldMap (foldMap binder) a.patterns <> case a.body of
      Unconditional e -> expr e
      GuardBlock gs -> foldMap guardLine gs
  guardLine = case _ of
    GuardBinding b e -> binder b <> expr e
    Guard g e -> expr g <> expr e

letBinding :: LetBinding -> Array CheckError
letBinding = case _ of
  LetSignature _ t -> type_ t
  LetValue _ bs e -> foldMap binder bs <> expr e
  LetPattern b e -> binder b <> expr e

binder :: Binder -> Array CheckError
binder = case _ of
  BinderAs _ b -> binder b
  BinderConstructor _ bs -> foldMap binder bs
  BinderTag _ bs -> foldMap binder bs
  BinderParens b -> binder b
  BinderTuple bs -> foldMap binder bs
  BinderOr bs -> foldMap binder bs
  BinderRecord fs -> foldMap recordBinder fs
  BinderTyped b t -> binder b <> type_ t
  BinderApp f as -> binder f <> foldMap binder as
  BinderInvalid e -> expr e
  _ -> []
  where
  recordBinder = case _ of
    RecordBinderField _ b -> binder b
    _ -> []

clause :: Clause -> Array CheckError
clause = case _ of
  ClauseOperation _ _ bs e -> foldMap binder bs <> expr e
  ClauseReturn b e -> binder b <> expr e

handlerItem :: HandlerItem -> Array CheckError
handlerItem = case _ of
  HandlerCell _ e -> expr e
  HandlerClauses _ cs -> foldMap clause cs

listItem :: HandlerListItem -> Array CheckError
listItem = case _ of
  ListGroup g -> foldMap (expr <<< _.value) g.cells <> foldMap clause g.clauses
  ListHandler e -> expr e
