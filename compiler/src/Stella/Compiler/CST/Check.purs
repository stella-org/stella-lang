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
import Data.Maybe (Maybe(..))
import Stella.Compiler.CST.Types (Argument(..), AttributeParameter(..), Directive, Binder(..), CaseBody(..), Clause(..), Decl(..), Expr(..), GuardLine(..), HandlerItem(..), HandlerListItem(..), Item(..), LetBinding(..), Module(..), Name, RecordBinder(..), RecordField(..), RowItem(..), SourceRange, Type(..))

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
  -- | `τ / ρ` with no arrow for `/` to belong to, other than at the top of a
  -- | top-level signature.
  | ComputationTypeMisplaced
  -- | A directive this version does not have.
  | DirectiveUnsupported
  -- | `#observ` with an argument other than `none`.
  | DirectiveArgumentsInvalid
  -- | A directive of this version in a type, where none stands.
  | DirectiveInType

derive instance Eq CheckReason

instance Show CheckReason where
  show = case _ of
    OperationArrowOutsideOperation -> "OperationArrowOutsideOperation"
    OperationArrowMisplaced -> "OperationArrowMisplaced"
    OperationArrowMissing -> "OperationArrowMissing"
    ComputationTypeMisplaced -> "ComputationTypeMisplaced"
    DirectiveUnsupported -> "DirectiveUnsupported"
    DirectiveArgumentsInvalid -> "DirectiveArgumentsInvalid"
    DirectiveInType -> "DirectiveInType"

printCheckReason :: CheckReason -> String
printCheckReason = case _ of
  OperationArrowOutsideOperation ->
    "You can put `->*` only in effect operation signatures"
  OperationArrowMisplaced ->
    "An operation's signature should have exactly one `->*`, on the spine of its arrows"
  OperationArrowMissing ->
    "An operation's signature needs exactly one `->*` on the spine of its arrows;\
    \ type synonym is not allowed"
  ComputationTypeMisplaced ->
    "A computation type `τ / ρ` can stand only at the top of a top-level signature;\
    \ write `Unit -> τ / ρ` where a suspended computation is meant"
  DirectiveUnsupported -> "This directive is not supported; the one there is is `#observ(none)`"
  DirectiveArgumentsInvalid -> "`#observ` takes the one argument `none`"
  DirectiveInType -> "This directive cannot stand in a type"

checkModule :: Module -> Array CheckError
checkModule (Module m) = foldMap item m.items

item :: Item -> Array CheckError
item = case _ of
  ItemImport _ -> []
  ItemAttribute a -> foldMap argument a.args
  ItemDirective d -> directive d <> foldMap (foldMap argument) d.args
  ItemModifier _ -> []
  ItemDecl d -> decl d
  ItemMacro _ -> []
  ItemBroken _ -> []
  where
  argument = case _ of
    ArgumentPositional e -> expr e
    ArgumentKeyed _ e -> expr e

decl :: Decl -> Array CheckError
decl = case _ of
  DeclSignature _ t -> signature t
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
  DeclAttribute _ ps -> foldMap parameter ps
  where
  parameter = case _ of
    AttributePositional t -> type_ t
    AttributeKeyword _ t d -> type_ t <> foldMap expr d

-- | An operation's signature: under its quantifiers, a spine of arrows with
-- | exactly one `->*`, arguments to its left, and the resumption type to its
-- | right. Neither side may hold another. The rule is that of first-order
-- | operations.
operationSignature :: { name :: Name, type :: Type } -> Array CheckError
operationSignature op = computationTypes op.type <> typeDirectives op.type <> case spine op.type of
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

-- | A type that is neither an operation's signature nor a top-level
-- | signature, which holds no `->*` and no computation type.
type_ :: Type -> Array CheckError
type_ t = outsideOperation t <> computationTypes t <> typeDirectives t

-- | A top-level signature, which may be a computation type at its top, under
-- | its quantifiers and constraints. Parentheses around the whole of it change
-- | nothing, there being no arrow for them to part it from.
signature :: Type -> Array CheckError
signature t = outsideOperation t <> typeDirectives t <> top t
  where
  top = case _ of
    TypeForall _ body -> top body
    TypeConstrained c body -> computationTypes c <> top body
    TypeParens body -> top body
    TypeEffect a _ r -> computationTypes a <> computationTypes r
    other -> computationTypes other

-- | The directives a type holds, at any depth. None of this version stands in a
-- | type, so one that is well formed is misplaced there.
typeDirectives :: Type -> Array CheckError
typeDirectives = case _ of
  TypeDirective d t -> inType d <> typeDirectives t
  t -> foldMap typeDirectives (subtypes t)
  where
  inType d = case directive d of
    [] -> [ CheckError d.name.range DirectiveInType ]
    errors -> errors

-- | A directive of this version: `#observ(none)` is the one there is. Where it
-- | may stand is decided where declarations are grouped.
directive :: Directive -> Array CheckError
directive d = case d.name.name, d.args of
  "observ", Just [ ArgumentPositional (ExprVar n) ] | n.qualifier == Nothing && n.name == "none" -> []
  "observ", _ -> [ CheckError d.name.range DirectiveArgumentsInvalid ]
  _, _ -> [ CheckError d.name.range DirectiveUnsupported ]

outsideOperation :: Type -> Array CheckError
outsideOperation t = map (\r -> CheckError r OperationArrowOutsideOperation) (operationArrows t)

-- | Where `->*` stands in a type, at any depth.
operationArrows :: Type -> Array SourceRange
operationArrows = case _ of
  TypeOperationArrow a r b -> operationArrows a <> [ r ] <> operationArrows b
  t -> foldMap operationArrows (subtypes t)

-- | Every `τ / ρ` in a type whose `/` belongs to no arrow. A `/` belongs to the
-- | arrow it follows directly; parentheses between the two make the
-- | parenthesized type a computation type of its own.
computationTypes :: Type -> Array CheckError
computationTypes = go false
  where
  go resultOfArrow = case _ of
    TypeEffect a r e ->
      (if resultOfArrow then [] else [ CheckError r ComputationTypeMisplaced ])
        <> go false a
        <> go false e
    TypeArrow a b -> go false a <> go true b
    t -> foldMap (go false) (subtypes t)

-- | The types a type is built from, in the order written.
subtypes :: Type -> Array Type
subtypes = case _ of
  TypeOperationArrow a _ b -> [ a, b ]
  TypeApp f a -> [ f, a ]
  TypeArrow a b -> [ a, b ]
  TypeEffect t _ r -> [ t, r ]
  TypeCapability a b -> [ a, b ]
  TypeForall _ t -> [ t ]
  TypeConstrained c t -> [ c, t ]
  TypeKinded t _ -> [ t ]
  TypeParens t -> [ t ]
  TypeTuple ts -> ts
  TypeRecord _ rs -> foldMap rowItem rs
  TypeEffectRow _ rs -> foldMap rowItem rs
  TypeVariant _ rs -> foldMap rowItem rs
  TypeSynthesized _ t _ -> [ t ]
  TypeDirective _ t -> [ t ]
  TypeVar _ -> []
  TypeConstructor _ -> []
  TypeWildcard _ -> []
  TypeHole _ -> []
  TypeUnit _ -> []
  where
  rowItem = case _ of
    RowField _ t -> [ t ]
    RowTag _ t -> [ t ]
    RowElement t -> [ t ]
    RowSpread _ t -> foldMap pure t

expr :: Expr -> Array CheckError
expr = case _ of
  ExprParens e -> expr e
  ExprTuple es -> foldMap expr es
  ExprRecord _ fs -> foldMap field fs
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
  BinderRecord _ fs -> foldMap recordBinder fs
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
