-- | A tree written without its positions, so that a test can say what shape it
-- | expects in a line.
module Test.Stella.Compiler.CST.Sketch
  ( sketchModule
  , sketchItem
  , sketchDecl
  , sketchType
  , sketchExpr
  , sketchBinder
  ) where

import Prelude
import Prim hiding (Type)

import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Stella.Compiler.CST.Types (Argument(..), AttributeParameter(..), Directive, Macro, QuotePart(..), Token(..), Binder(..), CaseBody(..), Clause(..), Decl(..), DeclKeyword(..), Export(..), Expr(..), Fixity(..), GuardLine(..), HandlerItem(..), HandlerListItem(..), Import(..), ImportItem(..), Item(..), Kind(..), LetBinding(..), Marker(..), Members(..), Module(..), Name, Operator(..), RecordBinder(..), RecordField(..), RowItem(..), Type(..), TypeVarBinding(..), printToken)

list :: Array String -> String
list xs = "(" <> joinWith " " xs <> ")"

name :: Name -> String
name n = case n.qualifier of
  Nothing -> n.name
  Just q -> q <> "." <> n.name

names :: Array Name -> String
names = joinWith "." <<< map name

sketchModule :: Module -> String
sketchModule (Module m) =
  list
    ( [ "module", name m.name ]
        <>
          ( case m.exports of
              Nothing -> []
              Just es -> [ list (map export es) ]
          )
        <> map sketchItem m.items
    )
  where
  export = case _ of
    ExportValue n -> name n
    ExportOperator n -> "(" <> name n <> ")"
    ExportTypeOperator n -> "type (" <> name n <> ")"
    ExportType n ms -> name n <> members ms
    ExportMacro n -> "macro " <> name n
    ExportAttribute n -> "attribute " <> name n
    ExportModule n -> "module " <> name n

members :: Maybe Members -> String
members = case _ of
  Nothing -> ""
  Just MembersAll -> "(..)"
  Just (MembersOnly ns) -> list (map name ns)

sketchItem :: Item -> String
sketchItem = case _ of
  ItemImport (Import i) ->
    list
      ( [ if i.lazy then "import-lazy" else "import", name i.module ]
          <>
            ( case i.names of
                Nothing -> []
                Just is -> [ list (map importItem is) ]
            )
          <>
            ( case i.hiding of
                Nothing -> []
                Just h -> [ "hiding", list (map importItem h.items) ]
            )
          <>
            ( case i.alias of
                Nothing -> []
                Just a -> [ "as", name a ]
            )
      )
  ItemAttribute a -> list ([ "@", name a.name ] <> map argument a.args)
  ItemDirective d -> directive d
  ItemModifier n -> list [ "modifier", name n ]
  ItemDecl d -> sketchDecl d
  ItemMacro m -> macro m
  ItemBroken _ -> "broken"
  where
  importItem = case _ of
    ImportValue n -> name n
    ImportOperator n -> "(" <> name n <> ")"
    ImportTypeOperator n -> "type (" <> name n <> ")"
    ImportType n ms -> name n <> members ms
    ImportMacro n -> "macro " <> name n
    ImportAttribute n -> "attribute " <> name n

directive :: Directive -> String
directive d = list
  ( [ "#" <> name d.name ] <> case d.args of
      Nothing -> []
      Just es -> [ list (map argument es) ]
  )

argument :: Argument -> String
argument = case _ of
  ArgumentPositional e -> sketchExpr e
  ArgumentKeyed k e -> name k <> "=" <> sketchExpr e

-- | A part of a quotation: its tokens as written, the layout's shown by name,
-- | or an antiquotation.
quotePart :: QuotePart -> String
quotePart = case _ of
  QuotedTokens ts -> joinWith " " (map (shown <<< _.value) ts)
  QuotedAntiquote a -> list [ "$", sketchExpr a.expr ]
  where
  shown = case _ of
    TokLayoutStart _ -> "{"
    TokLayoutSep _ -> ";"
    TokLayoutEnd _ -> "}"
    t -> printToken t

macro :: Macro -> String
macro m = list [ name m.name <> "%", joinWith " " (map (printToken <<< _.value) m.body) ]

sketchDecl :: Decl -> String
sketchDecl = case _ of
  DeclSignature n t -> list [ "sig", name n, sketchType t ]
  DeclValue n bs e w ->
    list
      ( [ "value", name n ] <> map sketchBinder bs <> [ sketchExpr e ]
          <> case w of
            Nothing -> []
            Just ls -> [ list ([ "where" ] <> map letBinding ls) ]
      )
  DeclData n vs cs ->
    list ([ "data", name n ] <> map typeVar vs <> map (\c -> list ([ name c.name ] <> map sketchType c.fields)) cs)
  DeclNewtype n vs c t -> list ([ "newtype", name n ] <> map typeVar vs <> [ name c, sketchType t ])
  DeclType n vs t -> list ([ "type", name n ] <> map typeVar vs <> [ sketchType t ])
  DeclKindSignature k n kd -> list [ keyword k, name n, sketchKind kd ]
  DeclEffect n vs os ->
    list ([ "effect", name n ] <> map typeVar vs <> map (\o -> list [ name o.name, sketchType o.type ]) os)
  DeclHandler n ps t is -> list ([ "handler", name n ] <> map sketchBinder ps <> [ sketchType t ] <> map handlerItem is)
  DeclForeign n t -> list [ "foreign", name n, sketchType t ]
  DeclForeignType n k -> list [ "foreign-type", name n, sketchKind k ]
  DeclFixity f p n o -> list [ fixity f, p.raw, name n, name o ]
  DeclTypeFixity f p n o -> list [ fixity f, p.raw, "type", name n, name o ]
  DeclAttribute n ps -> list ([ "attribute", name n ] <> map parameter ps)
  where
  parameter = case _ of
    AttributePositional t -> sketchType t
    AttributeKeyword l t Nothing -> list [ name l, "::", sketchType t ]
    AttributeKeyword l t (Just e) -> list [ name l, "::", sketchType t, "=", sketchExpr e ]
  keyword = case _ of
    KeywordData -> "data-kind"
    KeywordNewtype -> "newtype-kind"
    KeywordType -> "type-kind"
  fixity = case _ of
    Infix -> "infix"
    Infixl -> "infixl"
    Infixr -> "infixr"

typeVar :: TypeVarBinding -> String
typeVar = case _ of
  BindName n -> name n
  BindKinded n k -> list [ "::", name n, sketchKind k ]

sketchKind :: Kind -> String
sketchKind = case _ of
  KindName n -> name n
  KindVar n -> name n
  KindApp f a -> list [ sketchKind f, sketchKind a ]
  KindArrow a b -> list [ "->", sketchKind a, sketchKind b ]
  KindParens k -> sketchKind k

sketchType :: Type -> String
sketchType = case _ of
  TypeVar n -> name n
  TypeConstructor n -> name n
  TypeWildcard _ -> "_"
  TypeHole n -> "?" <> name n
  TypeUnit _ -> "()"
  TypeApp f a -> list [ sketchType f, sketchType a ]
  TypeOp a o b -> list [ name o, sketchType a, sketchType b ]
  TypeArrow a b -> list [ "->", sketchType a, sketchType b ]
  TypeOperationArrow a _ b -> list [ "->*", sketchType a, sketchType b ]
  TypeEffect t _ r -> list [ "/", sketchType t, sketchType r ]
  TypeCapability a b -> list [ "~>", sketchType a, sketchType b ]
  TypeForall vs t -> list ([ "forall" ] <> map typeVar vs <> [ sketchType t ])
  TypeConstrained c t -> list [ "=>", sketchType c, sketchType t ]
  TypeKinded t k -> list [ "::", sketchType t, sketchKind k ]
  TypeParens t -> list [ "parens", sketchType t ]
  TypeTuple ts -> list ([ "tuple" ] <> map sketchType ts)
  TypeRecord _ rs -> list ([ "record" ] <> map rowItem rs)
  TypeEffectRow _ rs -> list ([ "effects" ] <> map rowItem rs)
  TypeVariant _ rs -> list ([ "variant" ] <> map rowItem rs)
  TypeSynthesized n t f -> list [ "synth", maybe "_" name n, sketchType t, "by", name f ]
  TypeDirective d t -> list [ directive d, sketchType t ]
  where
  rowItem = case _ of
    RowField l t -> name l <> "::" <> sketchType t
    RowTag g t -> "'" <> name g <> "::" <> sketchType t
    RowElement t -> sketchType t
    RowSpread _ Nothing -> "..."
    RowSpread _ (Just t) -> "..." <> sketchType t

maybe :: forall a b. b -> (a -> b) -> Maybe a -> b
maybe d f = case _ of
  Nothing -> d
  Just a -> f a

sketchExpr :: Expr -> String
sketchExpr = case _ of
  ExprVar n -> name n
  ExprConstructor n -> name n
  ExprDiscriminator n -> name n <> "?"
  ExprOperatorValue n -> "(" <> name n <> ")"
  ExprTag n -> "'" <> name n
  ExprHole n -> "?" <> name n
  ExprSection _ -> "_"
  ExprBoolean _ b -> show b
  ExprInt l -> l.raw
  ExprNumber l -> l.raw
  ExprChar l -> l.raw
  ExprString l -> l.raw
  ExprUnit _ -> "()"
  ExprParens e -> list [ "parens", sketchExpr e ]
  ExprTuple es -> list ([ "tuple" ] <> map sketchExpr es)
  ExprRecord _ fs -> list ([ "record" ] <> map field fs)
  ExprApp f a -> list [ sketchExpr f, sketchExpr a ]
  ExprOp a o b -> list [ operator o, sketchExpr a, sketchExpr b ]
  ExprTyped e t -> list [ "::", sketchExpr e, sketchType t ]
  ExprAccess e ls -> list [ ".", sketchExpr e, names ls ]
  ExprLambda bs e -> list ([ "\\" ] <> map sketchBinder bs <> [ sketchExpr e ])
  ExprLet ls e -> list ([ "let" ] <> map letBinding ls <> [ sketchExpr e ])
  ExprCase es as -> list ([ "case" ] <> map sketchExpr es <> map alternative as)
  ExprHandle e is -> list ([ "handle", sketchExpr e ] <> map listItem is)
  ExprUsing is e -> list ([ "using" ] <> map listItem is <> [ sketchExpr e ])
  ExprLocalOpen n e -> list [ "open", name n, sketchExpr e ]
  ExprImportIn n e -> list [ "import-in", name n, sketchExpr e ]
  ExprMacro m -> macro m
  ExprQuote q -> list ([ "%" <> q.category.name ] <> map quotePart q.parts)
  ExprAntiquote a -> list [ "$", sketchExpr a.expr ]
  ExprExpanded x -> "(expanded " <> sketchExpr x.expr <> ")"
  ExprInvalid _ -> "(invalid)"
  ExprAt n e -> name n <> "@" <> sketchExpr e
  ExprCellRead n -> name n <> "!"
  ExprCellWrite n e -> list [ ":=", name n, sketchExpr e ]
  ExprResume _ -> "resume"
  where
  operator = case _ of
    OperatorSymbol n -> name n
    OperatorName n -> "`" <> name n <> "`"
  field = case _ of
    FieldValue l e -> name l <> ":" <> sketchExpr e
    FieldPun l -> name l
    FieldUpdate l e -> name l <> "=" <> sketchExpr e
    FieldSpread e -> "..." <> sketchExpr e
  alternative a =
    list
      ( [ joinWith " | " (map (joinWith ", " <<< map sketchBinder) a.patterns) ] <> case a.body of
          Unconditional e -> [ sketchExpr e ]
          GuardBlock gs -> map guardLine gs
      )
  guardLine = case _ of
    GuardBinding b e -> list [ "=", sketchBinder b, sketchExpr e ]
    Guard g e -> list [ "?", sketchExpr g, sketchExpr e ]

letBinding :: LetBinding -> String
letBinding = case _ of
  LetSignature n t -> list [ "sig", name n, sketchType t ]
  LetValue n bs e -> list ([ "=", name n ] <> map sketchBinder bs <> [ sketchExpr e ])
  LetPattern b e -> list [ "=", sketchBinder b, sketchExpr e ]

marker :: Maybe Marker -> Array String
marker = case _ of
  Nothing -> []
  Just Full -> [ "full" ]
  Just Fast -> [ "fast" ]
  Just ReifiableFull -> [ "reifiable full" ]

clause :: Clause -> String
clause = case _ of
  ClauseOperation m n bs e -> list ([ "|" ] <> marker m <> [ name n ] <> map sketchBinder bs <> [ sketchExpr e ])
  ClauseReturn b e -> list [ "| return", sketchBinder b, sketchExpr e ]

handlerItem :: HandlerItem -> String
handlerItem = case _ of
  HandlerCell n e -> list [ "var", name n, sketchExpr e ]
  HandlerClauses m cs -> list ([ "group" ] <> marker m <> map clause cs)

listItem :: HandlerListItem -> String
listItem = case _ of
  ListGroup g ->
    list
      ( [ "group", name g.head ] <> marker g.marker
          <> map (\c -> list [ "var", name c.name, sketchExpr c.value ]) g.cells
          <> map clause g.clauses
      )
  ListHandler e -> sketchExpr e

sketchBinder :: Binder -> String
sketchBinder = case _ of
  BinderWildcard _ -> "_"
  BinderVar n -> name n
  BinderAs n b -> name n <> "@" <> sketchBinder b
  BinderConstructor n [] -> name n
  BinderConstructor n bs -> list ([ name n ] <> map sketchBinder bs)
  BinderTag n [] -> "'" <> name n
  BinderTag n bs -> list ([ "'" <> name n ] <> map sketchBinder bs)
  BinderBoolean _ b -> show b
  BinderInt l -> l.raw
  BinderNumber l -> l.raw
  BinderChar l -> l.raw
  BinderString l -> l.raw
  BinderUnit _ -> "()"
  BinderParens b -> list [ "parens", sketchBinder b ]
  BinderTuple bs -> list ([ "tuple" ] <> map sketchBinder bs)
  BinderOr bs -> list ([ "or" ] <> map sketchBinder bs)
  BinderRecord _ fs -> list ([ "record" ] <> map field fs)
  BinderTyped b t -> list [ "::", sketchBinder b, sketchType t ]
  BinderApp f as -> list ([ "app", sketchBinder f ] <> map sketchBinder as)
  BinderInvalid e -> list [ "invalid", sketchExpr e ]
  where
  field = case _ of
    RecordBinderField l b -> name l <> ":" <> sketchBinder b
    RecordBinderPun l -> name l
    RecordBinderRest _ Nothing -> "..."
    RecordBinderRest _ (Just n) -> "..." <> name n
