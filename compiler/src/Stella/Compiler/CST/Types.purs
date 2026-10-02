-- | The tokens of the surface syntax, as the lexer produces them and the layout
-- | pass extends them.
module Stella.Compiler.CST.Types
  ( SourcePos
  , SourceRange
  , SourceToken
  , Token(..)
  , StringStyle(..)
  , Qualifier
  , keywords
  , isKeyword
  , printToken
  , Name
  , Literal
  , Module(..)
  , Export(..)
  , Members(..)
  , Import(..)
  , ImportItem(..)
  , Item(..)
  , Attribute
  , Argument(..)
  , Directive
  , Macro
  , DeclKeyword(..)
  , Fixity(..)
  , Decl(..)
  , AttributeParameter(..)
  , DataCtor
  , OperationSignature
  , TypeVarBinding(..)
  , Kind(..)
  , Type(..)
  , RowItem(..)
  , Operator(..)
  , Expr(..)
  , RecordField(..)
  , LetBinding(..)
  , CaseAlternative
  , CaseBody(..)
  , GuardLine(..)
  , Binder(..)
  , RecordBinder(..)
  , Marker(..)
  , HandlerItem(..)
  , Clause(..)
  , HandlerListItem(..)
  ) where

import Prelude

-- The tree has a `Type` of its own, and an explicit import of `Prim` replaces
-- the implicit one.
import Prim hiding (Type)

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

import Data.Array as Array
import Data.Maybe (Maybe(..))

-- | A position in the source. Lines count from 1; columns count UTF-16 code
-- | units from 1, which is what an editor protocol counts.
type SourcePos = { line :: Int, column :: Int }

-- | The first position a token covers and the position just after it.
type SourceRange = { start :: SourcePos, end :: SourcePos }

-- | A token with where it stands. `spaceBefore` records whether whitespace or a
-- | comment separates it from the token before it, which is what the rules
-- | depending on adjacency read.
type SourceToken =
  { range :: SourceRange
  , spaceBefore :: Boolean
  , value :: Token
  }

-- | The module part of a qualified name, `Data.Array` in `Data.Array.length`.
type Qualifier = Maybe String

data StringStyle = Quoted | Block

derive instance Eq StringStyle

instance Show StringStyle where
  show = case _ of
    Quoted -> "Quoted"
    Block -> "Block"

data Token
  = TokLeftParen
  | TokRightParen
  | TokLeftSquare
  | TokRightSquare
  | TokLeftBrace
  | TokRightBrace
  -- | `{|`, opening an effect row.
  | TokLeftBar
  -- | `|}`, closing an effect row.
  | TokRightBar
  -- | `{{`, opening a synthesized argument. It closes with two `}`.
  | TokLeftSynth
  -- | `@[`, opening an attribute.
  | TokLeftAttribute
  -- | `M.(`, opening a local open of the module `M`.
  | TokLocalOpen String
  | TokComma
  | TokBackslash
  | TokUnderscore
  -- | A name beginning with a lower case letter or `_`. A keyword is lexed as
  -- | one too; the grammar tells keywords apart.
  | TokLowerName Qualifier String
  | TokUpperName Qualifier String
  -- | `C?`, the discriminator of the constructor `C`.
  | TokDiscriminator Qualifier String
  -- | A run of operator characters, reserved spellings included.
  | TokOperator Qualifier String
  -- | `(++)`, an operator as a value.
  | TokOperatorValue Qualifier String
  -- | `` `rem` ``, a name used infix.
  | TokInfixName Qualifier String
  -- | `?name` or `?_`.
  | TokHole String
  -- | `'Ok`.
  | TokTag String
  -- | `#inline`. The flag says that an argument list follows immediately.
  | TokDirective String Boolean
  -- | `format%`, the name of a macro called on the bracket or string after it.
  | TokMacro Qualifier String
  -- | The source text and the value.
  | TokInt String Int
  | TokNumber String Number
  | TokChar String String
  | TokString StringStyle String String
  -- | Inserted by the layout pass: a block opens at the column given, an item
  -- | of the innermost block begins, and the innermost block closes.
  | TokLayoutStart Int
  | TokLayoutSep Int
  | TokLayoutEnd Int

derive instance Eq Token

instance Show Token where
  show = case _ of
    TokInt raw n -> "(TokInt " <> show raw <> " " <> show n <> ")"
    TokNumber raw n -> "(TokNumber " <> show raw <> " " <> show n <> ")"
    TokChar raw v -> "(TokChar " <> show raw <> " " <> show v <> ")"
    TokString style raw v -> "(TokString " <> show style <> " " <> show raw <> " " <> show v <> ")"
    TokDirective name args -> "(TokDirective " <> show name <> " " <> show args <> ")"
    TokLayoutStart n -> "(TokLayoutStart " <> show n <> ")"
    TokLayoutSep n -> "(TokLayoutSep " <> show n <> ")"
    TokLayoutEnd n -> "(TokLayoutEnd " <> show n <> ")"
    tok -> "`" <> printToken tok <> "`"

keywords :: Array String
keywords =
  [ "module"
  , "where"
  , "import"
  , "data"
  , "newtype"
  , "type"
  , "effect"
  , "handler"
  , "foreign"
  , "attribute"
  , "infix"
  , "infixl"
  , "infixr"
  , "let"
  , "in"
  , "case"
  , "of"
  , "forall"
  , "handle"
  , "with"
  , "using"
  , "full"
  , "fast"
  , "reifiable"
  , "resume"
  , "var"
  , "true"
  , "false"
  ]

isKeyword :: String -> Boolean
isKeyword name = Array.elem name keywords

qualified :: Qualifier -> String -> String
qualified = case _ of
  Nothing -> identity
  Just q -> \name -> q <> "." <> name

-- | The token as it would be written. Layout tokens, which nothing writes, are
-- | described instead.
printToken :: Token -> String
printToken = case _ of
  TokLeftParen -> "("
  TokRightParen -> ")"
  TokLeftSquare -> "["
  TokRightSquare -> "]"
  TokLeftBrace -> "{"
  TokRightBrace -> "}"
  TokLeftBar -> "{|"
  TokRightBar -> "|}"
  TokLeftSynth -> "{{"
  TokLeftAttribute -> "@["
  TokLocalOpen q -> q <> ".("
  TokComma -> ","
  TokBackslash -> "\\"
  TokUnderscore -> "_"
  TokLowerName q name -> qualified q name
  TokUpperName q name -> qualified q name
  TokDiscriminator q name -> qualified q name <> "?"
  TokOperator q op -> qualified q op
  TokOperatorValue q op -> qualified q ("(" <> op <> ")")
  TokInfixName q name -> "`" <> qualified q name <> "`"
  TokHole name -> "?" <> name
  TokTag name -> "'" <> name
  TokDirective name _ -> "#" <> name
  TokMacro q name -> qualified q name <> "%"
  TokInt raw _ -> raw
  TokNumber raw _ -> raw
  TokChar raw _ -> raw
  TokString _ raw _ -> raw
  TokLayoutStart _ -> "the start of a block"
  TokLayoutSep _ -> "the start of a new line"
  TokLayoutEnd _ -> "the end of a block"

-- The concrete syntax tree.
--
-- It keeps what was written, in the shape it was written: operators stand in
-- the order they appeared, before fixity rebrackets them; parentheses are kept;
-- an attribute, a directive and a modifier are items of their own, attached to
-- the declaration after them later; and whatever the grammar reads widely --
-- the patterns of a case alternative, the left of a `let` binding -- is kept as
-- read. Checking what may stand where is the next stage's.

-- | A name as written, with its qualifier if it had one.
type Name = { range :: SourceRange, qualifier :: Qualifier, name :: String }

-- | A literal: its source text and its value.
type Literal a = { range :: SourceRange, raw :: String, value :: a }

data Module = Module
  { name :: Name
  , exports :: Maybe (Array Export)
  , items :: Array Item
  }

data Export
  = ExportValue Name
  | ExportOperator Name
  | ExportType Name (Maybe Members)
  | ExportMacro Name
  | ExportAttribute Name
  | ExportModule Name

-- | The members listed after a type name: `(..)`, or some of them. A data
-- | type's members are its constructors and an effect's its operations.
data Members
  = MembersAll
  | MembersOnly (Array Name)

data Import = Import
  { lazy :: Boolean
  , module :: Name
  , names :: Maybe (Array ImportItem)
  , alias :: Maybe Name
  }

data ImportItem
  = ImportValue Name
  | ImportOperator Name
  | ImportType Name (Maybe Members)
  | ImportMacro Name
  | ImportAttribute Name

data Item
  = ItemImport Import
  | ItemAttribute Attribute
  | ItemDirective Directive
  -- | `implicit`, before a handler declaration.
  | ItemModifier Name
  | ItemDecl Decl
  -- | A macro called at a declaration's position.
  | ItemMacro Macro
  -- | What the parser could not read, up to the next item.
  | ItemBroken (Maybe SourceToken)

-- | `@[name arg …]`. The name is that of an attribute, qualified or not,
-- | `TC.instance`.
type Attribute = { range :: SourceRange, name :: Name, args :: Array Argument }

-- | An argument of an attribute or a directive.
data Argument
  = ArgumentPositional Expr
  | ArgumentKeyed Name Expr

-- | `#name` or `#name(arg, …)`.
type Directive = { name :: Name, args :: Maybe (Array Argument) }

-- | A macro and the tokens it is called on, its brackets included.
type Macro = { name :: Name, body :: Array SourceToken }

data DeclKeyword
  = KeywordData
  | KeywordNewtype
  | KeywordType

data Fixity
  = Infix
  | Infixl
  | Infixr

data Decl
  = DeclSignature Name Type
  | DeclValue Name (Array Binder) Expr (Maybe (Array LetBinding))
  | DeclData Name (Array TypeVarBinding) (Array DataCtor)
  | DeclNewtype Name (Array TypeVarBinding) Name Type
  | DeclType Name (Array TypeVarBinding) Type
  | DeclKindSignature DeclKeyword Name Kind
  | DeclEffect Name (Array TypeVarBinding) (Array OperationSignature)
  | DeclHandler Name (Array Binder) Type (Array HandlerItem)
  | DeclForeign Name Type
  | DeclForeignType Name Kind
  | DeclFixity Fixity (Literal Int) Name Name
  -- | `attribute name τ … (label :: τ) … (label :: τ = c) …`.
  | DeclAttribute Name (Array AttributeParameter)

-- | A parameter of an attribute declaration: positional, written as its type,
-- | or keyword, with its default if it has one.
data AttributeParameter
  = AttributePositional Type
  | AttributeKeyword Name Type (Maybe Expr)

type DataCtor = { name :: Name, fields :: Array Type }

type OperationSignature = { name :: Name, type :: Type }

data TypeVarBinding
  = BindName Name
  | BindKinded Name Kind

data Kind
  = KindName Name
  | KindVar Name
  | KindApp Kind Kind
  | KindArrow Kind Kind
  | KindParens Kind

data Type
  = TypeVar Name
  | TypeConstructor Name
  | TypeWildcard SourceRange
  | TypeHole Name
  | TypeUnit SourceRange
  | TypeApp Type Type
  | TypeArrow Type Type
  -- | `τ ->* σ`, in the signature of an operation, with where the `->*` stands.
  | TypeOperationArrow Type SourceRange Type
  -- | `τ / ρ`, with where the `/` stands.
  | TypeEffect Type SourceRange Type
  -- | `E ~> ρ`, the shape of a capability translation.
  | TypeCapability Type Type
  | TypeForall (Array TypeVarBinding) Type
  | TypeConstrained Type Type
  | TypeKinded Type Kind
  | TypeParens Type
  | TypeTuple (Array Type)
  -- | A row in its brackets, which the range covers: `{ … }`, `{| … |}`, and
  -- | `[ … ]`.
  | TypeRecord SourceRange (Array RowItem)
  | TypeEffectRow SourceRange (Array RowItem)
  | TypeVariant SourceRange (Array RowItem)
  -- | `{{ name :: τ by f }}`.
  | TypeSynthesized (Maybe Name) Type Name
  | TypeDirective Directive Type

data RowItem
  = RowField Name Type
  | RowTag Name Type
  | RowElement Type
  | RowSpread SourceRange (Maybe Type)

data Operator
  = OperatorSymbol Name
  -- | A name used infix, `` `rem` ``.
  | OperatorName Name

data Expr
  = ExprVar Name
  | ExprConstructor Name
  | ExprDiscriminator Name
  | ExprOperatorValue Name
  | ExprTag Name
  | ExprHole Name
  -- | `_`, an anonymous argument.
  | ExprSection SourceRange
  | ExprBoolean SourceRange Boolean
  | ExprInt (Literal Int)
  | ExprNumber (Literal Number)
  | ExprChar (Literal String)
  | ExprString (Literal String)
  | ExprUnit SourceRange
  | ExprParens Expr
  | ExprTuple (Array Expr)
  -- | A record literal; the range covers its braces.
  | ExprRecord SourceRange (Array RecordField)
  | ExprApp Expr Expr
  -- | Operators in the order written; fixity is applied later.
  | ExprOp Expr Operator Expr
  | ExprTyped Expr Type
  | ExprAccess Expr (Array Name)
  | ExprLambda (Array Binder) Expr
  | ExprLet (Array LetBinding) Expr
  | ExprCase (Array Expr) (Array CaseAlternative)
  | ExprHandle Expr (Array HandlerListItem)
  | ExprUsing (Array HandlerListItem) Expr
  | ExprLocalOpen Name Expr
  | ExprImportIn Name Expr
  | ExprMacro Macro
  -- | `name@atom`: an operation of a labelled effect, `get@cache`, and in a
  -- | guard block the as-pattern a binding's left may be, `m@(Just x)`.
  | ExprAt Name Expr
  | ExprCellRead Name
  | ExprCellWrite Name Expr
  | ExprResume SourceRange

data RecordField
  = FieldValue Name Expr
  | FieldPun Name
  -- | `name = e`, replacing a field.
  | FieldUpdate Name Expr
  | FieldSpread Expr

data LetBinding
  = LetSignature Name Type
  | LetValue Name (Array Binder) Expr
  | LetPattern Binder Expr

type CaseAlternative =
  { patterns :: Array (Array Binder)
  , body :: CaseBody
  }

data CaseBody
  = Unconditional Expr
  | GuardBlock (Array GuardLine)

data GuardLine
  = GuardBinding Binder Expr
  | Guard Expr Expr

data Binder
  = BinderWildcard SourceRange
  | BinderVar Name
  | BinderAs Name Binder
  | BinderConstructor Name (Array Binder)
  | BinderTag Name (Array Binder)
  | BinderBoolean SourceRange Boolean
  | BinderInt (Literal Int)
  | BinderNumber (Literal Number)
  | BinderChar (Literal String)
  | BinderString (Literal String)
  | BinderUnit SourceRange
  | BinderParens Binder
  | BinderTuple (Array Binder)
  | BinderOr (Array Binder)
  -- | A record pattern; the range covers its braces.
  | BinderRecord SourceRange (Array RecordBinder)
  | BinderTyped Binder Type
  -- | Atoms side by side with no constructor at their head: the left of a
  -- | local function binding, `f x y`, and nothing a pattern may be.
  | BinderApp Binder (Array Binder)
  -- | An expression read where a pattern was meant, that is none.
  | BinderInvalid Expr

data RecordBinder
  = RecordBinderField Name Binder
  | RecordBinderPun Name
  | RecordBinderRest SourceRange (Maybe Name)

data Marker
  = Full
  | Fast
  -- | `reifiable full`: the clause takes the continuation as its last parameter,
  -- | a value it may keep beyond the clause.
  | ReifiableFull

-- | An item of a handler declaration's block.
data HandlerItem
  = HandlerCell Name Expr
  | HandlerClauses (Maybe Marker) (Array Clause)

data Clause
  = ClauseOperation (Maybe Marker) Name (Array Binder) Expr
  | ClauseReturn Binder Expr

-- | An item of `handle … with` or `using … handle`.
data HandlerListItem
  = ListGroup
      { head :: Name
      , marker :: Maybe Marker
      , cells :: Array { name :: Name, value :: Expr }
      , clauses :: Array Clause
      }
  | ListHandler Expr

derive instance Generic Module _
derive instance Generic Export _
derive instance Generic Members _
derive instance Generic Import _
derive instance Generic ImportItem _
derive instance Generic Item _
derive instance Generic Argument _
derive instance Generic DeclKeyword _
derive instance Generic Fixity _
derive instance Generic Decl _
derive instance Generic AttributeParameter _
derive instance Generic TypeVarBinding _
derive instance Generic Kind _
derive instance Generic Type _
derive instance Generic RowItem _
derive instance Generic Operator _
derive instance Generic Expr _
derive instance Generic RecordField _
derive instance Generic LetBinding _
derive instance Generic CaseBody _
derive instance Generic GuardLine _
derive instance Generic Binder _
derive instance Generic RecordBinder _
derive instance Generic Marker _
derive instance Generic HandlerItem _
derive instance Generic Clause _
derive instance Generic HandlerListItem _

instance Show Module where
  show x = genericShow x

instance Show Export where
  show x = genericShow x

instance Show Members where
  show x = genericShow x

instance Show Import where
  show x = genericShow x

instance Show ImportItem where
  show x = genericShow x

instance Show Item where
  show x = genericShow x

instance Show Argument where
  show x = genericShow x

instance Show DeclKeyword where
  show x = genericShow x

instance Show Fixity where
  show x = genericShow x

instance Show Decl where
  show x = genericShow x

instance Show AttributeParameter where
  show x = genericShow x

instance Show TypeVarBinding where
  show x = genericShow x

instance Show Kind where
  show x = genericShow x

instance Show Type where
  show x = genericShow x

instance Show RowItem where
  show x = genericShow x

instance Show Operator where
  show x = genericShow x

instance Show Expr where
  show x = genericShow x

instance Show RecordField where
  show x = genericShow x

instance Show LetBinding where
  show x = genericShow x

instance Show CaseBody where
  show x = genericShow x

instance Show GuardLine where
  show x = genericShow x

instance Show Binder where
  show x = genericShow x

instance Show RecordBinder where
  show x = genericShow x

instance Show Marker where
  show x = genericShow x

instance Show HandlerItem where
  show x = genericShow x

instance Show Clause where
  show x = genericShow x

instance Show HandlerListItem where
  show x = genericShow x

derive instance Eq Module
derive instance Eq Export
derive instance Eq Members
derive instance Eq Import
derive instance Eq ImportItem
derive instance Eq Item
derive instance Eq Argument
derive instance Eq DeclKeyword
derive instance Eq Fixity
derive instance Eq Decl
derive instance Eq AttributeParameter
derive instance Eq TypeVarBinding
derive instance Eq Kind
derive instance Eq Type
derive instance Eq RowItem
derive instance Eq Operator
derive instance Eq Expr
derive instance Eq RecordField
derive instance Eq LetBinding
derive instance Eq CaseBody
derive instance Eq GuardLine
derive instance Eq Binder
derive instance Eq RecordBinder
derive instance Eq Marker
derive instance Eq HandlerItem
derive instance Eq Clause
derive instance Eq HandlerListItem
