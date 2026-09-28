-- | The JavaScript the backend prints: a syntax tree of the constructs it emits
-- | and nothing more, and the printer that turns one into text.
-- |
-- | This is the layer every execution strategy shares
-- | ([JavaScript](../../../../../docs/technical-references/05-Backend/05-JavaScript.md)).
-- | It holds no Stella meaning: a strategy's own IR decides what to say, and this
-- | only says it.
module Stella.Compiler.JavaScript.Syntax
  ( Expr(..)
  , Stmt(..)
  , Top(..)
  , Module
  , Case
  , print
  , stringLiteral
  ) where

import Prelude

import Prim as P

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.CodePoints (CodePoint, codePointFromChar)
import Data.String.CodePoints as CodePoints
import Data.Enum (fromEnum)
import Data.Int (hexadecimal, toStringAs)
import Data.Tuple (Tuple(..))

data Expr
  = Ident P.String
  -- | A numeric literal, already written as JavaScript reads it.
  | Number P.String
  | String P.String
  | Boolean P.Boolean
  | Array (P.Array Expr)
  -- | `object.name`, where `name` is an identifier.
  | Member Expr P.String
  | Index Expr Expr
  | Call Expr (P.Array Expr)
  | New Expr (P.Array Expr)
  | Binary P.String Expr Expr
  | Unary P.String Expr
  -- | `(parameters) => body`.
  | Arrow (P.Array P.String) Expr

data Stmt
  = Const P.String Expr
  | Let P.String (Maybe Expr)
  | Assign Expr Expr
  | ExprStmt Expr
  | Return Expr
  | If Expr (P.Array Stmt) (P.Array Stmt)
  | Switch Expr (P.Array Case) (Maybe (P.Array Stmt))
  | Block (P.Array Stmt)
  | Throw Expr
  | Function P.String (P.Array P.String) (P.Array Stmt)

type Case = { label :: Expr, body :: P.Array Stmt }

data Top
  -- | `import { "external" as local, … } from "specifier"`. An external name is
  -- | written as a string, so any name a module exports is importable as it stands.
  = ImportNamed (P.Array (Tuple P.String P.String)) P.String
  -- | `import * as local from "specifier"`.
  | ImportAll P.String P.String
  -- | `export { local as "external", … }`.
  | Export (P.Array (Tuple P.String P.String))
  | Statement Stmt

type Module = P.Array Top

-- Printing -------------------------------------------------------------------------

print :: Module -> P.String
print tops = String.joinWith "\n" (map top tops) <> "\n"

top :: Top -> P.String
top = case _ of
  ImportNamed names from ->
    "import { " <> String.joinWith ", " (map (\(Tuple ext local) -> stringLiteral ext <> " as " <> local) names)
      <> " } from "
      <> stringLiteral from
      <> ";"
  ImportAll local from -> "import * as " <> local <> " from " <> stringLiteral from <> ";"
  Export names ->
    "export { " <> String.joinWith ", " (map (\(Tuple local ext) -> local <> " as " <> stringLiteral ext) names) <> " };"
  Statement s -> String.joinWith "\n" (stmt 0 s)

indent :: P.Int -> P.String
indent n = String.joinWith "" (Array.replicate n "  ")

block :: P.Int -> P.Array Stmt -> P.Array P.String
block n = Array.concatMap (stmt n)

stmt :: P.Int -> Stmt -> P.Array P.String
stmt n = case _ of
  Const name e -> [ indent n <> "const " <> name <> " = " <> expr e <> ";" ]
  Let name Nothing -> [ indent n <> "let " <> name <> ";" ]
  Let name (Just e) -> [ indent n <> "let " <> name <> " = " <> expr e <> ";" ]
  Assign target e -> [ indent n <> expr target <> " = " <> expr e <> ";" ]
  ExprStmt e -> [ indent n <> expr e <> ";" ]
  Return e -> [ indent n <> "return " <> expr e <> ";" ]
  If cond yes no ->
    [ indent n <> "if (" <> expr cond <> ") {" ]
      <> block (n + 1) yes
      <> (if Array.null no then [] else [ indent n <> "} else {" ] <> block (n + 1) no)
      <> [ indent n <> "}" ]
  Switch scrutinee cases default ->
    [ indent n <> "switch (" <> expr scrutinee <> ") {" ]
      <> Array.concatMap
        ( \c ->
            [ indent (n + 1) <> "case " <> expr c.label <> ": {" ]
              <> block (n + 2) c.body
              <> [ indent (n + 1) <> "}" ]
        )
        cases
      <>
        ( case default of
            Nothing -> []
            Just body -> [ indent (n + 1) <> "default: {" ] <> block (n + 2) body <> [ indent (n + 1) <> "}" ]
        )
      <> [ indent n <> "}" ]
  Block body -> [ indent n <> "{" ] <> block (n + 1) body <> [ indent n <> "}" ]
  Throw e -> [ indent n <> "throw " <> expr e <> ";" ]
  Function name params body ->
    [ indent n <> "function " <> name <> "(" <> String.joinWith ", " params <> ") {" ]
      <> block (n + 1) body
      <> [ indent n <> "}" ]

-- | Every compound expression is parenthesized, so no precedence table is needed
-- | and none can be got wrong.
expr :: Expr -> P.String
expr = case _ of
  Ident name -> name
  Number text -> text
  String text -> stringLiteral text
  Boolean b -> if b then "true" else "false"
  Array es -> "[" <> String.joinWith ", " (map expr es) <> "]"
  Member e name -> atom e <> "." <> name
  Index e i -> atom e <> "[" <> expr i <> "]"
  Call f args -> atom f <> "(" <> String.joinWith ", " (map expr args) <> ")"
  New f args -> "new " <> atom f <> "(" <> String.joinWith ", " (map expr args) <> ")"
  Binary op l r -> "(" <> expr l <> " " <> op <> " " <> expr r <> ")"
  Unary op e -> "(" <> op <> atom e <> ")"
  Arrow params body -> "((" <> String.joinWith ", " params <> ") => " <> expr body <> ")"

-- | An expression standing where a member access or a call applies to it.
atom :: Expr -> P.String
atom e = case e of
  Number _ -> "(" <> expr e <> ")"
  _ -> expr e

-- | A JavaScript string literal holding exactly the text given.
-- |
-- | What a line would swallow or act on is escaped, the two line terminators
-- | JavaScript reads inside a literal among them. The text holds scalar values
-- | only (D27), so no lone surrogate reaches here.
stringLiteral :: P.String -> P.String
stringLiteral text = "\"" <> String.joinWith "" (map escape (CodePoints.toCodePointArray text)) <> "\""
  where
  escape :: CodePoint -> P.String
  escape cp
    | cp == codePointFromChar '"' = "\\\""
    | cp == codePointFromChar '\\' = "\\\\"
    | cp == codePointFromChar '\n' = "\\n"
    | cp == codePointFromChar '\r' = "\\r"
    | cp == codePointFromChar '\t' = "\\t"
    | fromEnum cp < 0x20 || fromEnum cp == 0x7F || fromEnum cp == 0x2028 || fromEnum cp == 0x2029 =
        "\\u{" <> toStringAs hexadecimal (fromEnum cp) <> "}"
    | otherwise = CodePoints.singleton cp
