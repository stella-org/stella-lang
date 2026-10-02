# Syntax

This document settles how tokens become the concrete syntax tree: the offside rule, and the grammar. The tokens are those of [Lexical Structure](04-Lexical-Structure.md).

Three passes turn text into the tree and a fourth checks it, each a module of `Stella.Compiler.CST`:

| Pass | Module | Does |
| --- | --- | --- |
| lexing | `Lexer` | text to tokens |
| layout | `Layout` | inserts the block tokens indentation calls for |
| parsing | `Parser` | tokens to the tree of `Types` |
| checking | `Check` | what the grammar reads widely, against what the language admits |

**The parser is generated.** Its grammar is `Parser.pursy`, an LR(1) grammar that Puppy compiles to the `Parser` module. The grammar below is that file's, written without its semantic actions; where the two differ, the file is right.

## The concrete syntax tree

**The tree keeps what was written, in the shape it was written.** Operators stand in the order they appeared, before any fixity is applied. Parentheses are kept. An attribute, a directive, and a modifier are items of their own, to be attached to the declaration after them. What the grammar reads widely — the patterns of an alternative, the left of a `let` binding, the left of a binding in a guard block — is kept as read.

**Checking what may stand where is not the parser's.** The grammar admits more than the language does wherever the difference is not a matter of shape, or where a check can say what is wrong better than a token the parser did not expect can. `Check` holds the checks that need nothing but the tree, and reports every place one fails; the rest belong to name resolution and elaboration.

| Admitted by the grammar | Rejected later |
| --- | --- |
| any pattern in a binding position | a pattern that can fail ([Pattern Matching](../../proposals/03-Pattern-Matching-Syntax.md)) |
| an or-pattern binding a variable | a binding or-pattern |
| `import lazy M` without `as`, or with a list | a lazy import that is not qualified and implicit |
| a member of either case after any type name | one the declaration does not have: a constructor of a data type, an operation of an effect |
| `module N` in any export list | the module naming itself, `module M (module M) where` |
| `->*` wherever an arrow may stand | `->*` outside an effect's operation signature; an operation signature without exactly one on its spine, or with one inside an argument or the resumption type (`Check`) |
| any atom as an attribute's value — unparenthesized, an argument is one atom, so `@[a f x]` has two | anything but a literal, a name, or a record or array of those |
| any integer literal as a precedence | one written other than as decimal digits: `-1`, `1_0`, `0x10` |
| `name@atom` with any atom after the `@` | in an expression, anything but an unqualified name after it, `op@label`; the wider form stands for an as-pattern on the left of a guard block's binding, and an `@` not taken as one there is checked for this |
| any upper case name in a kind | a name other than `Type`, `Effect`, `Row` |
| a computation type anywhere a type stands | a computation type other than at the top of a top-level signature |
| `resume` anywhere | `resume` outside the immediate body of a `full` clause |
| any parameters in a `reifiable full` clause | a clause with no parameter after the operation's arguments, which is the continuation it keeps |
| a `reifiable full` clause in any module | one in a module that does not import `Base.Continuation`, which its desugaring depends on |
| an attribute, a directive, or a modifier with no declaration after it | the same |
| `implicit` before any item | one before anything but a handler declaration or a macro call, which keeps it |
| an import anywhere among the items | one after a declaration |
| a signature, or a kind signature, anywhere | one not followed directly by the definition of its name, or the declaration of its keyword and name |

## Layout

**Indentation is turned into block tokens before parsing, from the tokens alone.** The grammar then matches `{`, `;` and `}` that nobody wrote — written here as `VOPEN`, `VSEP` and `VCLOSE` — as it would explicit braces and semicolons. The rule follows PureScript's, which the tokens settle without asking the parser.

### Blocks

**A block opens after `where`, `let`, `of`, `with`, and `using`, at the column of the token that follows.** It opens only where that column is to the right of the block it stands in; otherwise nothing opens.

**Within a block, a token at its column on a later line begins a new item**, and a `VSEP` is inserted before it. **A token to the left of its column closes it**, and a `VCLOSE` is inserted. Whatever is still open at the end of the input is closed there.

```stella
module M where
f x = g x
  where
  g y = y
h = 1
```

```text
module M where { f x = g x where { g y = y } ; h = 1 }
```

### What closes a block early

- **`in` closes the `let` block it belongs to**, together with every block opened inside it: `let x = 1 in x`.
- **`handle` closes the `using` block it belongs to** the same way: `using runA handle w`.
- **`)`, `]`, and `}` close every block opened inside the bracket.**
- **A comma closes every block opened since the nearest bracket**, which is what lets a block stand inside a list.
- **An operator closes every block whose column it does not stand to the right of**, so that a line continuing an expression can begin with one. `|` is the exception: it begins a handler clause, which may stand at the column of its block, and closes only a block whose column is to its right.
- **`->` closes every block whose column it does not stand to the right of**, except a case block.

### Case alternatives and guard blocks

**The alternatives of a case form a block.** While the patterns of an alternative are read, a comma separates patterns rather than closing anything, and `->` ends them.

**`where` after the patterns of an alternative opens a guard block** instead of closing anything, and its lines are items of that block.

```stella
case _ of
  n where
      m = n `rem` 3 == 0
      m -> "Fizz"
  n -> show n
```

```text
case _ of { n where { m = n `rem` 3 == 0 ; m -> "Fizz" } ; n -> show n }
```

A `where` anywhere else closes every block whose column it does not stand to the right of, and opens the block of a declaration's `where`.

### Handler clauses

**The clauses of a group may stand at the column of the block they are in**, each then an item of its own, or **further right**, continuing the item before them:

```stella
handle work with
  State full | get _ -> resume 0
             | set _ -> resume ()
  runToStdout
```

```text
handle work with { State full | get _ -> resume 0 | set _ -> resume () ; runToStdout }
```

### Where no block opens

- **A keyword standing as a record label opens nothing**: after `{`, `{|`, `{{`, a comma inside one of them, and a `.` of field access. `{ type: 1, where: 2 }.where` holds no block.
- **A keyword directly inside an attribute opens nothing**, being the attribute's name or a label of its arguments: `@[where]`, `@[foo where=1]`. Inside a bracket nested in the attribute the rule is the ordinary one.
- **Inside a macro's bracket nothing is inserted at all.** The tokens after `name%` up to the matching bracket pass through as they were lexed, and the macro receives them with their positions.

## Notation

The grammar below writes a terminal in capitals or quoted, `x?` for an optional `x`, `x*` and `x+` for repetition, `sep(x, s)` for one or more `x` separated by `s`, and `block(x)` for `VOPEN sep(x, VSEP) VCLOSE`.

## Names

```text
ident     ::= LOWER | "as" | "lazy" | "return" | "by" | "implicit" | "macro"
qualIdent ::= ident | QUAL_LOWER
properName     ::= UPPER
qualProperName ::= UPPER | QUAL_UPPER
moduleName     ::= UPPER | QUAL_UPPER
label     ::= ident | "var" | any keyword
operatorName ::= OPERATOR | QUAL_OPERATOR | "/"
```

**The words of the second list in [Keywords](04-Lexical-Structure.md#keywords) are names wherever the grammar does not give them a meaning**, and `ident` says which. **A record label may be any word, a keyword included.** Two words are narrower than the rest:

- **`var` is reserved.** A group in a handling expression may declare a cell after its head, `State var n := 0 | …`, where a name would otherwise read as an argument of an application.
- **`by` is not a type variable**, since it closes a synthesized argument, `{{ d :: Show a by f }}`, where a type application would otherwise take it.

## Modules

```text
module     ::= "module" moduleName exports? "where" block(item)?
exports    ::= "(" sep(export, ",") ")"
export     ::= qualIdent | OPVALUE | properName members? | "macro" ident | "module" moduleName
members    ::= "(..)" | "(" ")" | "(" sep(memberName, ",") ")"
memberName ::= properName | ident

import     ::= "import" "lazy"? moduleName importList? ("as" moduleName)?
importList ::= "(" ")" | "(" sep(importItem, ",") ")"
importItem ::= ident | OPVALUE | properName members? | "macro" ident
```

`(..)` is the token `..` as an operator value ([Lexical Structure](04-Lexical-Structure.md)), which after a type name means every member: every constructor of a data type, or every operation of an effect. A member named alone may be of either case, an operation being lower case, and which one it must be follows from the declaration ([Name Resolution](06-Name-Resolution.md)). `macro m` names a macro, which is spelled as a value is.

### Items

```text
item ::= import
       | decl
       | macroCall
       | attribute item?
       | directive item?
       | "implicit" handlerDecl?
       | ERROR
```

**An attribute, a directive, and a modifier are items of their own**, standing on a line before the declaration they belong to or on the same line ahead of it. The modifier `implicit` stands only before a handler declaration ([Effect Handlers](02-Effect-Handlers.md)).

- **They join the declaration after them, which is their prefix.** A declaration given a signature has its prefix from before the signature and from before the definition alike, in the order written, so a prefix may stand between the two. Where the definition does not follow, the prefix before the signature goes with the signature, and to nothing after it.
- **A signature is followed directly by the definition of its name**, and a kind signature by the declaration of its keyword and name: `data T :: Type -> Type` then `data T a = …`.
- **The imports come before every declaration**, a signature counting as the start of one, so that the header, which the dependencies are read from, is the top of the module (D22).
- **A macro called at a declaration's position keeps the prefix before it as a unit with it.** What an attribute there means is the macro's to settle, and nothing in the prefix passes on to the declarations an expansion produces or to the one after the call.

**Where the parser carries on past an error, an item it cannot read is skipped up to the next item** and stands in the tree as a broken one, so that everything else in the module is still read. The generated parser has an entry point that does so beside the one that stops at the first error.

```text
attribute ::= "@[" sep(label, ".") attributeArg* "]"
attributeArg ::= exprAtom | label "=" exprAtom
directive ::= DIRECTIVE | DIRECTIVE "(" sep(exprAtom, ",")? ")"
macroCall ::= MACRO tokenTree
```

- **An attribute's name may be dotted**: `@[typeclass.instance]`.
- **An argument is positional, or keyed by `name=value`**: `@[synthesizedBy Typeclass.resolve]`, `@[entrypoint runner=myrunner]`.
- **A directive's arguments are the parenthesis that follows it with no space**, `#observ(none)`.

### Macro calls

**A macro is called on one bracket and everything inside it, or on one string.** The tree keeps the tokens, the brackets included, for the macro to read.

```text
tokenTree ::= "(" tokenTreeItem* ")" | "M.(" tokenTreeItem* ")"
            | "[" tokenTreeItem* "]" | "@[" tokenTreeItem* "]"
            | "{" tokenTreeItem* "}" | "{|" tokenTreeItem* "|}"
            | "{{" tokenTreeItem* "}" "}"
            | STRING
tokenTreeItem ::= tokenTree | any token but a bracket
```

A macro call stands where an expression does, and where an item does: `format%"{n}"`, `class%{ … }`.

## Declarations

```text
decl ::= ident "::" type
       | ident binderAtom* "=" expr ("where" block(letBinding))?
       | "data" properName typeVarBinding* ("=" "|"? sep(dataCtor, "|"))?
       | "newtype" properName typeVarBinding* "=" properName typeAtom
       | "type" properName typeVarBinding* "=" type
       | ("data" | "newtype" | "type") properName "::" kind
       | "effect" properName typeVarBinding* "where" block(ident "::" type)
       | handlerDecl
       | "foreign" ident "::" type
       | "foreign" "type" properName "::" kind
       | ("infix" | "infixl" | "infixr") INT (qualIdent | qualProperName) "as" operatorName

dataCtor ::= properName typeAtom*
typeVarBinding ::= typeVar | "(" typeVar "::" kind ")"
typeVar        ::= any ident but "by"
```

- **A function is defined by one equation**, its parameters written as pattern atoms ([Pattern Matching](../../proposals/03-Pattern-Matching-Syntax.md)).
- **A constructor list may begin with `|`**, so that constructors on lines of their own align.
- **A kind or a type is given to a declared name by a signature of its own**, never inline: `type T :: Type`, not `type (T :: Type)`. A parameter is a binder and may carry one: `data Proxy (a :: k) = Proxy`.
- **An operation's type has exactly one `->*` on its spine, and no other type has one** (D21), which `Check` confirms, the grammar reading `->*` wherever an arrow may stand: `writeAt :: Int -> String ->* Unit`, `abort :: forall b. Unit ->* b`. It stands at the precedence of `->` and associates to the right, so what follows it is the type the continuation resumes with, a function included: `op :: A ->* B -> C` resumes with `B -> C`. Parentheses around the rest of the spine change nothing, `op :: A -> (B ->* C)`. **The `->*` is written in the signature itself**: no type synonym stands for an operation's signature, since a synonym's right side is no operation's signature and holds no `->*`. The rule is that of first-order operations, the only kind there is; a higher-order operation has a signature `->*` cannot write, and admitting one restates it ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).
- **A precedence is a decimal integer** from 0 to 2³¹−1, with no sign and no `_` ([Lexical Structure](04-Lexical-Structure.md)).
- A directive stands before the declaration it applies to: `#observ(none) foreign sqrt :: Number -> Number`.

## Kinds

```text
kind     ::= kind1 | kind1 "->" kind
kind1    ::= kindAtom | kind1 kindAtom
kindAtom ::= qualProperName | ident | "(" kind ")"
```

**`Type`, `Effect`, and `Row` are the names a kind is made of**, and have that meaning in a kind alone. A lower case name is a kind variable, bound implicitly by the declaration it appears in. There is no `forall` in a kind.

## Types

```text
type  ::= type1
        | "forall" typeVarBinding+ "." type
        | type1 "=>" type
type1 ::= type2
        | type2 "->" type1
        | type2 "->*" type1
        | type2 "/" typeAtom
        | type2 "~>" type2
type2 ::= typeAtom | type2 typeAtom

typeAtom ::= "_" | HOLE | typeVar | qualProperName
           | "(" ")" | "(" type ")" | "(" type "," sep(type, ",") ")"
           | "(" type "::" kind ")"
           | "(" directive type ")"
           | "{" sep(rowItem, ",")? "}"
           | "{|" sep(rowItem, ",")? "|}"
           | "[" sep(rowItem, ",")? "]"
           | "{{" (ident | "_") "::" type "by" qualIdent "}" "}"

rowItem ::= label "::" type | TAG "::" type | type | "..." typeAtom?
```

- **`/` follows the last arrow of a chain and belongs to it.** `Int -> String -> Unit / {| Console |}` is `Int -> (String -> Unit / {| Console |})`, the effect on the second arrow. With no arrow before it, `Int / {| Random |}`, it is a computation type ([Top-level Computation Declaration](../../proposals/05-Toplevel-Computation-Declaration.md)).
- **`()` is `Unit`**; a parenthesized list of two or more is a tuple.
- **Braces hold a record's row, `{| |}` an effect row, and brackets a variant's**, each row written by one element grammar ([Rows](../03-Typed-Core/02-Rows.md)): a labelled element `name :: τ`, a tag `'Ok :: τ`, an element standing alone such as an effect `State Int`, and a spread `...r`, `...`.
- **`E ~> ρ` is the shape of a capability translation** ([Effect Handlers](02-Effect-Handlers.md)).
- **`{{ d :: C τ by f }}` is a synthesized argument**, the parameter a constraint desugars to.

## Expressions

```text
expr  ::= expr1 | expr1 "::" type
expr1 ::= expr2 | expr1 operator expr2
expr2 ::= expr3 | expr2 expr4 | expr2 blockExpr
expr3 ::= expr4 | blockExpr
expr4 ::= exprAtom | exprAtom "." sep(label, ".")

operator ::= operatorName | INFIXNAME

blockExpr ::= "\" binderAtom+ "->" expr
            | "let" block(letBinding) "in" expr
            | "case" sep(expr, ",") "of" block(caseAlternative)
            | "handle" expr "with" block(handlerListItem)
            | "using" block(handlerListItem) "handle" expr
            | "import" moduleName "in" expr
            | ident ":=" expr

exprAtom ::= "_" | HOLE | qualIdent | qualProperName | DISCRIMINATOR
           | OPVALUE | TAG | "true" | "false" | INT | NUMBER | CHAR | STRING
           | "resume"
           | "(" ")" | "(" expr ")" | "(" expr "," sep(expr, ",") ")"
           | "[" sep(expr, ",")? "]"
           | "{" recordFields? "}"
           | "M.(" expr ")"
           | macroCall
           | ident "@" exprAtom
           | ident "!"

recordFields ::= sep(recordField, ",") ("," "..." expr)? | "..." expr
recordField  ::= label ":" expr | label | label "=" expr
letBinding  ::= ident "::" type | binder1 "=" expr
```

- **Every operator is read at one precedence and associates to the left**, in the order written. Declared fixities rebracket the chain afterwards, as PureScript's rebracketing does, which is where an imported operator's fixity is known.
- **Application binds tighter than any operator.** A negative literal is one token, so `f -1` is `f` applied to `-1` ([Lexical Structure](04-Lexical-Structure.md)).
- **A lambda, `let`, `case`, `handle`, and `using` extend as far to the right as they can**, and may stand as the last argument of an application: `map \x -> x + 1`.
- **`_` is an anonymous argument**: `case _, _ of`, and the section `(_ + 1)`.
- **A record literal's field is `name: e`, a pun `name`, or a replacement `name = e`, and one spread `...e` may stand last.**
- **`op@label`** performs an operation of a labelled effect, and on the left of a guard block's binding `m@(Just x)` is an as-pattern; **`x!`** reads a cell and **`x := e`** writes one ([Effect Handlers](02-Effect-Handlers.md)).
- **`M.( e )` opens `M` within `e`**, and **`import M in e`** does the same over the rest of the expression ([Name Resolution](06-Name-Resolution.md)).
- **A local function binding is written in a `let` as a name followed by patterns**, `let f x = x`; a name alone binds a value, and anything else is a pattern binding.

### Case

```text
caseAlternative ::= sep(sep(binder1, ","), "|") ("->" expr | "where" block(guardLine))
guardLine ::= expr1 "=" expr | expr1 "->" expr
```

- **An alternative's patterns are one row per scrutinee, separated by `,`, and an or-pattern at its top separates whole rows by `|`**, which binds more loosely than `,`: `A, B | C, D` is `(A, B)` or `(C, D)`. An or inside one column is parenthesized.
- **A guard block holds bindings and guards**, `x = e` and `e -> body`. The left of a binding is read as an expression and taken as a pattern afterwards.
- `otherwise` is a guard with the meaning it has there ([Pattern Matching](../../proposals/03-Pattern-Matching-Syntax.md)); to the grammar it is a name.

## Patterns

```text
binder  ::= binder1 | binder1 "::" type
binder1 ::= binderAtom+
binderAtom ::= "_" | ident | ident "@" binderAtom | qualProperName | TAG
             | "true" | "false" | INT | NUMBER | CHAR | STRING
             | "(" ")" | "(" binder ")"
             | "(" binder "," sep(binder, ",") ")"
             | "(" binder "|" sep(binder, "|") ")"
             | "{" recordBinders? "}"
recordBinders ::= sep(recordBinder, ",") ("," "..." ident?)? | "..." ident?
recordBinder  ::= label ":" binder | label
```

**Atoms side by side are a constructor or a tag applied to the rest**, `Just x`, `'Ok n`. Any other head is kept as written, for a `let` binding to read as a local function and for a pattern to be rejected.

## Handlers

```text
handlerDecl ::= "handler" ident binderAtom* "::" type "where" block(handlerItem)
handlerItem ::= "var" ident ":=" expr
              | marker? clause+
handlerListItem ::= (qualProperName | ident) marker? ("var" ident ":=" expr)* clause+
                  | expr
clause ::= "|" marker? opName binderAtom* "->" expr
         | "|" "return" binderAtom "->" expr
marker ::= "full" | "fast" | "reifiable" "full"
```

**A group written in place is a head — an effect name or a label — followed by a marker, a cell declaration, or a clause**; any other item of a handling expression is a handler, an expression. The two are told apart by the token after the head ([Handler Surface Syntax](../../proposals/02-Handler-Surface-Syntax.md)).

**A top-level handler's block holds its cells and its clauses with no head**, the effect it handles following from its signature.

**`reifiable` qualifies a marker that captures the continuation**, and today that is `full` alone: a `reifiable full` clause takes the continuation as a parameter after the operation's arguments, a value of the abstract type `Continuation` it may keep beyond the clause, where a `full` clause reaches it through `resume` alone ([Handler Surface Syntax](../../proposals/02-Handler-Surface-Syntax.md)).
