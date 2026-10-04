# Lexical Structure

This document settles how source text becomes tokens. The lexer is `Stella.Compiler.CST.Lexer`, and the token type is `Stella.Compiler.CST.Types`. The offside rule, which turns indentation into the block tokens the grammar matches, is a separate pass over the tokens and is described with the grammar ([Syntax](05-Syntax.md)).

## Principles

**Source is UTF-8 text, read as Unicode scalar values.** A byte order mark at the start is skipped.

**A token is the longest match**, apart from the exceptions each rule below names: a negative literal, a comment, `|}`, and `@[`.

**Some tokens depend on adjacency.** The whitespace and comments before a token are kept on it as written, its leading trivia — every run of spaces, every line break as spelt, and every comment — and what follows the last token is kept apart, so that no character of a text is lost but a byte order mark at its start, which marks the encoding and is no text. Whether a token stands apart from the one before it is read off its trivia, the first token of a text standing apart, and several rules read it: the `%` of a macro call, the argument list of a directive, a typed hole, the `@` of a label and of an as-pattern, the `!` of a cell read, an operator as a value, and the `-` of a negative literal.

**Positions** count lines from 1 and columns from 1, in UTF-16 code units, which is what an editor protocol counts.

## Whitespace and comments

```text
newline      ::= "\r\n" | "\r" | "\n"
space        ::= " " | newline
lineComment  ::= "--" "-"* ( any character but a newline )*
blockComment ::= "{-" ( blockComment | any character )* "-}"
```

- **A run of dashes is a comment only where no other operator character follows it.** `-->` is an operator, and `--|` is one too.
- **A block comment nests.**
- **A tab character is a lexical error**, outside a comment and a string. Indentation is written with spaces alone.

No other character is whitespace.

## Names

```text
upper      ::= "A" … "Z"
lower      ::= "a" … "z" | "_"
digit      ::= "0" … "9"
identChar  ::= upper | lower | digit | "'"

lowerName     ::= lower identChar*
upperName     ::= upper identChar*
discriminator ::= upperName "?"
qualifier     ::= ( upperName "." )+
```

- **Names are ASCII.** Letters of other scripts, and alternative spellings such as `→` or `⇒`, are not admitted; adding them later only accepts more programs.
- **`'` may stand anywhere in a name but first**: `x'`, `isn't_it`.
- **`?` ends a name only when the name begins with an upper case letter**, and the result is a discriminator, `Just?`. `empty?` is a lexical error.
- **`_` alone is a token of its own**, the wildcard and the anonymous argument. `_x` is an ordinary name.
- **A qualified name** is a qualifier followed with no space by a lower case name, an upper case name, a discriminator, an operator, or `(`: `Data.Array.length`, `M.Just`, `M.Just?`, `DA.++`, `DA.(++)`, `DA.( … )`. A qualifier may contain digits: `Html5.div`.
- **A keyword is lexed as a name**, and the grammar tells it apart. That is what lets a record field be named by a keyword ([Syntax](05-Syntax.md)).

A name the compiler generates, such as `$entry_main`, is not a name of this grammar, and so never meets one written in the source.

### Keywords

```text
module where import data newtype type effect handler foreign attribute
infix infixl infixr let in case of forall handle with using
full fast reifiable resume var true false
```

These are reserved wherever a name may stand, except as a record field. Some other words have a meaning only where the grammar places them, and are ordinary names elsewhere:

| Word | Where it has a meaning |
| --- | --- |
| `as`, `lazy`, `hiding` | an import |
| `macro` | an import or an export list |
| `implicit` | before a handler declaration |
| `return` | a handler clause |
| `otherwise` | a guard |
| `by` | a synthesized argument, `{{ … by f }}`; it is not a type variable |
| `Type`, `Effect`, `Row` | a kind |

## Operators

```text
opChar   ::= "!" | "#" | "$" | "%" | "&" | "*" | "+" | "-" | "." | "/"
           | ":" | "<" | "=" | ">" | "?" | "@" | "\\" | "^" | "|" | "~"
operator ::= opChar+
```

**Some spellings are reserved.** They are tokens of the grammar and never a user's operator:

```text
\  .  ...  =  |  @  %  #  !  :  ::  ->  ->*  =>  <-  :=  ~>
```

**A spelling is reserved only when the whole run of operator characters is that spelling.** `==`, `|>`, `@@`, `%%`, `!=`, `<#>`, `..`, and `.?` are ordinary operators, and `..` is free for a range, `.?` for an optional chain.

- **`?` and `-` alone are ordinary operators.**
- **`\` alone is the backslash of a lambda**, `\x -> e`, and among other operator characters it is one of them: `/\` and `\/` are operators. The longest match decides, so `f $\x -> x` is `f`, `$\`, `x`, `->`, `x`, and a lambda after an operator is written with space between.
- **`%` and `#` alone are lexical errors.** `%` marks a macro call and `#` a directive, and neither is an operator on its own.
- **`@` stands with no space on either side**: `get@cache`, `mb@(Just _)`. With space beside it, it is a lexical error.
- **`!` alone follows a lower case name with no space between**: `n!` reads a cell. Anywhere else it is a lexical error. `n!=m` is `n`, `!=`, `m`, the longest match.
- **`/` is an ordinary operator in an expression.** In a type it belongs to the grammar, as the `/` of a computation type `τ / ρ`, and is no type operator; any other operator may be one ([Syntax](05-Syntax.md)).

**An operator as a value is `(`, an operator, and `)`, with no space between**: `(++)`, and with a qualifier `DA.(++)`. It is one token. `( ++ )` is three tokens and not an operator as a value. A reserved spelling cannot be made a value: `(=)` and `(\)` are lexical errors. `(..)` is the operator `..` as a value, which the grammar also reads, after a type name in an import or export list, as every constructor of the type.

**A name used infix** is written between backticks with no space inside: `` `rem` ``, `` `M.mod` ``.

## Brackets and punctuation

```text
(  )  [  ]  {  }  ,  \  _
{|  |}  {{  @[  M.(
```

- **`{|` is `{` and `|` with no space between.** `|}` is a lone `|` followed with no space by `}`: `||}` is `||` and `}`. `{||}` is `{|` and `|}`, the empty effect row.
- **`{{` opens a synthesized argument and closes with two `}`**, so that it never meets the `}}` of nested records.
- **`@[` opens an attribute** where `@` alone is followed by `[`. `@@[` is the operator `@@` and `[`.
- **`M.(` opens a local open** of the module `M`, closed by `)`.

## Adjacency

| Written | Token | Example |
| --- | --- | --- |
| a lower case name, `%`, and `(`, `[`, `{`, or `"` | a macro call | `format%"…"`, `class%{ … }`, `Fmt.format%"…"` |
| `#` and a lower case letter | a directive | `#inline` |
| a directive and `(` | a directive with arguments | `#observ(none)` |
| `?` and a name or `_` | a typed hole | `?todo`, `?Foo`, `?_` |
| `'` and an upper case letter | a variant tag | `'Ok`, `'A` |

- **A macro call** is the name and the `%`. The bracket or the string after it is an ordinary token.
- **A directive** is the name. Whether an argument list follows with no space is recorded on it: `#observ(none)` has one, and in `(#unbox (Maybe Int))` the parenthesis is what the directive applies to.
- **`?` followed by a name is a hole** wherever it stands, so `x?y` is `x` and the hole `?y`. A `?` followed by nothing that can begin a name is an operator character.
- **A tag has no `'` and no `?` in it.** `'A'` is a character, `'A` a tag, and `'Ok'` a lexical error.

## Numeric literals

```text
decimal  ::= digit ( "_"? digit )*
binary   ::= "0b" bit ( "_"? bit )*
hexadec  ::= "0x" hex ( "_"? hex )*
int      ::= "-"? decimal | binary | hexadec
number   ::= "-"? decimal "." decimal exponent?
           | "-"? decimal exponent
exponent ::= ( "e" | "E" ) ( "+" | "-" )? decimal
bit      ::= "0" | "1"
hex      ::= digit | "A" … "F" | "a" … "f"
```

- **An `int` is an `Int` and a `number` a `Number`.** `1e3` is a `Number`.
- **`_` separates digits**, one between two digits, anywhere a run of digits stands: `1_000.000_1`, `1e1_0`, `0b1010_1010`, `0xFF_FF`. It cannot stand beside `.`, `e`, or a prefix: `1_.0` and `0x_FF` are lexical errors.
- **Leading zeros are admitted** and mean nothing: `007` is `7`.
- **A `.` belongs to a number only with digits on both sides.** `.5` and `1.` are not numbers, and `1..5` is `1`, `..`, `5`.
- **A literal followed with no space by a name character** — `1abc`, `1_`, `0x` — is a lexical error.

### Negative literals

**A negative literal is a `-` followed with no space by a digit, where the `-` has space before it, stands first in the text, or follows `(`, `[`, `{`, `{|`, `{{`, `@[`, `M.(`, or `,`.** Anywhere else the `-` is an operator.

```text
f -1        f applied to the literal -1
x - 1       subtraction
x-1         subtraction; the - follows a name with no space
[3,-4]      two literals
a==-5       the operator ==- ; the longest match takes the -
```

There is no prefix negation: `-x` is not an expression, and `negate x` is written instead. Only a decimal literal is negative; `-0xFF` is not a literal, and `negate 0xFF` is written.

### Range

**A decimal `int` lies within `Int`**, −2³¹ to 2³¹−1 (D37), the sign included, so `-2147483648` is a literal. Beyond that it is a lexical error.

**A binary or hexadecimal `int` is a 32-bit pattern.** A value from `0` to `0xFFFFFFFF` is read as two's complement: `0xFFFFFFFF` is `-1` and `0x80000000` is −2³¹. Beyond that it is a lexical error. Leading zeros do not count.

**A `number` is rounded to the nearest binary64, ties to even.** One that rounds to an infinity is a lexical error. `-0.0` and `0.0` are different literals (D37).

## String and character literals

```text
string      ::= "\"" stringChar* "\""
stringChar  ::= any character but "\"", "\\", or a newline
              | escape
escape      ::= "\\" ( "\"" | "\\" | "/" | "b" | "f" | "n" | "r" | "t" )
              | "\\u" hex hex hex hex
              | "\\u{" hex+ "}"

blockString ::= "\"\"\"" blockChar* "\"\"\""
blockChar   ::= any character but the start of "\"\"\"" or of "\\\"\"\""
              | "\\\"\"\""

char        ::= "'" ( any character but "'", "\\", or a newline | escape | "\\'" ) "'"
```

This follows GraphQL's string grammar.

- **An escape names a Unicode scalar value.** One naming a surrogate, D800 to DFFF, is a lexical error, whether written `\uXXXX` or `\u{…}`, and one beyond 10FFFF is too. A Stella `String` holds no unpaired surrogate (D27), and `\u{1F600}` is how a character beyond the Basic Multilingual Plane is written, so no rule joins two escapes into one character.
- **A literal holds Unicode scalar values alone.** An unpaired surrogate written raw in a string or a character literal is a lexical error, as one an escape names is; a pair written raw is the one scalar value it encodes.
- **A quoted string ends on its line.** A newline inside it is a lexical error.
- **A block string is raw**: its one escape is `\"""`, which stands for `"""`. Its value is GraphQL's BlockStringValue of its text: line terminators become `\n`, the indentation common to every line after the first that is not blank is removed, and blank lines at the start and the end are dropped.

  ```stella
  greeting = """
      Hello,
        World!
      """
  -- "Hello,\n  World!"
  ```

- **A character literal holds exactly one scalar value**, and takes the escapes of a string together with `\'`.

## Precedence of fixity

The precedence in a fixity declaration is a decimal `int` with no sign and no `_`, from 0 to 2³¹−1 ([Syntax](05-Syntax.md)).
