# Syntax Extensions and Parsers

Status: Proposed. Part 1 is the contract the first implementation of macros fixes; Part 2 is the
direction it is built to grow into. What an implementation settles moves from here into the
technical references.

## What is This?

### Background

A macro call stands where an expression or an item does, `format%"{n}"`, and is resolved by name
in the macro namespace the module's header fixes
([Name Resolution](../technical-references/02-Surface-Language/06-Name-Resolution.md)). What a macro
receives, what it returns, its type, and how it runs are not settled. Two aims decide them:

- **A macro is written as naturally as the syntax it introduces.** An author describes the syntax
  the call reads and the syntax it stands for, and does not assemble tokens by hand.
- **The surface grammar extends to first-class parsers without a second mechanism.** A library
  syntax selected today by naming it, `do%{ … }`, is selected later by its own keyword, `do …`,
  and the code that reads it is the same.

So a macro is not a function from tokens to tokens. **A macro is a parser**: it reads the tokens
the call hands it and produces syntax of a known category, which the host then reads as it reads
source.

```text
m%{ … }                          explicit selection, by name
   ↓ the parser m names
Parser (Syntax Term)             reads a token tree
   ↓ Syntax Term
the host's grammar               reads the syntax as an expression
   ↓
Surface AST                      resolved as source is
```

## Part 1: The contract

### 1. A macro is a parser of a category

```stella
@[macro]
doSyntax :: Parser (Syntax Term)
```

`@[macro]` on a value of type `Parser (Syntax c)` declares a macro of category `c`. `Term` is the
category of expressions and the only one Part 1 admits. **`m%` selects the parser by its name**,
and the bracket or the string after the `%` is its whole input, which it must consume: a parser
leaving tokens unread fails, naming what it expected next.

**The type is checked, since the category is read from it.** The declaration's checked scheme,
its synonyms expanded, is `Parser (Syntax Term)` exactly — no quantifier and no constraint — or
`@[macro]` on it is rejected. A module importing the macro checks the same of the scheme its
interface carries. **The session that runs it holds no type**, and checks instead what the global
holds and what crosses: a `Parser` around a function, an input of the types `Stella.Syntax` gives
the token tree, and a result that is a `Result (Syntax Term)`.

**A macro is compiled to a global and has no identity as a value in source.** Its name enters the
macro namespace of the modules importing it and no value namespace, so neither those modules nor
the module declaring it names it as a value
([Name Resolution](../technical-references/02-Surface-Language/06-Name-Resolution.md)).

**A call stands where an expression does.** Which category a call must produce is decided by where
it stands, and not by the bracket or the string after the `%`, which only delimits its input: at an
expression's position it is `Term`, and at an item's position it is a declaration. Part 1 expands
the first alone, and rejects a call at an item's position as not supported, whatever follows its
`%`.

### 2. The input is a lossless token tree

A call hands its parser a **token tree**: the tokens of the bracket, the brackets included, nested
by delimiter. Nothing is lost on the way.

```text
TokenTree = Leaf Token
          | Group Delimiter Token (List TokenTree) Token     the opening and closing tokens kept

Token     = { kind, text, range, leading : List Trivia }

Trivia    = Spaces       text range
          | Newline      text range
          | LineComment  text range
          | BlockComment text range
```

A range carries the line and column of each end. **The host computes no layout on a macro's
input**: no virtual brace or separator is inserted, and indentation stays in the trivia, where a
parser reads it if it means to. Comments are kept for the same reason: a parser may ignore them,
and a tool still has them.

### 3. A parser, and the `layout` combinator

`Parser a` consumes tokens and fails or yields an `a`. A failure carries **the farthest position
reached, the set of tokens expected there, and the labels** the parser gave the contexts it was
in, so that a call written wrong is reported where it went wrong and in the terms of its syntax.

**Reading indentation is a parser's choice.** The `layout` combinator reads a block of items by
the lines and columns the trivia records, as the host's own layout does for source: the column of
the first item's first token is the block's, a token beginning a line at that column begins the
next item, one to its left ends the block, and one to its right continues the item. A syntax may
instead read braces, commas, or lines, and each library syntax chooses for itself.

```stella
doSyntax =
  layout statement >>= \statements -> …
```

### 4. The output is classified syntax

A parser produces `Syntax c`, syntax of category `c`:

| It holds | Why |
| --- | --- |
| a tree of tokens and delimiters | what the host reads |
| logical layout groups, and the boundaries between their items | blocks, decided already rather than written as indentation |
| an origin per token and per node — a group, a layout group, an item boundary | diagnostics reach the source, and the host places what it inserts for a group, an empty one included |

**A layout group is not the `layout` combinator.** The combinator interprets the trivia of an
input; a group is structure an output already has. Where the host reads `Syntax c`, each group
stands for a block whose items are separated and enclosed by the virtual tokens its own layout
inserts, `VOPEN`, `VSEP`, and `VCLOSE` ([Syntax](../technical-references/02-Surface-Language/05-Syntax.md)).
Nothing is recomputed from indentation, and no source `;` is involved, so a group never meets the
sequencing `e1; e2`.

**An origin a parser gives is where a token or a node came from, and the expansion it came through
is the host's to add.** A parser returns the origins its input carried, or those of the quotation
it built from; the host attaches the frame of the expansion — the macro, the call, and the
expansion that call stands in — so that no parser can write a trace of its own. The host checks
what it is returned before reading it: a tree well formed, every origin one it handed out or a
quotation's.
### 5. Quotation

Writing syntax is quoting it. A quotation is a surface form holding syntax of a category, with
**antiquotations** splicing in values of type `Syntax c` computed around it:

```stella
quoteTerm
  let
    x = $e1
    y = $e2
  in x
```

The quoted text is read by the host's grammar for the category, extended by antiquotation holes,
so a quotation that is no expression is an error where it is written. Its layout becomes layout groups: the block above is
one group of two items. The spelling of a quotation and of an antiquotation is fixed with their
implementation.

### 6. Running a parser

**A parser is guest code, and the host runs it.** `Parser` and its combinators are Stella terms,
executed on the compile-time session ([Abstract Machine](../technical-references/07-Runtime/01-Abstract-Machine.md))
like any guest; the module declaring a macro is loaded as any module is. The host owns everything
around them: the lexer and the token tree, the fixed grammar that reads what a parser returns, the
session and its budget, the check of a returned syntax, and the origins and expansion frames — and,
later, hygiene. **`parse` is not a parser engine of the host's**: it runs a guest global at the type
its declaration was checked at, through a request the session advertises as the capability `parse`.

| Request | Answer |
| --- | --- |
| `parse { parser: { module, name }, input: { trees, end }, budget }` | `parsed { syntax }`, `parseFailed { failure }`, `executionFailed { reason, detail }`, or `budgetExceeded {}` |

**The category is the parser's**, read from the type its declaration gives it; a request names no
category of its own. The input is the trees of the call and the position they end at, which is
what the trusted `Stella.Syntax.runParser` the session applies takes. `parseFailed` is the parser
failing as a parser does, with the farthest
position, the tokens expected, and its labels; `executionFailed` is the code failing; and
`budgetExceeded` is the step budget spent. The token tree and the syntax cross as the session's
generic values.

**A parser reaches no observable state outside its run.** It does not reach the elaborator's
kernel — no goal, no metavariable, no term — and performs no effect a host could observe, so what
an expansion produces depends on the parser, its input, and the values of the modules it reaches,
and a build may key it as it keys a module. The session makes this so rather than trusting it: a
parser runs closed, halting at an effect it handles nowhere, a foreign the host carries out, and an
array it did not make; and a session running parsers loads no module declaring such a foreign and
initializes every module a client loads closed
([Abstract Machine](../technical-references/07-Runtime/01-Abstract-Machine.md)).

The types — `TokenTree`, `Trivia`, `Syntax`, `Parser`, and the combinators — are a module of
guest code the compiler supplies, as it supplies `Stella.Elab`.

### 7. Expansion, and where it stands

Expansion is a stage of its own between the import scope and name resolution
([Name Resolution](../technical-references/02-Surface-Language/06-Name-Resolution.md)):

```text
items grouped → import scope → expansion → top-level scope → resolution
```

- **A call is resolved by name in the macro namespace the header fixes**, and nothing else is
  resolved before the expansion it belongs to.
- **What an expansion produces is read and expanded again**: a call in its output is expanded in
  turn, to a depth past which the call is an error.
- **A failure is reported at the call**, whether the parser failed, the code failed, the budget ran
  out, or what it produced is not what its category reads.
- **Every token and node an expansion produces keeps its origin**: the call's input or a quotation,
  under the frame the host attached — which macro, at which call, under which enclosing expansion.
  A node of the Surface AST built from one is located through it.

**Part 1 is not hygienic.** A name an expansion writes is resolved where the call stands, as though
written there.

## Part 2: Later stages

The contract above is built so that each of these adds to it rather than replaces it.

- **`SyntaxSpec`.** A declaration publishing a syntax: its category, the parser, the tokens that
  trigger it, its precedence where it composes with other syntax, the roles of its tokens, and its
  documentation. An interface carries it, so a tool reads it without running the parser.
- **Selection by trigger.** Where a `SyntaxSpec` is in scope, its trigger selects its parser as
  `m%` selects one today: `do …` rather than `do%{ … }`. The fixed grammar reaches a library syntax
  through an extension point of a category, reading the extent of the call as a token tree, so an
  arbitrary parser never runs inside the host parser's own states.
- **Keywords by environment.** Beyond what the lexer must fix, a word is a keyword where a syntax
  imported into the module makes it one, so the reserved words of a module are computed from its
  imports.
- **Hygiene.** Scope marks on the names an expansion writes, so that a binding it introduces
  captures no name written in source.
- **Other categories.** Declarations, with the attribute prefix a declaration-position call keeps;
  types; patterns.
- **Tooling metadata.** Annotations a parser puts on the syntax it builds — the role a token has
  there, keyword, binder, operator — which the language server turns into semantic tokens; and
  completion, hover, folding, and formatting.

## Open Questions

- The spelling of quotation and antiquotation.
- The depth past which repeated expansion is an error, and whether a module may raise it.
- **What a trigger hands its parser.** A parser selected by a trigger cannot run inside the host
  parser's states, so a `SyntaxSpec` says how far the host reads the call as a token tree — a
  delimited group, a layout block, until a set of tokens — and whether the trigger itself is part
  of the input. For one parser to serve `do%{ … }` and `do …` alike, the host consumes the
  selector and the trigger and hands the parser a payload of one shape either way.
- How a declaration a parser produces is published to the catalog alone
  ([Open Questions](../technical-references/99-Open-Questions/01-Open-Questions.md)).
