# Surface AST

The Surface AST is what name resolution builds from the concrete syntax tree and what elaboration reads ([Name Resolution](06-Name-Resolution.md), [Elaboration](01-Elaboration.md)). It is `Stella.Compiler.Surface`.

**It is expanded, resolved, and desugared.** It holds no macro call, no unresolved name, no local open, no parenthesis, and no operator chain waiting for its fixity. Every global is qualified by the module declaring it, every local is the binding it refers to, and every node carries its origin. Which entity a name refers to is told by the node holding it, and nothing else about the entity is: its scheme, its arity, and the type a constructor builds are read from the module's environment and the interfaces.

## Origins

**Every node carries an `Origin`**, which a diagnostic about the node is located by. A node built from source carries `FromSource` and the range of the source it was built from. A node built from what an expansion of a macro produced carries `FromExpansion`.

```text
Origin = FromSource range
       | FromExpansion { range, macro, call :: Origin, written :: Origin }
```

**Every range is in one text**: the source, or what one expansion produced. An expansion's text is numbered apart from every other's, and two ranges are of one text where they are of the source, or of the expansion of one number. **A token of an expansion stands at its place in what was produced**, the `n`th covering column `n` of line 1, and the expansion records the macro, the range of its call — in the text the call stands in — and, for each of its tokens, the range of the token it came from: a token of the call's input, or, once a parser can write one, of a quotation. So a range of an expansion covers a run of its tokens, and its origin is read off the range alone:

- `macro` is the macro expanded, and `call` the origin of the call, which is itself `FromExpansion` where an expansion wrote the call;
- `written` is the origin of what the tokens it covers came from, the ranges they came from joined where they are of one text, and the call's where it covers none.

**A diagnostic is located at the call written in source** that the expansions a node came through began at, and the chain of `call` and `written` says which expansion, of which macro, it stands in and what it was written as. A node an expansion produced stands under one holding the call's range, so no node of one text covers a range of another: **ranges are joined only within one text**, and joining two of different texts keeps the first.

**A range is composed from the concrete syntax tree** ([Syntax](05-Syntax.md)). A node built from several covers the smallest range holding theirs, so a node's range begins at its first part and ends at its last; a keyword and a grouping parenthesis are not part of it, and `\x -> e` covers `x -> e`, `(f x)` covers `f x`. A form made by its brackets — `()`, a record, a row, a variant, a record pattern — covers its brackets, so `()` and `{}` have a range like any other node.

## Names

| Position | Held as |
| --- | --- |
| a global value: a value, a computation, a foreign, a handler, a constructor, an operation | `Qualified Ident` |
| a type constructor or a type synonym | `Qualified TyName` |
| an effect | `Qualified EffName` |
| an attribute, where it is declared and where it is attached | `Qualified Ident` |
| a local value | `LocalVar` |
| a type variable | `TypeVar` |
| a cell | `CellVar` |
| a kind variable | `KindVar`, its name |
| a label, and a tag | `Symbol` and `Tag`, as written |
| an operator, or a type operator, a fixity declaration introduces | `OperatorName` |

- **A binding is a number and the name it was written with.** The number, a `BindingId`, is unique within the module and is what tells two bindings of one spelling apart; the name is kept for diagnostics and for the names Core is given.
- **A kind variable is held by its name.** It is bound by the declaration it appears in, implicitly and at the front (D3), and no binder of one stands inside another, so its name is enough.
- **A declared name is qualified by its module**, as every reference to it is, so a declaration and a reference to it compare equal. An elaboration-only constructor is declared under its internal identity ([Modules](../06-Modules/01-Modules.md)).

## What a name refers to is told by the node

| Node | Refers to |
| --- | --- |
| `ExprLocal` | a local value |
| `ExprValue` | a top-level value, a foreign, or a handler |
| `ExprComputation` | a computation declaration, which runs each time it is referred to ([Top-level Computation Declaration](../../proposals/05-Toplevel-Computation-Declaration.md)) |
| `ExprConstructor` | a data constructor; `()` is `Prim.Unit` |
| `ExprOperation` | an operation, with the label of the instance it is performed on where one is written, `get@cache` |
| `ExprDiscriminator` | the discriminator `C?` of a constructor ([Discriminator](../../proposals/04-Discriminator.md)) |
| `TypeConstructor` | a data type, a newtype, a foreign type, or an intrinsic; `()` is `Prim.Unit` |
| `TypeSynonym` | a type synonym, expanded where the type is elaborated |

**A type synonym is a node of its own** for the reason a computation is: what elaboration does with it differs from what it does with a type constructor, a synonym being expanded where it stands.

## Types

**Three forms of the surface stand in one position each**, and each is a type of its own rather than a form of `Type`, so none can stand elsewhere.

| Written | Stands | Held as |
| --- | --- | --- |
| `forall ā. C => {{ d :: C τ̄ by f }} -> τ / ρ` | at the end of the spine of a computation declaration's signature | `ComputationType`: its spine — quantifiers, constraints, and synthesized arguments (`PrefixSynthesized`) — in the order written, the result, and the row |
| `forall b̄. σ̄ ->* τ` | as an operation's signature | `OperationSignature`: its own type variables, the arguments, and the type it resumes with (D21) |
| `forall ā. E ~> ( t̄ )` | as a handler declaration's signature, under its quantifiers | `HandlerSignature`'s `Capability`: the binders of each `forall` in front of `~>`, a group apiece in the order written, then the source and the targets, each an effect application |

**An arrow holds the row `/` puts on it.** `τ1 -> τ2 / ρ` is a `TypeFunction` with the row, and an arrow with none is pure. The arrow after a synthesized argument is pure and takes no row; a `/` after it is the computation type its spine ends in.

**A type operator is applied to its two operands**, rebracketed by fixity: `TypeOperator` holds the operator, as the entity it names — a type constructor, a type synonym, or an effect — with the origin of where it was written, and then the operands. One naming an effect stands as the effect application it is where one is called for — an element of an effect row, the source or a target of `~>` — its arguments being its two operands and then any an application adds, `(a & b) c`; anywhere else it is a `TypeOperator` like any other, and kinding judges it. The arrow, the `/` of a computation type, and `~>` are no type operators, and keep the forms above.

**A signature names the type variables it quantifies implicitly.** `Signature` holds them beside the type, outermost: those it mentions that nothing around it binds. An operation's signature quantifies nothing implicitly, and is no `Signature` ([Name Resolution](06-Name-Resolution.md)).

**A row is held by the bracket it is written in**, each with the items that bracket admits.

| Bracket | Items |
| --- | --- |
| a record, `{ … }` | a field `name :: τ`, a spread |
| a variant, `[ … ]` | a tag `'Ok :: τ`, a label `ok :: τ`, a spread |
| an effect row, `{\| … \|}` | an effect element `E τ̄`, an instance `name :: E τ̄`, a spread |

- **An effect element and an instance hold an effect application**, a declared effect and its arguments. A name standing for an effect is written at the head of one and nowhere else; anywhere else it is no type, and an error ([Name Resolution](06-Name-Resolution.md)). The head of an effect row's element is a declared effect (D16), and a type synonym cannot stand for one: an effect declaration is the only declaration producing `Effect`, and a synonym produces none (D24).
- **A spread with no operand is the anonymous one**, which every anonymous spread of one signature shares per row kind ([Rows](../03-Typed-Core/02-Rows.md)).

**`{{ d :: C τ̄ by f }}` binds nothing.** `d` is a name written for the reader and for diagnostics; the parameter the synthesized argument is passed in is bound where the definition binds its parameters, as any other is.

## Expressions and patterns

- **An operator is applied to its two operands**, rebracketed by fixity: `ExprOperator` holds the operator, as the reference it stands for with the origin of where it was written, and then the operands.
- **`e.a.b` is two selections**, one label at a time.
- **A declaration's `where` is a `let`** around the body.
- **A `case` alternative holds a row of patterns per or-choice at its top**, one pattern per scrutinee in each, and a body that is unconditional or a guard block. A guard block holds bindings, guards, and `otherwise`, which is a line of its own rather than a guard naming a value ([Pattern Matching](../../proposals/03-Pattern-Matching-Syntax.md)).
- **A constructor pattern holds one pattern per field**, as many as the constructor has.
- **A tag pattern holds one pattern for its payload, or none.** A variant element carries one payload, so several values are a tuple.
- **A literal pattern is a `Boolean`, an `Int`, a `Char`, or a `String`.** A `Number` is matched by no literal: a literal's identity, bitwise for a `Number` (D37), is not numeric equality, and a guard writes the comparison it means.
- **A pun is a field**: `{ x }` is `x: x`, in a record and in a record pattern alike.
- **An or-pattern binds no variable** and is held as its choices.

## Handlers

- **`handle e with …` and `using … handle e` are one node**, `ExprHandle`, holding the items from the first, outermost, to the last, and the computation. An item is a handler applied, or a group written in place ([Effect Handlers](02-Effect-Handlers.md)).
- **A group holds the effect it handles**, and the label where it handles an instance. A group headed by a label is given its effect from the operations its clauses name.
- **A handler declaration holds the effect it handles**: the left of `~>`, or, for a signature written in full, the one element the thunk's row holds and the result's row does not, a row named by a type synonym read through it ([Effect Handlers](02-Effect-Handlers.md)).
- **A clause holds the form in effect for it**, a group's marker and the default resolved: `ClauseFast`, `ClauseFull`, or `ClauseReifiable` with the pattern its continuation is bound by, the clause's last parameter.
- **A clause holds one pattern per argument of its operation**, a `reifiable full` clause's continuation apart from them, and **a handler holds one clause per operation at most, and one return clause at most**. That every operation of the effect has a clause is not checked here: a handler missing one is rejected by the Core type checker.
- **`ExprResume` stands only as the function of an `ExprApp`**, `resume e`, in the immediate body of a `full` clause: not inside a lambda, a local function, or a handling expression there ([Effect Handlers](02-Effect-Handlers.md)).
- **A group and a handler declaration hold one `HandlerBody`**: the cells, the operation clauses, and the return clause where one is written.

## Declarations

| Declaration | Holds besides its origin, attributes, and name |
| --- | --- |
| value | its signature where written, its parameters, and its body |
| computation | its `ComputationType` signature and its body; it has no parameter |
| data | its kind signature, its parameters, and its constructors |
| newtype | its kind signature, its parameters, and its one constructor of one field |
| type synonym | its kind signature, its parameters, and the type it stands for |
| effect | its parameters and its operations |
| handler | `implicit`, its parameters, its signature, the effect it handles, and its `HandlerBody` |
| foreign | its `Observation` and its signature |
| foreign type | its kind ([Foreign Types](../../proposals/06-Foreign-Types.md)) |
| fixity | its associativity, its precedence, the value or constructor it names, a computation among the values, and the operator |
| type fixity | its associativity, its precedence, the type constructor, type synonym, or effect it names, and the operator |
| attribute | its positional parameter types and its keyword parameters with their defaults |

A fixity declaration, of an operator or of a type operator, names the operator rather than a declaration of its own, and neither it nor an attribute declaration carries attributes ([Attributes, Modifiers, and Directives](07-Attributes-Modifiers-and-Directives.md)).

**What stands before a declaration is part of it.** A modifier and a directive are fields: `implicit` of a handler declaration, and `#observ(none)` of a foreign one, `Observation` being `MayObserve` where nothing is written and `ObservesNone` where it is. An attribute is its qualified name and its arguments **normalized**: as many positional arguments as the declaration has parameters, and every keyword argument in the order the declaration gives its parameters, a default standing for one left out. A default carries the origin of the attribute it was filled into.

**An argument is a constant**: a literal, a global value, a constructor applied to constants, or a record of constants. A computation and an operation are no constant, a reference to either standing for what running it does. A name in a constant is held qualified by the module defining it, which may be one the header imports or one reached through a re-export; resolution adds nothing to the module's dependencies for it.

**A module holds its name, its imports, and its declarations.** The imports are the dependencies its header declares (D22); `Prim` is never among them, an `import Prim` choosing how its names are written and nothing else. What it exports is computed with its interface, rather than held here.

## What an error leaves

**Resolution reports every error in the module and goes on past each**, building what it can. A module with an error is not elaborated, so what is built around an error serves only to go on, and it is built by two rules.

**An error in an expression, a type, a kind, a pattern, or a constant leaves an invalid node of that class** — `ExprInvalid`, `TypeInvalid`, `KindInvalid`, `BinderInvalid`, `ConstantInvalid` — where the erroneous form stood. A name that does not resolve, a form standing where it is not admitted, and a form not yet supported are among them. So is a macro call that was not expanded, which the expansion reported where it stands and which nothing reports again. A chain of operators, of values or of types, holding one that does not resolve or two that cannot be chained is invalid as a whole. So is a local open of an alias no import declares, what it encloses being left unresolved. A capability translation whose source is no effect applied to its arguments is held as an invalid signature written in full. A constructor matched with other than one pattern per field, a tag with several, a `Number` literal, and an or-pattern binding a variable leave the pattern invalid. Where a `case` alternative has several choices at its top, each pattern of a choice that writes a variable is left invalid, and the other patterns of the row are kept: `x, One | Nothing, Two` holds `!, One` and `Nothing, Two`.

**Any other error drops the smallest part around it that is a member of a sequence**: an import, a declaration, an attribute, an item of a row, a target of a capability, an item of a handling expression, a cell, or a clause.

| The error | What is dropped |
| --- | --- |
| an import of a module that is not there | the import |
| an attribute whose name does not resolve, or whose arguments do not match its declaration; any attribute on a fixity or an attribute declaration; one the compiler reads on a declaration it is not for, or a second use of it on one declaration | the attribute |
| a keyword parameter an attribute declaration declares a second time | that parameter |
| `@[elaborationOnly]` on a declaration that is not exactly one the compiler lists | the attribute; the declaration is what it would be without it |
| an item a row's bracket does not admit; an effect element or instance, or a capability target, that is no effect applied to its arguments, or whose effect does not resolve | that item, or that target |
| an operation clause whose operation does not resolve or is not an operation of the effect handled, one with other than a pattern per argument of its operation and its continuation where it keeps one, a second clause for one operation, a second return clause | the clause |
| a `var` of a handler declaration after a clause | the cell |
| a group whose effect cannot be determined | the group |
| a handler declaration whose effect cannot be determined, a fixity declaration whose target does not resolve, a computation declaration with parameters, a macro called at a declaration's position, which this version does not expand | the declaration |

**An import whose module is there keeps its dependency**, whatever else is wrong with it: a lazy import with no alias, or with a list, is reported and opens no name, and its module stays among the dependencies the header declares.

**A dropped declaration's name stays in scope.** The top-level scope is built before any declaration is resolved, so what refers to the name still resolves, and one error is not reported again at every use.

**An error about a form that can still be held leaves it as it is.** A name bound twice keeps both bindings, a declaration of a name declared already is kept beside the first, a record writing a label twice keeps both fields, and a positional parameter an attribute declaration writes after a keyword one is kept among its positional parameters, in the order written; the error is reported and nothing is replaced.

**Where a local name refers is decided by the bindings as written, whatever their errors.**

- **A binder's bindings are numbered and entered into scope before what they scope over is resolved**, read off the syntax as written: the parameters of a declaration, a lambda, or a clause, the variables of a pattern, the bindings of a `let` block or a `where`, and the cells of a handler. They are numbered in the order written and handed to what binds them in that order; a binding is never told apart from another by its range, an expansion giving several names one range.
- **A pattern left invalid still binds the variables written in it**, an or-pattern's among them. Its bindings stand in no node of the tree, the pattern being invalid, and a reference to one still resolves, so a body is not reported again for what its pattern got wrong.
- **Where one group of bindings binds a name twice, the first written is the one a reference reaches.** The group is what binds together: the parameters of one declaration, lambda, or clause, a `reifiable full` clause's continuation among its parameters; the patterns of one `case` alternative; one binding of a guard block; one `let` block or `where`, the names its definitions bind and the variables of its pattern bindings together; the cells of one handler; and the type variables of one `forall`. The later binding keeps a number of its own, and nothing refers to it; `x` and `x!` alike reach the first.

## From the concrete syntax tree

| Concrete syntax tree | Surface AST |
| --- | --- |
| `ItemImport` | an import of the module, unless it names `Prim`, which is no dependency; its list, alias, and `hiding` decide names and leave nothing in the tree |
| `ItemAttribute`, `ItemDirective`, `ItemModifier` | the declaration's attributes, `Observation`, and `implicit`, joined to it where declarations are grouped |
| `ExprMacro` | what its expansion produced, resolved where the call stands; `ExprInvalid` where it was not expanded |
| `ItemMacro` | nothing yet: the declaration is dropped, a call at a declaration's position not being expanded in this version |
| `ItemBroken` | nothing; the parser reported it |
| `DeclSignature` and `DeclValue` | a value, or a computation where the signature is a computation type |
| `DeclKindSignature` and `DeclData`, `DeclNewtype`, `DeclType` | a data type, a newtype, or a type synonym, with its kind |
| `DeclEffect`, `DeclHandler`, `DeclForeign`, `DeclForeignType`, `DeclFixity`, `DeclAttribute` | the declaration of that name |
| `DeclTypeFixity` | a type fixity declaration |
| `KindName`, `KindApp` | `KindType`, `KindEffect`, and `KindRow`; any other name or application is invalid |
| `TypeOp` | `TypeOperator`, rebracketed by fixity; where it names an effect and stands where an effect application is called for — an element or an instance of an effect row, the source or a target of `~>` — an `EffectApplication`, any arguments an application adds following its two operands |
| `TypeArrow` | `TypeFunction`, with the row where its result is a `TypeEffect`; one from a synthesized argument is pure, a `TypeFunction` with no row in a value's signature and a `PrefixSynthesized` on the spine of a computation declaration's signature |
| `TypeForall`, `TypeConstrained` | `TypeForall` and `TypeConstrained`; on the spine of a computation declaration's signature, a `PrefixForall` and a `PrefixConstraint`; in front of `~>`, a `forall` is a group of `Capability`'s quantifiers |
| `TypeEffect` | at the end of the spine of a computation declaration's signature, the result and the row of its `ComputationType`; after an arrow other than one from a synthesized argument, the row of that arrow; anywhere else invalid |
| `TypeOperationArrow` | as an operation's signature, its `OperationSignature`; anywhere else invalid |
| `TypeCapability` | as a handler declaration's signature, under its `forall`s, `HandlerSignature`'s `Capability`; anywhere else invalid |
| `TypeParens`, `TypeUnit` | the type it encloses, and `Prim.Unit` |
| `TypeDirective` | invalid; no directive of this version stands in a type |
| `RowItem` | the item of the row its bracket gives; one the bracket does not admit is dropped |
| `ExprVar`, `ExprConstructor`, `ExprDiscriminator`, `ExprOperatorValue` | the reference node of what it resolves to |
| `ExprOp` | `ExprOperator`, rebracketed by fixity |
| `ExprSection` | the lambda it stands for |
| `ExprAccess`, `ExprAt` | nested `ExprSelect`, and an `ExprOperation` with its label |
| `ExprHandle`, `ExprUsing` | `ExprHandle` |
| `ExprLocalOpen`, `ExprImportIn` | the expression they enclose, its names resolved under the open |
| `ExprParens`, `ExprUnit` | the expression it encloses, and `Prim.Unit` |
| `FieldPun`, `RecordBinderPun` | a field binding the name |
| `BinderParens`, `BinderUnit` | the pattern it encloses, and `Prim.Unit` |
| `BinderApp`, `BinderInvalid` | invalid |
| a `Guard` whose condition is `otherwise` | `GuardOtherwise` |
