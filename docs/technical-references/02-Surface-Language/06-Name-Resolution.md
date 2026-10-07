# Name Resolution

This document settles what a name written in source refers to. By the time a term reaches the Surface AST every name in it is resolved, and by the time it reaches Core every name is fully qualified ([Modules](../06-Modules/01-Modules.md)).

## Where it runs

**Resolution and macro expansion are one pass from the concrete syntax tree to the Surface AST**, and they run in stages, because expanding a macro call needs the macro's name resolved and the expansion's result needs resolving in turn.

1. **The import scope** is built from the header alone: what each import makes visible, unqualified and through each alias.
2. **Macro calls are expanded**, and a call an expansion produced is expanded in turn. This version expands a call standing where an expression does, until none remains; a call at a declaration's position or in an attribute's argument passes this stage as it stands and is reported as not yet supported where it is resolved. What this stage resolves is **the name of each call and nothing else**, in the macro namespace. That namespace holds what the imports bring and nothing the module declares, so it is fixed by the header, and the order expansions run in changes nothing a call resolves to. A call inside a local open is resolved against the macros the open brings, the extent of the construct being known before anything is expanded. How a call is expanded is in [Expanding a macro call](#expanding-a-macro-call).
3. **The module's top-level scope** is the import scope together with every top-level declaration. An expansion at a declaration's position is to add the declarations it produces; one where an expression stands produces none, and is the only one this version expands.
4. **Every other name is resolved**, against the top-level scope and the bindings around it, whether it was written in source or produced by an expansion. In `f x = m%{ x }`, the `x` an expansion places in the body is resolved here, under the binding of `f`'s parameter, and could not have been at stage 2, where neither the top-level scope nor any local binding exists yet.

### What it produces

**The resolver reads the concrete syntax tree and builds the Surface AST.** What the Surface AST holds is fixed in [Surface AST](08-Surface-AST.md). The tree keeps every name as written, a qualifier being the alias written and not yet a module, and the Surface AST holds at each position the kind of name that position calls for.

| Position | Name held |
| --- | --- |
| a global value: a value, a computation, a foreign, a handler, a constructor, an operation | `Qualified Ident` |
| a type constructor or a type synonym | `Qualified TyName` |
| an effect | `Qualified EffName` |
| a local value, and a cell | the binding it refers to |
| a type variable | the type binding it refers to |
| a label and a tag | `Symbol` and `Tag`, unresolved |

- **A global is qualified by the module that declares it.** An alias is replaced by the module it stands for, and a name a module re-exports is the entity it was in the module declaring it, so `M.a` after `import Long.Module as M` is `Long.Module.a` where `Long.Module` declares `a`, and `Other.a` where it re-exports the `a` of `Other`.
- **A binding carries the name it was written with**, beside the identity that tells two bindings of one spelling apart, for diagnostics and for the names Core is given.
- **What a name refers to is told by the node holding it.** A reference to a value and a reference to a computation are different nodes, as are a constructor, an operation, and a discriminator, and as are a type constructor and a type synonym; what else is known of an entity is read from the module's environment and the interfaces, so no resolved name carries it.
- **Every node is annotated with where it came from**: its source range, for a node built from source, and for one built from what an expansion produced, its range in that expansion, through which the call and what its tokens were written as are reached ([Surface AST](08-Surface-AST.md)).
- **A name that does not resolve is an error node, and resolution carries on**, so that every error in the module is reported; a module holding one is not elaborated.

**An expansion produces declarations and expressions, and never an import or a module header.** The header is what the dependencies are read from (D22), and the import scope has been fixed before any expansion runs.

### Expanding a macro call

**A call standing where an expression does is expanded; this version expands no other.** A call at a declaration's position and one in an attribute's argument are reported as not yet supported where they stand ([Syntax Extensions and Parsers](../../proposals/09-Syntax-Extensions-and-Parsers.md)).

**The name of a call is looked up in three places, the first that holds it deciding.**

1. A qualified call, `A.m%[ … ]`, under its alias, an alias no import declares being an error. A lazy alias opens nowhere but in a local open, so it qualifies no call.
2. An unqualified call in the innermost local open around it that brings the name, `A.( … )` and `import A in …` alike, a lazy alias's included.
3. Otherwise, in what the imports bring unqualified.

A name standing for two macros is ambiguous where it is called. A name the module declares as a macro — a value carrying `macro` as the module's own scope decides it ([Macro declarations](#macro-declarations)) — is in no namespace of the module's, and a call of it is reported as such, a macro being for the modules importing it. **What the name stands for must be a parser of terms**: a value carrying `Prim.macro` whose scheme, as its interface carries it, is exactly `Stella.Syntax.Parser (Stella.Syntax.Syntax Stella.Syntax.Term)`.

**A call is run, and what it produced is read as written source is.** The macro's parser is run on the token tree of the call's bracket or string, the input ending at the closing delimiter or at the end of the string. The syntax it returns is checked — every group closed as its delimiter closes, every origin one the call's input carried or one a quotation declares — of the module declaring the macro or of one it reaches through its imports, at a range whose positions are positions and in order, which is all that is checked of it — every token and its trivia what the lexer reads them as — and read by the grammar as one expression, each layout group standing as the virtual tokens the layout inserts ([Syntax](05-Syntax.md)). The expression is then checked as an expression of source is, so an expansion can produce nothing written source could not be.

**A build runs a parser on a compile-time session**, through the session's `parse` request ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)), the build's host making sure the module declaring the macro is loaded there before the call is expanded, a macro of the build running from the bytecode the build wrote for its module; the session installs `Base.Int` and `Stella.Syntax` itself. **What the parser came to is the call's**: syntax, a failure, a run that did not reach an answer, or a budget spent. **What kept the session from answering is not**: a request the session refused or could not carry, an input that cannot be written as a value, and an answer that is not what a parser returns are faults of the session or of the compiler, and stop the build, reported as no error of the module.

**What an expansion produced is expanded in turn, where the call stands.** A call written in the source is at depth 1, and a call an expansion at depth `n` produced is at depth `n + 1`; a call deeper than the limit the build sets is not run. The depth is that of one chain of expansions and not a count over the module, so any number of calls side by side reaches no limit. An outer call is expanded before what it produced, and what it produced in the order written; a call in it resolves its name against the local opens around the call it came from, the expansion being in place of that call.

**A call that is not expanded is reported once, where it stands, and stands as an invalid expression** that no later stage reports again: a name that resolves to no macro, to several, or to no parser of terms; a parser that fails, does not run to an answer, or runs out of steps; syntax that does not read back or does not read as a well-formed expression; and a call too deep.

### A quotation

**A quotation is resolved into the expression building the syntax it quotes**, `Stella.Syntax.Syntax Stella.Syntax.Term` written as an application of `Stella.Syntax`'s constructors ([Syntax](05-Syntax.md)): each token as it is written — its kind, its text, and the trivia before it — each bracket and what it holds a group, and each block the layout opened a layout group, its items as the layout separated them. The braces of the quotation are none of it. **Nothing quoted is resolved**: a name in a quotation is resolved where the syntax is read, by the module a macro's expansion stands in, as every name an expansion produces is. So a module calling a macro imports what its quotations name: one calling `ls` of `Data.List`, whose quotations write `Cons` and `Nil`, imports `Data.List (List(..))`.

**An antiquotation is resolved where it stands**, as an expression of the module, and is syntax of a term; what it splices in stands in parentheses, so that it is one operand whatever it holds: `%term{ f $x }` with `x` holding `1 + 2` reads `f (1 + 2)`. A macro call inside an antiquotation is expanded as any other is.

**Every token and node of a quotation carries an origin declaring where it was written**: the module and the range in its source, which a diagnostic of an expansion it stands in names beside the call ([Surface AST](08-Surface-AST.md)). The constructor of that origin and the splicing are `Stella.Syntax`'s elaboration-only entries, which the elaborator reads at the schemes the compiler lists and no source names ([Modules](../06-Modules/01-Modules.md)). **A module holding a quotation imports `Stella.Syntax`**, whose types the syntax is of; one that does not is reported where the quotation stands.

## Namespaces

**A name is looked up in the namespace its position calls for**, and a name in one namespace never hides a name in another.

| Namespace | Top-level entries | Local binders | Where a name is written |
| --- | --- | --- | --- |
| **value** | values, computations, foreigns, handlers, constructors, operations, synthesizers | value variables | expressions, patterns (constructors), the synthesizer after `by` |
| **type** | data types, newtypes, type synonyms, foreign types, effects | type variables | types, rows |
| **operator** | the operators fixity declarations introduce for values and constructors | none | between operands in an expression, and as a value `(++)` |
| **type operator** | the operators fixity declarations introduce for types, `infixr 0 type RowApply as +` | none | between operands in a type |
| **macro** | the macros the imports bring; none the module declares | none | the name of a macro call, `m%` |
| **attribute** | the attributes declared by the module and the imports | none | the head of an attribute, `@[a …]` |
| **module** | none; the aliases `as` introduces and the namespace tokens `import lazy` introduces, which the header declares | none | the qualifier `X.` of a name, and local open |
| **cell** | none | the cells of a handler | `x!` and `x := e` |

**A namespace holds top-level entries and local binders alike, and a local binder hides an entry of its own namespace only.** A value variable may hide a top-level value; a type variable may hide nothing but a type variable, top-level types being upper case and type variables lower case.

- **A constructor is a value.** It is applied, passed, and matched on as one, as in Core, where a constructor is an ordinary global name ([Modules](../06-Modules/01-Modules.md)).
- **An operation is a value.** It is called as an ordinary function, `perform` not appearing in the surface (D17), and it belongs to the effect that declares it.
- **A clause of a handler names an operation of the effect handled, looked up among that effect's operations** rather than in scope. This is the one place a name is not looked up in scope: the clause head is a member of the effect, as `E(get, set)` names one, so `import M (E)` suffices for a handler of `E`, and a local value of an operation's name does not hide it. A qualified head is looked up in scope and must name an operation of that effect. A group headed by a label names no effect, and its clauses' operations are looked up in scope, local values aside ([Effect Handlers](02-Effect-Handlers.md)).
- **An effect is a type-level name.** Within a type, a name standing for an effect is written only at the head of an effect applied to its arguments: as an element or an instance of an effect row, and as the source or a target of `~>`. No type is an effect, so one written anywhere else in a type is an error. Nor is a type synonym an effect: one standing for a row of effects is written for the row itself, `/ S`, or spread into another, `{| Trace, ...S |}`, and `{| S |}` is an error. A declaration or a list naming an entity names an effect as it names any other: the target of a type fixity declaration, and an item of an import or export list. A type operator standing for an effect is not held to this: `a & b` is an application like any other, which kinding judges, and where an effect applied to its arguments is called for it is read as one, any arguments an application adds following its two operands, so `(a & b) c` is the effect applied to `a`, `b`, and `c`.
- **A macro has a namespace of its own, because it is visible where a value is not.** A macro cannot be used in the module declaring it, so the module's own macros are not in its macro namespace and appear only in its exports. `m%` looks `m` up there, and a bare `m` in the value namespace; a value and a macro of one spelling stand together without either hiding the other, and a macro the module declares hides no imported macro of its name. That a macro is compiled to a Stella function is not visible at the source level.
- **A macro produced by an expansion is no different.** It is not in the macro namespace of the module it was produced in, so it affects no later expansion there.
- **Two imported macros of one name are ambiguous where they are called**, and a qualified call, `M.m%( … )`, tells them apart.
- **An attribute is not a value.** It is declared by a declaration of its own and named at the head of `@[ … ]` alone, so it has a namespace of its own, and a value and an attribute of one spelling stand together ([Attributes, Modifiers, and Directives](07-Attributes-Modifiers-and-Directives.md)).
- **An operator is another name for a value**, and a type operator another name for a type. A fixity declaration `infixr 5 add as +` makes `+` refer to the value `add`, and `infixr 0 type RowApply as +` makes the type operator `+` refer to the type `RowApply`. An operator may name any entity of the value namespace: a constructor, an operation, or a computation among them, which runs where the operator is used, its result applied to the two operands, as a reference to it would be. **The two are namespaces apart**, so one spelling may be both and neither hides the other: what a position calls for decides which is looked up, as for every name. A type operator names an entity of the type namespace — a type constructor, a type synonym, or an effect — and `a + b` is that entity applied to `a` and then to `b`. Whether the two applications are well kinded is decided where the type is kinded, as for any application, so a fixity declaration is refused only where its target does not resolve. The arrow `->` and the `/` of a computation type are the grammar's and no type operator ([Syntax](05-Syntax.md)).
- **A cell is reached through its own syntax alone.** `x!` and `x := e` name a cell, a bare `x` never does, and a cell and a value variable of one spelling stand together without either hiding the other ([Effect Handlers](02-Effect-Handlers.md)).
- **A kind variable is bound by the declaration it appears in**, implicitly and at the front (D3), and is in scope in the kind positions of that declaration alone. `Type`, `Effect`, and `Row` are a closed set of words with that meaning in a kind position, so a kind has no top-level entries to resolve ([Syntax](05-Syntax.md)).

### Discriminators

**A discriminator is derived from a constructor and has no entry of its own** ([Discriminator](../../proposals/04-Discriminator.md)). Meeting `C?`, resolution looks `C` up in the value namespace and resolves `C?` to the discriminator of the constructor it finds; a `C` that is not a constructor is an error.

**It is therefore visible exactly where its constructor is**, under the same qualifier, and nothing exports, imports, or declares one. No other name can collide with one: `C?` is a token of its own, and no declaration names a value ending in `?` ([Lexical Structure](04-Lexical-Structure.md)).

### Labels are not resolved

**A label is a key of a row, and keys are structural.** A record field, the label of an effect instance in `get@cache`, and the label heading a handler group are `SymbolKey`s, which no declaration introduces and no scope holds ([Rows](../03-Typed-Core/02-Rows.md)). Resolution leaves them as written.

**A record writes each label once**: a record type, a record literal and its update, and a record pattern. A pun is a label, `{ a, a: x }` writing `a` twice, and a spread or a rest is none. Each label written after one of its spelling is an error, reported where it stands; in a pattern this is apart from a variable bound twice, so `{ a: x, a: x }` is both.

### Macro declarations

**A top-level value declaration carrying `@[macro]` declares a macro.** Its name enters the macro namespace of the modules importing it, and no value namespace: no source names it as a value, the declaring module included. It is compiled as a global like any other, which is how an expansion runs it, and what type it must have is fixed with macro expansion.

## Imports and exports

**An import brings names in unqualified or through an alias, never both**, and its list, where it has one, selects which.

| Import | Unqualified | Through the alias |
| --- | --- | --- |
| `import M` | everything `M` exports | — |
| `import M (items)` | the items | — |
| `import M hiding (items)` | everything `M` exports but the items | — |
| `import M ()` | nothing | — |
| `import M as A` | nothing | everything `M` exports, as `A.x` |
| `import M (items) as A` | nothing | the items, as `A.x` |
| `import lazy M as A` | nothing | nothing outside a local open of `A`; everything `M` exports inside one |

- **Every form declares the dependency**, `import M ()` doing nothing else, and the header is what the dependencies are read from (D22).
- **A reference reaches its entity through the export table of an import the header names**, and the module declaring the entity is then within the transitive closure of the header's imports. It need not be named there: where `C` imports `B` and `B` re-exports the `x` of `A`, a reference in `C` is `A.x`.
- **An unqualified name and a qualified one are written as two imports**, which reach one entity and so do not conflict: `import M (a)` and `import M as M` make `a` and `M.a` the same reference.
- **A lazy import is qualified and takes no list** ([Syntax](05-Syntax.md)).
- **`hiding` stands on `import M` alone**, with no list, no alias, and no `lazy`, and names items as a list does: `T` hides the type alone, so `import Prim hiding (Unit)` leaves the constructor `Unit` in scope, while `T(..)` hides its members besides and `T(A)` the type and `A`. A name `M` does not export is an error, as it is in a list. It is how a module declares or imports a name another import would bring, `Prelude`'s among them, without hiding one and being warned of it.
- **`Prim` is a fixed dependency of every module, and an import of it selects names and nothing else.** Where the header writes no `import Prim …`, `Prim`'s exports are opened unqualified as a plain `import Prim` would open them; where it writes one, that import opens them instead, as it would a module's, so `import Prim as P` brings `Prim`'s names through `P` alone and leaves `String` free to declare, and `import Prim hiding (String)` brings the rest. Where no import of it is written, a top-level declaration of one of its names hides an imported name and is warned of, as any other is. **Writing one adds no dependency**: `Prim` stands in `Σ`, in `G`, and in the runtime's registry whatever a header says, and an `import Prim` is recorded neither among the imports of the module's interface or its Surface AST nor among those of its Core or its `.dmo`.
- **An import list, an alias, `lazy`, and `hiding` change which names source may write, and nothing else.** The entities a module reaches and what its catalog holds are the same whichever form names an import ([Elaborator API](03-Elaborator-API.md)).

**What a module exports is its own declarations, or what its export list names.**

| Export list | Exported |
| --- | --- |
| none | every declaration of the module: values, types with their constructors, effects with their operations, operators, type operators, macros, and attributes; nothing imported |
| an item naming an entity in scope | that entity, the module's own or imported, qualified or not |
| `module A`, `A` an alias | every name `A.` qualifies, across every import sharing the alias |
| `module N`, `N` imported without `as` | every name that import brings in unqualified |

- **A module does not name itself in its own export list.** `module M (module M, …) where` is an error; a module exporting all of its declarations writes no list.
- **A list is not empty.** `module M () where` is not in the grammar.
- **A lazy alias is not re-exported.** It adds nothing to the module's scope, and `module A` for one is an error.
- **One exported name refers to one entity.** Two items exporting different entities under one name are an error, and an item exporting one already exported is not.
- **An item may be qualified**, a type, a macro, and an attribute as a value may: `A.x`, `A.T(..)`, `macro A.m`, `attribute A.json`. This is how one of two entities brought under one name is chosen; a name several entities stand for, written unqualified, is an error where it is exported, as where it is used.
- **`T(..)` exports every member of `T` that is in scope**, written as the type is, whichever import brought it, and `T(A)` names one that must be: a member a module never imported stays unexported whatever its type does. **Each member is published the way it came**, which need not be the way its type did. One type exported twice, by two items or by two whole modules, is exported once with the members of both, in order.
- **An elaboration-only entry is never listed** by any of these forms ([Modules](../06-Modules/01-Modules.md)).

**A name may stand for several entities in scope**, two imports bringing one name for different ones. That is no error until the name is used or exported; two imports bringing one entity bring it once.

**Imports and exports decide names, and not what a synthesizer may find.** Every module the header reaches contributes to the catalog however it is imported, and an entry may be published to the catalog without being exported to source ([Elaborator API](03-Elaborator-API.md)).

### Naming an entry in an import or export list

**An item of a list names its namespace by its spelling, and a macro, which is spelled as a value is, by the word `macro`.**

| Item | Namespace |
| --- | --- |
| `n` | value |
| `(++)` | operator |
| `type (+)` | type operator |
| `T`, `T(..)`, `T(A, B)`, `E(get, set)` | type: a data type with its constructors, or an effect with its operations |
| `macro m` | macro |
| `attribute a` | attribute |

```stella
import M (Maybe(..), State(..), fromMaybe, (<>), macro format)
```

- **A type and an effect need no word of their own.** Both are in the type namespace, where one module declares no name twice, so what the members after the name select — constructors or operations — follows from the declaration, and a member that is neither is an error.
- **`macro` has this meaning in a list alone**, as `as` and `lazy` have theirs in an import, and is an ordinary name elsewhere. `attribute` is a keyword, beginning an attribute declaration.
- **`type` before an operator names a type operator**, whose namespace is apart from that of the operators of values.

## Local open

**`M.( e )` and `import M in e` are one construct written two ways**, and either applies to any alias the header declares, whether `import … as M` or `import lazy … as M`.

**Within `e`, a name that `M.` qualifies may be written unqualified, and it takes precedence over the same name from outside `e`.** The names `M.` qualifies are those the imports declaring the alias make reachable through it. Where several imports share one alias, the construct opens all of them, and a name two of them bring for different entities is ambiguous where it is used.

```stella
import Data.Map as M        -- M.insert usable throughout the module
import lazy Data.Array as A -- A usable only by local open

f m  = M.( insert 0 (g []) m )   -- insert is M.insert; g is the module's own
g xs = A.( length xs )           -- length is A.length
```

- **The two kinds of alias differ outside the construct alone.** `M.x` is usable anywhere in the module after `import … as M`, and nowhere after `import lazy … as M`, which is what keeps a lazy alias from adding anything to the module's scope ([Modules](../06-Modules/01-Modules.md)).
- **What is opened is what a module can export**: the value, type, operator, type operator, and macro namespaces. An attribute is attached to a declaration and so never stands inside an expression, where an open is; `@[M.a]` and an import list reach one. A type in an annotation, an effect in a row, a constructor in a pattern, a discriminator, an operator, and a macro call inside `e` are resolved by the same rule; an operator opened this way takes its fixity from `M`. Local binders and cells are not a module's to open.
- **What is opened is an alias.** A module imported without `as` has no qualifier, so its full name cannot be opened.
- **The header still names every dependency.** The alias is declared by an import in either case, so local open adds nothing a build reads ([Modules](../06-Modules/01-Modules.md)).
- **An unqualified name is looked up in the innermost construct holding it**, a local open or a binding group, before the module's scope. A variable bound inside an open hides a name the open brings, and a name the open brings hides a local binding outside it, which is warned of at each reference it decides.
- **An alias no import declares is an error**, and the open is invalid as a whole; what it encloses is not resolved.
- **An operator means what its fixity declaration says wherever it is used.** The value a declared operator stands for is resolved where it is declared, so an open around a use changes which operator a spelling names and never what an operator stands for.

## Local scopes

**A construct binding values binds them as one group** ([Surface AST](08-Surface-AST.md)), and the group is in scope where the construct says.

| Construct | Its bindings are in scope in |
| --- | --- |
| a declaration's or a lambda's parameters | its body, its `where` among it |
| a `let` block or a `where` | every right-hand side of the block, and its body |
| a `case` alternative's patterns | its body or its guard block |
| a binding of a guard block | the lines of the block after it |

**A `let` block and a `where` are recursive.** Everything the block binds — the names its definitions bind and the variables of its pattern bindings — is in scope in every right-hand side and in the body, as in Haskell and PureScript. **Initializing a block requires no reference to what it is initializing.** `fibAnd = Tuple "fib" \n -> … snd fibAnd …` is admitted: the recursive function is stored in the tuple, and reads `fibAnd` only when it is applied, after the block is initialized. `x = Tuple 1 x` is not, reading `x` while building it. Standing inside a lambda is not enough on its own, a lambda applied at once, `x = (\_ -> x) ()`, reading the reference during initialization all the same. How a block is judged, conservatively and decidably, is settled where it is elaborated ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

**A local signature's type variables are in scope in its definition**, as a top-level signature's are ([Type variables](#type-variables)).

## Type variables

**A type variable is bound by a `forall`, by the parameters of a declaration, or implicitly by a signature.** The variables of one `forall`, or of one declaration's parameters, are one group: a name bound twice in it is an error, and a reference reaches the first. A `forall` inside another binds over its own body, and a variable it binds hides one of its name outside it ([Shadowing](#shadowing)).

**A signature quantifies implicitly** the type variables it mentions that nothing around it binds, outermost and in the order they first appear: `f :: b -> a -> b` is `forall b a. b -> a -> b`. A signature is that of a value, a computation, a foreign, a handler, or a `let` binding.

**The variables a signature quantifies are in scope in what it is the signature of**: in the parameters and the body of the definition, its `where` among them, and in the signatures and annotations nested there, which quantify only the variables they mention beyond those. They are the ones it quantifies implicitly and those the `forall`s on its spine bind, wherever they stand among its constraints and synthesized arguments, and, for a capability translation, the `forall`s in front of `~>`.

```stella
f :: forall a. a -> a
f x = go x
  where
    go :: a -> a      -- the a of f's signature; go quantifies nothing
    go y = y
```

**Any other type binds nothing implicitly**, so a variable no binder binds is an error there: an annotation `e :: τ`, a field of a constructor, and the right side of a synonym, where the declaration's parameters are what is in scope.

**An operation's signature is the exception among signatures: it quantifies nothing implicitly.** The parameters of its effect are in scope in it, and a variable of its own is written in a `forall`: `abort :: forall b. Unit ->* b`. A variable neither binds is an error, which catches a misspelt parameter of the effect; admitting implicit quantification later accepts more programs and refuses none.

## Shadowing

**A name written in source may hide another of its namespace.** A binding hides what its name referred to outside it, and an open hides what a name referred to outside the construct. **A binding that hides is warned of, and so is an open that hides a local binding; an open that hides a top-level name is not**, since opening a module is how an author says that its names are the ones meant there.

| What hides | What is hidden | |
| --- | --- | --- |
| a local binding | an enclosing local binding | warned |
| a local binding | a top-level or imported name, or a name an open brings | warned |
| a top-level declaration | an imported name | warned |
| a name `M.( … )` opens | a local binding outside it | warned |
| a name `M.( … )` opens | a top-level or imported name | not warned |
| a name an inner `N.( … )` opens | a name an outer `M.( … )` opens | not warned; the inner takes precedence |
| a type variable | an enclosing type variable | warned |

- **A name that brings the same entity again hides nothing**, and no warning concerns it. An unqualified import of `a` and a qualified one through `M` reach one entity, so `a`, `M.a`, and `M.( a )` are the same reference.

```stella
import M (a)
import M as M

x = a           -- M.a
y = M.( a b )   -- M.a M.b, no warning
```

```stella
a :: Int
a = 42

f :: forall a b. a -> b -> b
f a = \a -> a      -- two warnings: the parameter hides the top-level a, and the lambda's hides the parameter
```

- **One binding group binding a name twice is an error**, and not a hiding: `\x x -> …`, a record pattern binding one name twice, and two bindings of one name in a `let` block, a name a definition binds and a variable of a pattern binding among them. A reference reaches the first ([Surface AST](08-Surface-AST.md)).
- **Names in different namespaces do not hide each other.** The value `a` and the type variable `a` above are unrelated, and so are a cell and a value variable of one spelling.
- **A cell of a group hides an outer cell of its name throughout the group.** A group written in a clause of a handler with cells sees that handler's cells besides its own; its own clauses reach its cell, and in its initial values and `return` clause, where its own cells are closed, a name it declares reaches neither cell. A handler with cells applied inside a clause of another handler with cells is rejected all the same ([Effect Handlers](02-Effect-Handlers.md)), so no accepted program has two cell scopes nested; the rule fixes which cell a name reaches until that is reported. A handler with cells inside a clause of one without them is the ordinary case. Which construct owns a cell is to be revised, and the rule with it ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).
- **Kind variables do not shadow.** Each is bound by the declaration it appears in, once and at the front (D3), and no binder of a kind variable stands inside another.

### Generated bindings shadow nothing

**A binding that desugaring introduces is fresh**, under a name no source can write, so it never hides a name written in source and no warning concerns one. A binding a macro introduces is kept from capturing a name written in source by hygiene. Either capturing one would make a name refer to a binding its author did not write, which is a defect of the compiler rather than something to warn the author of.
