# Name Resolution

This document settles what a name written in source refers to. By the time a term reaches the Surface AST every name in it is resolved, and by the time it reaches Core every name is fully qualified ([Modules](../06-Modules/01-Modules.md)).

## Where it runs

**Resolution and macro expansion are one pass from the concrete syntax tree to the Surface AST**, and they run in stages, because expanding a macro call needs the macro's name resolved and the expansion's result needs resolving in turn.

1. **The import scope** is built from the header alone: what each import makes visible, unqualified and through each alias.
2. **Macro calls are expanded**, and a call an expansion produced is expanded in turn, until no call remains. What this stage resolves is **the name of each call and nothing else**, in the macro namespace. That namespace holds what the imports bring and nothing the module declares, so it is fixed by the header, and the order expansions run in changes nothing a call resolves to. A call inside a local open is resolved against the macros the open brings, the extent of the construct being known before anything is expanded.
3. **The module's top-level scope** is the import scope together with every top-level declaration, those an expansion produced among them.
4. **Every other name is resolved**, against the top-level scope and the bindings around it, whether it was written in source or produced by an expansion. In `f x = m%{ x }`, the `x` an expansion places in the body is resolved here, under the binding of `f`'s parameter, and could not have been at stage 2, where neither the top-level scope nor any local binding exists yet.

### What it produces

**The resolver reads the concrete syntax tree and builds the Surface AST.** The tree keeps every name as written, a qualifier being the alias written and not yet a module, and the Surface AST holds at each position the kind of name that position calls for.

| Position | Name held |
| --- | --- |
| a global value: a value, a computation, a foreign, a handler, a constructor, an operation | `Qualified Ident` |
| a type constructor | `Qualified TyName` |
| an effect | `Qualified EffName` |
| a local value, and a cell | the binding it refers to |
| a type variable | the type binding it refers to |
| a label and a tag | `Symbol` and `Tag`, unresolved |

- **A global is qualified by the module that declares it.** An alias is replaced by the module it stands for, and a name a module re-exports is the entity it was in the module declaring it, so `M.a` after `import Long.Module as M` is `Long.Module.a` where `Long.Module` declares `a`, and `Other.a` where it re-exports the `a` of `Other`.
- **A binding carries the name it was written with**, beside the identity that tells two bindings of one spelling apart, for diagnostics and for the names Core is given.
- **What a name refers to is told by the node holding it.** A reference to a value and a reference to a computation are different nodes, and so are a constructor, an operation, and a discriminator; what else is known of an entity is read from the module's environment and the interfaces, so no resolved name carries it.
- **Every node is annotated with where it came from**: its source range, for a node built from source. What a node an expansion produced carries is fixed with macro expansion.
- **A name that does not resolve is an error node, and resolution carries on**, so that every error in the module is reported; a module holding one is not elaborated.

**An expansion produces declarations and expressions, and never an import or a module header.** The header is what the dependencies are read from (D22), and the import scope has been fixed before any expansion runs.

## Namespaces

**A name is looked up in the namespace its position calls for**, and a name in one namespace never hides a name in another.

| Namespace | Top-level entries | Local binders | Where a name is written |
| --- | --- | --- | --- |
| **value** | values, computations, foreigns, handlers, constructors, operations, synthesizers | value variables | expressions, patterns (constructors), the synthesizer after `by` |
| **type** | data types, newtypes, type synonyms, foreign types, effects | type variables | types, rows |
| **operator** | the operators fixity declarations introduce | none | between operands, and as a value `(++)` |
| **macro** | the macros the imports bring; none the module declares | none | the name of a macro call, `m%` |
| **attribute** | the attributes declared by the module and the imports | none | the head of an attribute, `@[a …]` |
| **module** | none; the aliases `as` introduces and the namespace tokens `import lazy` introduces, which the header declares | none | the qualifier `X.` of a name, and local open |
| **cell** | none | the cells of a handler | `x!` and `x := e` |

**A namespace holds top-level entries and local binders alike, and a local binder hides an entry of its own namespace only.** A value variable may hide a top-level value; a type variable may hide nothing but a type variable, top-level types being upper case and type variables lower case.

- **A constructor is a value.** It is applied, passed, and matched on as one, as in Core, where a constructor is an ordinary global name ([Modules](../06-Modules/01-Modules.md)).
- **An operation is a value.** It is called as an ordinary function, `perform` not appearing in the surface (D17), and it belongs to the effect that declares it.
- **An effect is a type-level name.** It stands in a row as an element, which is a type position.
- **A macro has a namespace of its own, because it is visible where a value is not.** A macro cannot be used in the module declaring it, so the module's own macros are not in its macro namespace and appear only in its exports. `m%` looks `m` up there, and a bare `m` in the value namespace; a value and a macro of one spelling stand together without either hiding the other, and a macro the module declares hides no imported macro of its name. That a macro is compiled to a Stella function is not visible at the source level.
- **A macro produced by an expansion is no different.** It is not in the macro namespace of the module it was produced in, so it affects no later expansion there.
- **Two imported macros of one name are ambiguous where they are called**, and a qualified call, `M.m%( … )`, tells them apart.
- **An attribute is not a value.** It is declared by a declaration of its own and named at the head of `@[ … ]` alone, so it has a namespace of its own, and a value and an attribute of one spelling stand together ([Attributes, Modifiers, and Directives](07-Attributes-Modifiers-and-Directives.md)).
- **An operator is another name for a value.** A fixity declaration `infixr 5 add as +` makes `+` refer to the value `add`. Type operators are not admitted ([Syntax](05-Syntax.md)).
- **A cell is reached through its own syntax alone.** `x!` and `x := e` name a cell, a bare `x` never does, and a cell and a value variable of one spelling stand together without either hiding the other ([Effect Handlers](02-Effect-Handlers.md)).
- **A kind variable is bound by the declaration it appears in**, implicitly and at the front (D3), and is in scope in the kind positions of that declaration alone. `Type`, `Effect`, and `Row` are a closed set of words with that meaning in a kind position, so a kind has no top-level entries to resolve ([Syntax](05-Syntax.md)).

### Discriminators

**A discriminator is derived from a constructor and has no entry of its own** ([Discriminator](../../proposals/04-Discriminator.md)). Meeting `C?`, resolution looks `C` up in the value namespace and resolves `C?` to the discriminator of the constructor it finds; a `C` that is not a constructor is an error.

**It is therefore visible exactly where its constructor is**, under the same qualifier, and nothing exports, imports, or declares one. No other name can collide with one: `C?` is a token of its own, and no declaration names a value ending in `?` ([Lexical Structure](04-Lexical-Structure.md)).

### Labels are not resolved

**A label is a key of a row, and keys are structural.** A record field, the label of an effect instance in `get@cache`, and the label heading a handler group are `SymbolKey`s, which no declaration introduces and no scope holds ([Rows](../03-Typed-Core/02-Rows.md)). Resolution leaves them as written.

### Macro declarations

**A top-level value declaration carrying `@[macro]` declares a macro.** Its name enters the macro namespace of the modules importing it, and no value namespace: no source names it as a value, the declaring module included. It is compiled as a global like any other, which is how an expansion runs it, and what type it must have is fixed with macro expansion.

## Imports and exports

**An import brings names in unqualified or through an alias, never both**, and its list, where it has one, selects which.

| Import | Unqualified | Through the alias |
| --- | --- | --- |
| `import M` | everything `M` exports | — |
| `import M (items)` | the items | — |
| `import M ()` | nothing | — |
| `import M as A` | nothing | everything `M` exports, as `A.x` |
| `import M (items) as A` | nothing | the items, as `A.x` |
| `import lazy M as A` | nothing | nothing outside a local open of `A`; everything `M` exports inside one |

- **Every form declares the dependency**, `import M ()` doing nothing else, and the header is what the dependencies are read from (D22).
- **A reference reaches its entity through the export table of an import the header names**, and the module declaring the entity is then within the transitive closure of the header's imports. It need not be named there: where `C` imports `B` and `B` re-exports the `x` of `A`, a reference in `C` is `A.x`.
- **An unqualified name and a qualified one are written as two imports**, which reach one entity and so do not conflict: `import M (a)` and `import M as M` make `a` and `M.a` the same reference.
- **A lazy import is qualified and takes no list** ([Syntax](05-Syntax.md)).

**What a module exports is its own declarations, or what its export list names.**

| Export list | Exported |
| --- | --- |
| none | every declaration of the module: values, types with their constructors, effects with their operations, operators, macros, and attributes; nothing imported |
| an item naming an entity in scope | that entity, the module's own or imported, qualified or not |
| `module A`, `A` an alias | every name `A.` qualifies, across every import sharing the alias |
| `module N`, `N` imported without `as` | every name that import brings in unqualified |

- **A module does not name itself in its own export list.** `module M (module M, …) where` is an error; a module exporting all of its declarations writes no list.
- **A list is not empty.** `module M () where` is not in the grammar.
- **A lazy alias is not re-exported.** It adds nothing to the module's scope, and `module A` for one is an error.
- **One exported name refers to one entity.** Two items exporting different entities under one name are an error, and an item exporting one already exported is not.
- **An elaboration-only entry is never listed** by any of these forms ([Modules](../06-Modules/01-Modules.md)).

**Imports and exports decide names, and not what a synthesizer may find.** Every module the header reaches contributes to the catalog however it is imported, and an entry may be published to the catalog without being exported to source ([Elaborator API](03-Elaborator-API.md)).

### Naming an entry in an import or export list

**An item of a list names its namespace by its spelling, and a macro, which is spelled as a value is, by the word `macro`.**

| Item | Namespace |
| --- | --- |
| `n` | value |
| `(++)` | operator |
| `T`, `T(..)`, `T(A, B)`, `E(get, set)` | type: a data type with its constructors, or an effect with its operations |
| `macro m` | macro |
| `attribute a` | attribute |

```stella
import M (Maybe(..), State(..), fromMaybe, (<>), macro format)
```

- **A type and an effect need no word of their own.** Both are in the type namespace, where one module declares no name twice, so what the members after the name select — constructors or operations — follows from the declaration, and a member that is neither is an error.
- **`macro` has this meaning in a list alone**, as `as` and `lazy` have theirs in an import, and is an ordinary name elsewhere. `attribute` is a keyword, beginning an attribute declaration.
- **`type` before an item is reserved for type operators**, which are not admitted yet.

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
- **What is opened is what a module can export**: the value, type, operator, and macro namespaces. An attribute is attached to a declaration and so never stands inside an expression, where an open is; `@[M.a]` and an import list reach one. A type in an annotation, an effect in a row, a constructor in a pattern, a discriminator, an operator, and a macro call inside `e` are resolved by the same rule; an operator opened this way takes its fixity from `M`. Local binders and cells are not a module's to open.
- **What is opened is an alias.** A module imported without `as` has no qualifier, so its full name cannot be opened.
- **The header still names every dependency.** The alias is declared by an import in either case, so local open adds nothing a build reads ([Modules](../06-Modules/01-Modules.md)).

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

- **One binding naming a variable twice is an error**, and not a hiding: `\x x -> …`, a record pattern binding one name twice, and two bindings of one name in a `let` block.
- **Names in different namespaces do not hide each other.** The value `a` and the type variable `a` above are unrelated, and so are a cell and a value variable of one spelling.
- **Cells do not shadow cells.** A cell is reached from the operation clauses of the handler declaring it, and a handler with cells applied inside a clause of another handler with cells is rejected ([Effect Handlers](02-Effect-Handlers.md)), so no accepted program has two cell scopes nested. A handler with cells inside a clause of one without them is the ordinary case. Which construct owns a cell is to be revised, and rules for one cell hiding another come back with it ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).
- **Kind variables do not shadow.** Each is bound by the declaration it appears in, once and at the front (D3), and no binder of a kind variable stands inside another.

### Generated bindings shadow nothing

**A binding that desugaring introduces is fresh**, under a name no source can write, so it never hides a name written in source and no warning concerns one. A binding a macro introduces is kept from capturing a name written in source by hygiene. Either capturing one would make a name refer to a binding its author did not write, which is a defect of the compiler rather than something to warn the author of.
