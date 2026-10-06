# Overview

Stella is a pure functional language influenced by PureScript. It is not a PureScript dialect: source compatibility, package compatibility, and semantic compatibility are not goals. Where a more coherent design is available, Stella takes it.

The initial compilation targets are the web — JavaScript and WebAssembly — but the compiler keeps a backend-independent intermediate representation so that native backends remain possible.

## Two central positions

Two choices distinguish Stella from PureScript. Both follow from a single observation: PureScript loads too much work onto type class resolution.

**Rows are a first-class structure in the type system, not something manipulated through type classes.** A dedicated row solver normalizes open rows without closing them. Structural relationships between rows are constraints the solver discharges, not instances a search procedure finds.

**Type classes are a library, not a compiler builtin.** The compiler provides one general synthesis hook. The standard library implements class declarations as syntax macros and dictionary synthesis as an ordinary elaborator.

## What Stella inherits from PureScript

- Pure functional programming by default
- Strict evaluation
- A surface syntax close to PureScript's
- Local type inference in the Hindley–Milner tradition
- Explicit type annotations at library boundaries
- Algebraic data types and pattern matching
- Higher-kinded types
- Row-polymorphic records and variants
- A clear separation between safe code and the unsafe FFI boundary

These are influences, not compatibility requirements.

## A small trusted core

Surface language features elaborate into a small typed Core.

Syntax macros and elaborators can fail, diverge, or produce malformed syntax. They must never cause the compiler to accept an ill-typed Core term. An independent Core type checker validates every Core term that elaboration produces.

This separation is what allows type classes, derive mechanisms, and row-directed metaprograms to grow without enlarging the set of programs whose correctness the compiler vouches for. See [Core Type Checker](../03-Typed-Core/07-Core-Type-Checker.md).

## Compile-time computation is separated by concern

PureScript's type class resolution serves several purposes at once. Stella gives each its own mechanism.

| Mechanism | Responsibility |
| --- | --- |
| Unification and type inference | Infer unknown types and solve type equations |
| Row solver | Normalize rows and discharge structural constraints |
| Type-level evaluation | Evaluate explicit type functions |
| Syntax macros | Transform syntax into syntax, hygienically |
| Elaborator | Build typed Core terms from expected types and the environment |
| Type class resolver | A library elaborator that synthesizes dictionary terms |

In particular, type class resolution is not a substitute for row computation or for general compile-time computation.

## Compiler pipeline

```text
Source
  │ parsing
  ▼
concrete syntax tree
  │ macro expansion, name resolution, desugaring
  ▼
Surface AST
  │ elaboration: type inference builds Core⁺, the solver fills its holes,
  │ and the Core type checker verifies the result
  ▼
Typed Core
  │ lowering of language semantics
  ▼
backend-independent Mid IR
  │ lowering to bytecode
  ▼
.dmo module objects
  ├──────────────────► the Stella virtual machine
  ├── JavaScript IR ──► ES modules
  └── future IRs ─────► native and others

Wasm IR ──► WebAssembly modules      its input, Mid IR or a .dmo, is not yet fixed
```

**The concrete syntax tree** keeps what was written, in the shape it was written, and is what a formatter and an editor read ([Syntax](../02-Surface-Language/05-Syntax.md)).

**Surface AST** is expanded and resolved: it holds no macro invocation and no unresolved name. It carries source-oriented information: implicit arguments, holes, source locations, expansion provenance, and hygiene scopes. It is not a stable optimization interface.

**Typed Core** defines the semantics of the language. It makes explicit: type abstraction and application, evidence and dictionary arguments, record and variant operations, the decision structure of pattern matching, effect operations and handlers, and evaluation order wherever it is observable. The rest of these documents specify it.

**Mid IR** retains useful type information and invariants while depending on no particular backend. It expresses closure construction and application, algebraic data construction and destruction, join points and tail calls, primitive operations, explicit control flow, handler and continuation operations, and abstracted allocation. JavaScript functions and objects, Wasm GC structs, and linear-memory layouts must not leak into this stage. It is an A-normal form, and [Mid IR](../04-MiddleEnd/01-Mid-IR.md) specifies it.

**Bytecode** is the lowering of Mid IR to a machine Stella owns, which can be directly interpreted and executed by its own abstract machine, STEAM, allowing a program to run without relying on the existence of any compiler backends. ([Bytecode](../05-Backend/01-Bytecode.md)). Its continuations are multi-shot, so like the JavaScript backend and unlike the v0.1 Wasm backend it conforms to the reference semantics. Against the Core evaluator it is a second evaluator to compare with, and it runs the programs a one-shot backend cannot; the properties stated over Typed Core stay with the Core evaluator ([Implementation Plan](04-Implementation-Plan.md)).

Its output, a **`.dmo` module object** with the **`.dmi` interface** beside it, is what a backend builds on (D47). Mid IR is an in-memory representation, so the code a backend builds on is the lowered one — erased, in A-normal form, with closures and their captures explicit and decision trees already disjoint — rather than Typed Core.

**The JavaScript backend is handed the pair too**, and its code generator reads the `.dmo` of it (D45), so a first-class backend is what shows the published form is enough to build on, and the machine and the backend run the same lowered program ([JavaScript](../05-Backend/05-JavaScript.md)).

## The tools

**Each tool stops where the next one's knowledge begins** (D47).

| Tool | Does | Stops at |
| --- | --- | --- |
| `stellac`, the compiler command | compiles a package's modules — expanding their macros on a compile-time session it starts — and writes each module's `.dmo` and `.dmi` | the pairs it writes; it knows no backend, and no package of another |
| a backend | is handed a program's pairs, optimizes as it alone can, and makes each module into what its target runs; finishing the program — linking it into one executable — is a capability a backend may have | each module made, or the program finished where it finishes one; a JavaScript or WebAssembly backend may stop at the modules and leave the rest to a bundler |
| `steam`, the machine | runs `.dmo` files, given in dependency order with the entry point ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)) | one program, or one session |
| the package manager | resolves and fetches a package's dependencies, chooses the backend and what is run, and starts the compiler and the backend, handing the backend the pairs | |

**There is no package manager yet**, so a program is built with `stellac build` and run on the machine with `steam run`, which is also the reference a backend is checked against. The boundary is the pair, which `stellac` writes for each module ([Modules](../06-Modules/01-Modules.md)). **What `stellac` does is what needs the compiler's knowledge of the language** — the syntax, the names, the types: a command reading the dependency graph off the headers, or what a package's documentation is made from, belongs with it, and drawing a page, running a program, or managing dependencies does not ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

## Backend strategy

The JavaScript backend is the reference backend. Delegating garbage collection, closures, and module mechanics to the host allows the parser, type system, elaboration, and language semantics to be validated first.

The Wasm backend prioritizes Wasm GC. A backend using linear memory and a custom collector can be added later as a separate lowering.

Effect handlers are the one place where backends differ in what they can implement. See [Semantics](../03-Typed-Core/06-Semantics.md).

## Roadmap

| Phase | Content |
| --- | --- |
| A | Lexer, parser, source spans and diagnostics, name resolution, kind checking, type inference, Typed Core, Mid IR, JavaScript backend |
| B | Hygienic syntax objects, quotation and antiquotation, declaration attributes, typed reflection, metavariable and goal APIs, transactional elaboration, synthesis scheduling |
| C | Library-defined type classes: dictionary record macros, instance declaration macros, the standard resolver, recursive instance search, coherence and ambiguity rules, search trace diagnostics |
| D | Native row programming: canonical open-row representation, row unification and normalization, structural constraints, reflection over known row fragments, residual computation over unknown tails |
| E | Effects and WebAssembly: effect rows in Core, first-order operations and handlers, higher-order and scoped effects, JavaScript runtime strategy, Wasm GC backend, browser interoperability |

Phases A through D require no effect handlers. The Typed Core specified in these documents includes effect rows and handlers from the start so that function types, the FFI boundary, exceptions, and asynchrony do not have to be redesigned when Phase E arrives.

## Examples that validate the design

1. A class-free functional program compiled through every IR to JavaScript
2. `Eq` or `Show` implemented using only the standard metaprogramming library
3. An alternative resolver demonstrating that resolution policy is replaceable
4. A JSON encoder derived from a closed record row
5. Open-row encoder composition that leaves the unknown tail's encoder explicit
6. Lowering of the same Typed Core to both JavaScript and Wasm

These serve as architecture tests as well as demonstrations.

## Document map

| Document | Content |
| --- | --- |
| **§1. Introduction** | |
| [§1.2 Notation](02-Notation.md) | Metavariables, sequences, symbols |
| [§1.3 Design Decisions](03-Design-Decisions.md) | The numbered decisions D1–D47 |
| [§1.4 Implementation Plan](04-Implementation-Plan.md) | Order of implementation work |
| **§2. Surface Language** | |
| [§2.1 Elaboration](../02-Surface-Language/01-Elaboration.md) | Core⁺, metavariables, unification, synthesis |
| [§2.2 Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md) | Handler declarations, clause forms, implicit insertion |
| [§2.3 Elaborator API](../02-Surface-Language/03-Elaborator-API.md) | The two layers, goal records, the attempt transaction, the scheduler |
| [§2.4 Lexical Structure](../02-Surface-Language/04-Lexical-Structure.md) | Tokens, names, operators, literals |
| [§2.5 Syntax](../02-Surface-Language/05-Syntax.md) | The offside rule, the grammar, the concrete syntax tree |
| [§2.6 Name Resolution](../02-Surface-Language/06-Name-Resolution.md) | Namespaces, local open, shadowing |
| [§2.7 Attributes, Modifiers, and Directives](../02-Surface-Language/07-Attributes-Modifiers-and-Directives.md) | What stands with a declaration, and who gives it meaning |
| [§2.8 Surface AST](../02-Surface-Language/08-Surface-AST.md) | What name resolution builds and elaboration reads |
| **§3. Typed Core** | |
| [§3.1 Kinds and Types](../03-Typed-Core/01-Kinds-and-Types.md) | Names, kinds, types, kinding rules |
| [§3.2 Rows](../03-Typed-Core/02-Rows.md) | Row theory, normal form, entailment, surface syntax |
| [§3.3 Effects](../03-Typed-Core/03-Effects.md) | Effect rows, operations, handlers, `IO` |
| [§3.4 Terms and Matching](../03-Typed-Core/04-Terms-and-Matching.md) | Core terms, value forms, join points, decision trees |
| [§3.5 Typing Rules](../03-Typed-Core/05-Typing-Rules.md) | Contexts and the typing rules |
| [§3.6 Semantics](../03-Typed-Core/06-Semantics.md) | Evaluation order, erasure, handlers and continuations |
| [§3.7 Core Type Checker](../03-Typed-Core/07-Core-Type-Checker.md) | What the checker verifies, and what it does not |
| [§3.8 Examples](../03-Typed-Core/08-Examples.md) | Worked examples in Core |
| [§3.9 PureScript CoreFn](../03-Typed-Core/09-PureScript-CoreFn.md) | Correspondence with PureScript's CoreFn |
| **§4. Middle-end** | |
| [§4.1 Mid IR](../04-MiddleEnd/01-Mid-IR.md) | A-normal form, representation types, closures, join points, handlers |
| [§4.2 Translation](../04-MiddleEnd/02-Translation.md) | Typed Core to Mid IR: erasure, spines, decision trees, closure conversion |
| **§5. Backend** | |
| [§5.1 Bytecode](../05-Backend/01-Bytecode.md) | The instruction set, continuations, and the `.dmo` module object |
| [§5.2 Encoding](../05-Backend/02-Encoding.md) | The bytes of a `.dmo`: sections, tags, and opcodes |
| [§5.3 Interface](../05-Backend/03-Interface.md) | The `.dmi`: a module's whole interface, which compiling a module downstream reads |
| [§5.4 Foreign Manifest](../05-Backend/04-Foreign-Manifest.md) | The `foreign-manifest.json`: where a target reaches a module's implementations |
| [§5.5 JavaScript](../05-Backend/05-JavaScript.md) | The JavaScript backend: a module's pair and the program's manifest in, an ES module out, and what the host does not give |
| **§6. Modules** | |
| [§6.1 Modules](../06-Modules/01-Modules.md) | Modules, declarations, FFI, interfaces and the build environment, entry point |
| [§6.2 Prim and Base](../06-Modules/02-Prim-and-Base.md) | The four layers: what `Prim` holds, and what the `Base` ABI surface does |
| **§7. Runtime** | |
| [§7.1 Abstract Machine](../07-Runtime/01-Abstract-Machine.md) | Steam: the bytecode interpreter the REPL runs on |
| [Open Questions](../99-Open-Questions/01-Open-Questions.md) | Questions deferred beyond v0.1 |
