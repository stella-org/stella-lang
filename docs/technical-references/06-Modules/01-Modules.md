# Modules and Declarations

## Structure

```text
module ::= module M where
             import M1 ; … ; import Mn
             export ē
             decl1 ; … ; decln

decl ::= data    T forall k̄. (ā : κ̄) = Ctor_1 τ̄1 | … | Ctor_n τ̄n   [newtype]
       | effect  E (ā : κ̄) where op1 : σ1 ; …
       | foreign [#observ(none)] f : σκ
       | nonrec  x : σκ = e
       | rec     { x1 : σκ1 = v1 ; … }
       | attribute a τ̄ (ℓ1 : τ1 [= c1]) …
       | @[ attr ] decl

σκ ::= forall k1 .. kn . σ                (empty for most declarations)
```

`forall k̄.` may be omitted from any declaration that admits one, and an `effect` declaration admits none ([Kinds](../03-Typed-Core/01-Kinds-and-Types.md)). A declaration that binds kind variables is instantiated at each use site by `[[κ̄]]`.

**The order of value declarations is a dependency order.** A `nonrec` does not refer forwards, and every cycle is contained in a `rec` group.

`import` records the dependencies of the module: those name resolution established, and the module of every reference elaboration wrote, which may be one the header reaches only transitively when a synthesizer chose an entry there ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)). Since every Core name is fully qualified, `import` has no effect on type checking; it is retained for build ordering and linking.

## Modules are namespaces

Stella's modules are namespaces, as PureScript's are. There is no ML-style module system (D22): no functors, no sealing by signature, no first-class modules.

**Data abstraction is provided by export lists.** Exporting a type without its constructors yields an abstract type.

```purescript
module Stack (Stack, empty, push, pop) where
  data Stack a = Nil | Cons a (Stack a)     -- the constructors are not exported
```

This is a decision, but it also follows from the shape of Core. Every Core name is fully qualified and module boundaries vanish during name resolution. Were modules functors, Core would have to express functor application and signature matching, and the trusted core would grow by an order of magnitude.

Strengthening the module system remains possible, but it would require returning to the design of Core.

### An entry only elaboration names

**A reserved module may hold an elaboration-only entry**: a constructor whose Core identity is a name that belongs to no source grammar, which a desugaring the compiler carries out refers to and nothing else does. It is the one exception to export lists being what data abstraction is, and it is narrow by construction: **the compiler lists the entries by name**, and a `Base` module is source only the package implementing the ABI may supply (D26), which package resolution verifies.

**The module declares it in ordinary source, and name resolution gives it its internal identity.** The constructor is written under an ordinary name with the attribute `@[elaborationOnly]` on the declaration of its type. When the module is resolved, the source constructor binder is mapped to the internal qualified name the list gives, and that name is the constructor's identity from there on: its `CtorDecl`, every application of it and every pattern on it inside the module, the full signature built from the module, its `ExportCtor`, and the `.dmo` all use the internal name, and none of them the ordinary one. It is not a renaming at export, which Core would not admit: an `ExportCtor` names a constructor the signature declares under that same name. **The ordinary name exists in the declaring module's source alone**, where it resolves to the internal identity as any constructor's name resolves to its own, which is how the module writes the functions over it. **The list fixes the declaration whole**: its module, its type, whether it is a `newtype` or a `data` declaration, and its one constructor. The attribute is an error on a declaration that differs from an entry in any of these — another constructor, another form, a constructor besides — and so in any module but the ones listed; the declaration is then what it would be without the attribute.

```stella
module Base.Continuation (Continuation, continue) where

@[elaborationOnly]
newtype Continuation a b (r :: Row Effect) = Continuation (a -> b / {| ...r |})

continue :: forall a b r. Continuation a b r -> a -> b / {| ...r |}
continue (Continuation f) = f
```

**The list fixes the correspondence**, so that an implementation has one answer: which module may declare the entry, the type and source constructor the attribute is on, and the internal identity that constructor takes.

| Module | Type | Form | Source constructor | Internal identity | Referred to by |
| --- | --- | --- | --- | --- | --- |
| `Base.Continuation` | `Continuation` | `newtype` | `Continuation` | `Base.Continuation.$Continuation` | the desugaring of a `reifiable full` clause ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)) |

- **It is exported as any constructor is**, under its internal identity, and its `ExportCtor` is generated apart from the surface export list: its type is in the signature built from the module, which the Core type checker reads, and a linker finds it among the constructors a `.dmo` describes ([Interface](../05-Backend/03-Interface.md)).
- **No source outside the declaring module reaches it.** Its name, beginning with `$`, is no identifier ([Lexical Structure](../02-Surface-Language/04-Lexical-Structure.md)), so name resolution never resolves it, and an import list, a re-export, and a macro cannot spell it. **Nor does `(..)`, which selects constructors without naming them**: after the type, in an export list, an import list, or a re-export, does not enumerate it, and importing the whole module does not bring it in. Naming it under its ordinary name is an error, in the declaring module's export list, `Continuation(Continuation)`, as anywhere else; that list writes the type alone, which is what keeps it abstract to source. An editor does not offer it, and a list of a module's API leaves it out.
- **No synthesizer reaches it.** The catalog a synthesizer reads omits it, and the kernel refuses a global reference to it ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)).
- **The Core type checker does not enforce any of this.** A reference to it is checked as an ordinary reference, whoever wrote it. The restriction is a property of surface elaboration and its trust boundary, and a hand-written Core module is outside it.

**The module that holds one is a dependency like any other.** A module whose desugaring refers to an elaboration-only entry imports the module holding it, so its header still names every dependency.

## Local open and header completeness

ML's `M.( … )`, which brings `M`'s names into scope unqualified within one expression, is worth having in surface syntax.

PureScript has a property worth preserving:

> **A module's dependencies are determined by its header alone.**

A build system can read the header to construct the dependency graph, making incremental builds and parallel compilation planning cheap. OCaml lacks this property and must scan module bodies for capitalized identifiers.

The property is lost only if local open makes a header entry unnecessary. It need not.

The key is to **separate declaring a dependency from introducing names into scope**.

```purescript
module Main where
  import      Data.List                      -- dependency; unqualified names module-wide
  import      Data.Map    as M               -- dependency; M.x available module-wide
  import lazy Data.Array  as DA              -- dependency; nothing enters scope

  f xs = DA.( length xs + 1 )                -- DA is opened only here
  g xs = import DA in length xs              -- the block form does the same
```

**All three record the dependency in the header**, so header completeness holds in every case and a build system need read no further.

`import lazy M as A` is the only form that satisfies both of the following at once.

- The brevity of unqualified names, **confined to a region**
- **No pollution of module scope at all**, since `A.x` is not available module-wide either

`import M as A` combined with `A.( … )` fails the second, since `A.x` remains usable everywhere. The property ML's `let open` has is reproducible only with a header form of this kind. Local open itself applies to either alias, with one rule for what it opens ([Name Resolution](../02-Surface-Language/06-Name-Resolution.md)).

`A` is not a value, nor a type, nor a module, since modules are not first class. It is a **namespace token** usable only in local-open position — a new kind of binding, which the name resolver keeps in its own namespace.

**None of this reaches Core.** Local open and `lazy` are concerns of name resolution; by the time a term reaches Core, names are fully qualified and hygiene is resolved. Neither the judgements nor the grammar change.

## Data declarations and constructors

A data declaration supplies, for each constructor:

- a complete type, `Ctor : forall k̄. forall (ā : κ̄). τ1 -> … -> τn -> T ā`, with pure arrows throughout
- a tag, unique within the type
- an arity
- field types

The `forall k̄.` is a kind scheme and is normally empty. The representative case in which it is not is `Proxy`.

```text
data Proxy forall k. (a : k) = Proxy
  -- Proxy : forall k. k -> Type                      the type constructor's kind scheme
  -- Proxy : forall k. forall (a : k). Proxy [[k]] a  the data constructor's kind scheme
  --                                                  tag 0, arity 0
```

Kinds are written explicitly at the use site: `Proxy [[Type]] [Int]` gives `k := Type`, and `Proxy [[Row Type]] [r]` with `r : Row Type` gives `k := Row Type`. Type constructors and data constructors carry independent kind schemes, so instantiation occurs separately in type and term position.

Everything CoreFn carries in its `Constructor` node and `Meta.IsConstructor` lives here, so no constructor-specific term node is needed and `M.Ctor` is an ordinary global variable.

The `newtype` flag does not affect semantics; it tells the backend that the representation may be erased. **The Core type checker nevertheless verifies the shape**: a declaration marked `newtype` must have exactly one constructor with exactly one field. Erasing a representation without that check would corrupt the run-time representation of Core that has passed type checking, so the flag is not a trusted unchecked input.

## Foreign declarations

```text
foreign [#observ(none)] f : σκ
```

The kind scheme is normally empty. The Core type checker does not examine a `foreign`'s implementation; it trusts the declared type.

**The declared type is restricted to what can cross the boundary** (D44). Each
argument and the result must be a scalar, `Unit`, or an `intrinsic opaque` **other
than `Prim.IO`**; the result alone may be `IO τ`, for a `τ` that could itself have
crossed. A data type, a record, a variant, a function, or a continuation is refused
here.

**`Prim.IO` is excluded from the general case for a reason worth naming**, being an
`intrinsic opaque` like any other and so admitted by that clause without this. What
an `IO` value is, though, is the executing machine's own — a shape it takes apart
(D25) and not a payload a host may be handed — so it is not opaque **to the runtime**
in the way the word means here. `IO` crosses in one direction and one position: as a
result, where the host returns an action and the boundary wraps it. **Here is the only place it can be refused**, the type
existing nowhere downstream: a `.dmo` carries none
([Bytecode](../05-Backend/01-Bytecode.md)), so a declaration that got past this would
reach a boundary with nothing to marshal it by.

**What crosses for an abstract type is a wrapper written in Stella.** The discipline
is the one any backend boundary asks for — declare the transparent thing, and unfold
the abstract one into it above.

```text
foreign draw : Picture -> Unit        refused, `Picture` being a data type
foreign drawAt : Int -> Int -> Unit   declared, and `draw` is written over it
```

### `#observ(none)` asserts the absence of an observational effect

An effect belongs to one of three classes — **proper**, which a row carries and a handler deals with; **reified**, a computation a classical monad has made into a value, `IO` among them; and **observational**, whatever a saturated application may do besides returning its value, which appears in no type and which no handler deals with ([Semantics](../03-Typed-Core/06-Semantics.md)). The classes are not exclusive, and the third is what a mutable array behind a pure interface has: `Base.Array.unsafeSet` writes, and its declared type says `Unit`.

**`#observ(none)` asserts that a saturated application has no observational effect, and the assertion is strong.** Such an application reads and writes no hidden state, **produces no fault**, creates no identity anything can observe, performs no external effect where it is applied, and returns observationally equivalent results for observationally equivalent arguments — beside terminating, applying no Stella function value, and throwing nothing, which every entry owes in any case. **A declaration carrying no directive is read as one that may observe.** There are two rules and no third.

**Faulting is not a separate axis.** An entry may fault exactly when it does not carry the annotation, so `Base.String.codePointAt` faulting outside its range is an outcome its declaration admits, while a `#observ(none)` entry that faults is an implementation in breach. Grading observational behaviour more finely buys nothing: what lies past this boundary cannot be characterized, which is why Stella reaches for FFI sparingly to begin with (D19).

**What it says nothing about is the reified class.** Returning `IO` is read off the result type, and the two compose: `#observ(none) foreign log : String -> IO Unit` performs nothing when applied and merely constructs an action.

**One declaration, and two routes to an implementation.** Whether the machine supplies the implementation or a host does is settled after lowering — an operation in the first case and a foreign call in the second ([Prim and Base](02-Prim-and-Base.md)) — and the surface knows neither. The declaration is one form, and its type, its arity, and its observational contract are common to both routes. **Which route a name takes decides whose bug a violation is, and nothing else**: a `#observ(none)` entry the host implements that faults is a defect in that implementation, and one the machine implements that faults is a defect in the machine.

**The Core type checker records the annotation and verifies nothing of it.** There is nothing here to verify: an implementation is not examined, its type being trusted. `newtype`'s shape is not the parallel case — that flag makes a claim about the declaration itself, which is why the shape *is* checked — while this one claims a property of code the checker never sees, so it stands with the rest of what `Σ ⊨ G` obliges an implementer to ([Semantics](../03-Typed-Core/06-Semantics.md)). Nor can a machine check it while running: hidden mutation was never observable from the outside, so a fault reaching Steam cannot be told from a permitted one. Conformance tests and the implementer are what carry it.

Writing it is what lets an optimizer drop, share, or move a call, and the fact travels there through the interface file rather than through a `.dmo` ([Interface](../05-Backend/03-Interface.md)).

### Every arrow in a `foreign` type is pure

**Every arrow in a runtime-bearing position of a `foreign` type must have an empty effect row** (D23), on the argument side as well as the result side. Effects on the outside world are expressed by **returning `IO`**.

A runtime-bearing position is anywhere a value passes through, the payload of a row element included: `Record ( cb : a -{ρ}-> b )` hands a callback across the boundary as an argument does. A constraint is excluded, being an erased proposition that carries no value; neither handler bypass nor a leaking calling convention can arise inside one.

```text
foreign Js.Console.log : String -> IO Unit                 ← correct
foreign Js.Console.log : String -{( Console )}-> Unit      ← not admitted
```

The reason is soundness. `handle` intercepts only `perform`, whereas a `foreign` application calls the implementation directly. An effectful `foreign` would therefore let a handler remove the effect from the row while the actual effect **bypasses the handler's clauses**.

```text
-- were foreign log : String -{( Console )}-> Unit admitted
handle (log "x") with { handles Console ; … full log (s,k) -> … }
-- the type removes Console, yet the output never reaches the clause
```

Returning `IO` closes this. `Js.Console.log s` merely **constructs a value** of type `IO Unit`; the effect occurs when the runtime executes the `IO` (D20). Note that D23 constrains the declared type, not the implementation: that the implementation actually does nothing when applied is a conformance obligation on the backend ([Semantics](../03-Typed-Core/06-Semantics.md)). Handleable effects travel only through `perform`, and native effects only through `IO`.

The same rule forbids effectful arrows on the argument side, for a different reason.

```text
foreign mapImpl : forall a b. forall (e : Row Effect).
                  ( a -{e}-> b ) -> Array a -{e}-> Array b     ← not admitted
```

An argument arrow with a non-empty effect row would have the FFI call back into effectful Stella code. An effectful Stella function is not a host function the implementation can simply call: whatever represents a continuation — frames and a run loop of the backend's own, or continuation-passing style ([JavaScript](../05-Backend/05-JavaScript.md)) — has to see the call, so a JavaScript implementation calling `cb(x)` naively either receives something that is not the value or runs the callback outside the handlers installed around it. **The lowering's calling convention would leak across the FFI boundary.** PureScript does not face this because `Effect a` is a plain thunk `() -> a`; algebraic effects afford no such thing.

D23 therefore closes two holes with one rule: the result side prevents handler bypass, the argument side prevents the calling convention from leaking.

The rule is syntactically checkable.

**The declared type is curried; the implementation is not.** `foreign writeAt : Int -> String -> IO Unit` declares arity 2, and a **saturated call hands both arguments at once**, so a JavaScript `function writeAt(n, s)` is the implementation and nothing binds it as `(n) => (s) => …`. A partial application is not the implementation's concern: `writeAt 0` is a value in its own right and nothing reaches the implementation until the second argument arrives, which is what a machine holds a partial application for (D30, [Bytecode](../05-Backend/01-Bytecode.md)). Under D23 this is a question of arity rather than of when effects occur. That neither `writeAt 0` nor `writeAt 0 "x"` does anything follows from the implementation conforming to condition (3) of `Σ ⊨ G` ([Semantics](../03-Typed-Core/06-Semantics.md)); D23 constrains the declared type, not the implementation.

### Uncurried FFI

To avoid a chain of closures, PureScript uses `Fn2` through `Fn10`. The equivalent in Stella is a family of n-argument function types, which are manifest intrinsics of `Base.Function.Uncurried` rather than part of `Prim` ([Prim and Base](02-Prim-and-Base.md)). **What the family is for here is an uncurried function value** — one a program stores, passes, or returns — and not the arity of an implementation, which the rule above settles.

**The family takes no effect row.** Since `runFn2`'s result arrow must also be pure, admitting `Fn2 a b ρ c` would make `runFn2 : Fn2 a b ρ c -> a -> b -{ρ}-> c` undeclarable.

```text
Base.Function.Uncurried.Fn2 : Type -> Type -> Type -> Type
foreign Base.Function.Uncurried.runFn2 : forall a b c. Fn2 a b c -> a -> b -> c
```

External effects are expressed, as everywhere else, by an `IO` result.

```text
foreign primWriteAt : Fn2 Int String (IO Unit)

-- runFn2 primWriteAt 0 "x" : IO Unit   constructs a value; the runtime performs the effect
```

**One family suffices.** PureScript needs `Data.Function.Uncurried.Fn2` for pure functions and `Effect.Uncurried.EffectFn2` for effectful ones; in Stella `Fn2 a b (IO c)` covers the latter, because being uncurried and having effects are orthogonal.

These belong to the ABI surface rather than to Core. To Core, `Fn2` is an ordinary type constructor and `runFn2` an ordinary `foreign`.

### FFI supplies leaf operations

The restrictions above follow from a single principle.

> **FFI supplies leaf operations. Higher-order control structures are written in the language.**

`map`, `traverse`, and `fold` are control structures, not leaf operations. They are written in Stella, and FFI supplies only pure components.

```text
foreign Base.Array.length      : forall a. Array a -> Int
foreign Base.Array.unsafeNew   : forall a. Int -> Array a
foreign Base.Array.unsafeSet   : forall a. Int -> a -> Array a -> Unit
foreign Base.Array.unsafeIndex : forall a. Array a -> Int -> a
```

A `Base` signature mentions only `Prim` types and portable manifest intrinsics, so no leaf here takes a `List`: `List` belongs to `Prelude`, and converting between the two is `Data.Array` ([Prim and Base](02-Prim-and-Base.md)).

On top of these leaves, `mapArray` is Stella code, written in `Data.Array`.

```purescript
mapArray :: forall a b. (a -> b / {| ... |}) -> Array a -> Array b / {| ... |}
```

It traverses with `unsafeIndex` and builds its result with the construction its own module provides. Should mutable arrays be wanted, their operations are declared as leaves returning `IO`, and `mapArray`'s type returns `IO` accordingly.

Since `f` is called from the Stella side, the execution model sees every call it makes and **the calling convention never crosses the FFI boundary**.

This is the standard arrangement for a language with algebraic effects. Koka writes `list/map` in Koka and reserves `extern` for leaves.

**What is lost is a fast path, not expressiveness.** Even when the effect row is empty, the Stella loop runs rather than JavaScript's `Array.prototype.map`. A pure variant would be declared as a separate `foreign`, every arrow of its type being pure.

```text
foreign Base.Array.mapPure : forall a b. (a -> b) -> Array a -> Array b
```

**No such entry is admitted yet, and the obstacle is not the FFI surface.** An implementation of `mapPure` applies the function it is given, and `Σ ⊨ G` condition (3) forbids a `δ_f` from applying a Stella function value at all: the reduction rule for a saturated `foreign` is one atomic step, and an application that diverges would leave it stepping to nothing ([Semantics](../03-Typed-Core/06-Semantics.md)). What admitting one takes is recorded with the question ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

Forcing authors to choose between the two is undesirable, so the intended resolution is for `mapArray` to be an elaboration macro that inspects the effect row and emits the pure entry where the row resolves to empty and the Stella loop otherwise. This is exactly the typed transformation that the metaprogramming design provides. It waits on two things: the Phase B foundation, and the operational model that admits a higher-order entry at all. The equivalence of the two is asserted by the library, not derived by the compiler.

### Keeping the FFI surface small

**Stella uses FFI far more sparingly than PureScript** (D19).

Mid IR is required not to leak JavaScript functions and objects, Wasm GC structs, or linear-memory layouts into backends. **FFI is the only path around that requirement.**

PureScript's FFI is powerful, and the power has costs.

- **Implementations are raw JavaScript** and unusable from other backends, so every library with FFI must be rewritten per backend.
- **FFI code depends on the representation of values.** Writing `xs.length` binds every backend to representing `Array` as a JavaScript array; code touching records as JavaScript objects or ADTs as tagged objects does the same. The freedom to choose a different representation — a Wasm GC struct, a layout in linear memory — is lost.
- **Behaviour absent from the type is not declared**: exceptions, whether the function retains a reference it was given, whether it holds a resource open.

Authors of alternative backends are consequently forced to reimplement FFI and to track representation choices.

Stella's policy:

1. **Leaf operations only.** Control structures are written in the language.
2. **Keep the ABI surface small, explicit, and versioned.** The ABI entries of `Base.*` are the FFI a backend implements, versioned and graded by profile ([Prim and Base](02-Prim-and-Base.md)); everything else is Stella code.
3. **Do not depend on representation.** Types appearing in `foreign` declarations should be restricted to those with a declared ABI. Passing a `Record r` or a user-defined ADT raw fixes its representation for every backend.
4. **Separate per-backend implementations.** A `foreign` declaration — a name and a type — lives in the module; implementations are per-backend artifacts. Adding a backend must not require editing modules.

This is the same shape as the small trusted core. A small Core protects soundness against metaprograms; a **small ABI surface protects backend independence against FFI**. Only the adversary differs.

Of these, the Core type checker enforces only the first, through D23. The rest are conventions of the standard library and the build system.

## Attributes

```text
module TC
  attribute instance

module Main
  @[ TC.instance ]
  nonrec eqInt : Record ( eq : Int -> Int -> Boolean ) = …
```

An attribute is declared by a declaration of its own, and a declaration carries the attributes attached to it: each the attribute's qualified name and its arguments, which are constants ([Attributes, Modifiers, and Directives](../02-Surface-Language/07-Attributes-Modifiers-and-Directives.md)).

An attribute **has no meaning for the Core type checker**, which checks that its arguments have the types its declaration gives them and nothing else. No term refers to an attribute, and nothing of one reaches a `.dmo`.

Attributes exist so that a resolver can search for declarations carrying one. They must therefore be persisted in a compiled module's interface and be queryable from elaborators in other modules ([Elaboration](../02-Surface-Language/01-Elaboration.md)).

Which attributes there are is decided by the libraries declaring them, and what one means by whatever reads it. The compiler records them and answers for them, and is a reader of the few `Prim` declares for it.

## A package's files

**A file's path names the module it holds.** A package keeps its sources in **source directories**, each holding the modules named under a prefix, and a module's name is the prefix of the directory its file stands in, then the file's path from there. The source directories are given to a build, and where none are named a package has two:

| Directory | Prefix | Path | Module |
| --- | --- | --- | --- |
| `src` | none | `src/A/B/C.stel` | `A.B.C` |
| `test` | `Test` | `test/A/B/C.stel` | `Test.A.B.C` |

- **Each directory under a source directory, and the file's name without `.stel`, is a segment of the name**: an upper case letter, then letters, digits, `_`, and `'`. A path with any other segment names no module, so `src/A.B.stel` is no name for `A.B`.
- **A name belongs to the source directory with the longest prefix it falls under**, and a file whose name belongs to another directory than the one it stands in is an error: `src/Test/A.stel` would be `Test.A`, which `test` keeps.
- **The source directories name their modules apart**: each prefix is made of segments a name may hold, no two directories share a prefix, and none stands in another.
- **A header naming another module than its path does is an error**, reported where the name is written.

The rule runs both ways, which is what it is for: a tool finds the file of a module it is given the name of — through the directory with the longest prefix the name falls under — without reading a header, and a build knows the name of every module it is given before reading any file. Tests standing beside what they test, in the module itself, are open ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

## A module's interface and the build environment

**A module is compiled on its own, against a build environment the whole build shares.** The environment holds the interface of every module compiled so far; once a module is compiled, its interface is added, and what a module downstream reads of it — for name resolution, for elaboration, and for an optimizer — reaches it that way and no other. The interface is `Stella.Compiler.Interface.Module`, the environment `Stella.Compiler.Interface.Environment`; how an interface is kept in a file is [Interface](../05-Backend/03-Interface.md).

### What an interface holds

| Field | Holds |
| --- | --- |
| imports | the modules its header imports, which are its dependencies (D22); `Prim`, a dependency of every module, is never among them |
| exports | the names it publishes, one table per namespace — value, type, operator, type operator, macro, attribute — and the modules it re-exports whole |
| declarations | every top-level declaration it makes, by what each declares: values, types, effects, operators, type operators, attributes |
| implicit handlers | the implicit handlers it declares, each with the element it handles and the elements it performs in its place ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)) |
| catalog only | the values it publishes to the catalog without exporting them to source ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)) |
| arities | the definitional arity of each value it declares, that a module downstream can reach, and that has one ([Interface](../05-Backend/03-Interface.md)) |

**Names and entities are held apart.** An export is a name as an importer writes it, the entity it is another name for — qualified by the module declaring it — and the way it reached the module: declared there, or imported from a module the header names and re-exported. A type's export also lists the members published with it, a data type's constructors or an effect's operations, each of which is in the value table as well. What an entity is — its scheme, its constructors, its attributes — is held by the interface of the module declaring it and by no other, so a module re-exporting a name holds the name and the way it came, and nothing of the entity. **Core keeps nothing of the way**; it is for a tool, which may offer a name from a module re-exporting it or from the module declaring it.

**The declarations are every top-level declaration, not only those exported.** An exported scheme may mention a type the module keeps abstract or does not export, and Core refers to an entry published to the catalog alone. Which names source may write is the export tables' to say.

| Declaration | Held as |
| --- | --- |
| a value | its sort — a value, a foreign with what it asserts of its observational effects, a handler, a constructor of a type, or an operation of an effect — its scheme, and its attributes |
| a type | its kind scheme, its attributes, and what it is: a data type or newtype with its parameters and its constructors in the order of their tags, a synonym with its parameters and the type it stands for, a foreign type, or an intrinsic with its canonical class |
| an effect | its parameters, its operations — each with its own type variables, its arguments, and the type it resumes with — and its attributes |
| an operator | its associativity, its precedence, and the value or constructor it names |
| a type operator | its associativity, its precedence, and the type it names |
| an attribute | the types of its positional parameters, and its keyword parameters with their defaults |

**A computation is a value whose scheme ends in a computation type**, and a macro a value carrying `Prim.macro`; neither is a sort of its own.

### A scheme as an interface holds it

**An interface holds a declaration's surface scheme, and its Core scheme is derived from it.** Two things a surface signature says are gone from Core: a synthesized argument, which is an ordinary parameter of the dictionary's type in Core (D11) and which an importer must know a goal fills, and a computation type `τ / ρ`, which is a thunk `Unit -{ρ}-> τ` in Core and which a reference forces ([Top-level Computation Declaration](../../proposals/05-Toplevel-Computation-Declaration.md)). Both stand on the **spine** of the scheme — the sequence of its quantifiers, constraints, and synthesized arguments, then what the scheme ends in — and below the spine everything is a Core type.

```text
spine ::= τ                      a Core type, headed by no forall and no constraint
        | τ / ρ                  a computation type
        | forall (a : κ). spine
        | C => spine
        | {{ d :: C τ̄ by f }} -> spine     a synthesized argument, behind a pure arrow
```

- **The Core scheme is derived, never stored beside it**: a computation type becomes `Unit -{ρ}-> τ`, and a synthesized argument a pure arrow from the dictionary's type. The two cannot disagree.
- **A synthesized argument stands on the spine and nowhere else.** One inside the type of an argument, or after an ordinary parameter, is an error where the signature is resolved.
- **A type synonym a type mentions is expanded** in what an interface holds — a scheme, a constructor's fields, an operation's signature, a synonym's own body — so those are read without another module's synonyms. A synonym's declaration stays among the declarations, with its parameters and its expanded body, for a module downstream to expand a reference to it.

### The environment

**The environment begins with `Prim`.** `Prim` has no source; the compiler builds its interface, holding its intrinsic types, `Unit`, and the attributes the compiler acts on ([Prim and Base](02-Prim-and-Base.md)), and every module sees its names without importing it. A header may write `import Prim …` to choose how those names are written, which adds no dependency and no import to the module's interface ([Name Resolution](../02-Surface-Language/06-Name-Resolution.md)).

**`Base` is compiled as any module is**, from source listing its ABI entries as `foreign` declarations. What the ABI manifest supplies is held in the environment beside the interfaces: for each module it names, the intrinsic type constructors that module's declarations are checked with. **What the manifest supplies is intrinsics and nothing else**, which is the trust boundary its reader keeps: a declaration, a scheme, or a constructor in it would be a trusted input no checker sees.

**An interface is added after every module it imports.** One added before an import of its own is refused, and so is a second interface of a module the environment holds, `Prim`'s among them. The environment is therefore ordered as the import graph is, a cycle cannot enter it, and everything a header reaches is there when its module is compiled.

### What a module sees

**A module compiled against the environment sees what its header reaches, and nothing else.**

| | From |
| --- | --- |
| names | the export tables of the modules its header imports, and of `Prim`, opened as the header's `import Prim` says, or unqualified where it writes none |
| entities | the declarations of every module its header reaches, directly or transitively, and of `Prim` |
| the catalog | the same modules as entities ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)) |
| implicit handlers, `Ξ` | the module itself, and the modules its header imports directly |

A name resolves through the first and the entity it stands for is read from the second, wherever it is declared: where `C` imports `B` and `B` re-exports the `x` of `A`, `C` writes `x`, resolves it to `A.x`, and reads `A.x` from `A`'s interface, `A` being reached through `B`. A module reached only through another publishes no name to this one. How names are written — an import list, an alias, `lazy` — selects among the names of the first row and changes none of the other three.

**`Ξ` is taken from direct imports alone, where the catalog is taken from the closure.** An implicit handler is inserted where its plan is unique (D29), so a handler that entered `Ξ` by being reached transitively could make a plan ambiguous because a dependency added an import of its own, a change no header of this module records.

### How a build proceeds

**A build is given the files of a package, in no order it relies on**, its source directories, and the build environment the modules outside it are in. The driver is `Stella.Compiler.Build`.

**Every header is read first.** A header is a module's name and its imports, and since the imports come before every declaration, a file is lexed up to the first item of its block that is no import and no further: what follows decides nothing of what the module imports, and nothing in it — a string left open in a declaration — keeps the header from being read. Each file's name is checked against its path as its header is read.

**The modules are ordered by their imports.** Each stands after every module of the build it imports, and of modules neither of which imports the other, the one given first is taken first. **Modules importing one another are reported before any is compiled**, each of them named.

**Then the modules are compiled one at a time**: a module is read again, compiled, and dropped, and what a build keeps from one module to the next is the build environment alone. **Within a module, what a phase made is held no longer than the next phase reads it**: it is handed to the host as the phase ends — to show, or to write as a file — and the next phase is given what it reads. A build of a large package therefore holds one module's text and the results of one or two of its phases at a time, and no step of it reads the whole program. A module is compiled against the modules of the build it imports as it is against those outside it.

**Every stage of a module runs against one environment, which does not hold the module.** Its interface enters the environment once the module is lowered and its interface assembled, for the modules after it alone, and what a stage knows of the module itself comes from the module. An environment holding the module would let a stage take what the module published for what it is compiling — an optimizer inlining the module's own functions into themselves, or a build reading what an earlier build of the module left behind — so no module of the build may be named as one the environment already holds.

**A module's stages run in this order**: the text is lexed, laid out, and parsed; its syntax is checked for what no later stage reads; it is resolved, its macro calls expanded ([Name Resolution](../02-Surface-Language/06-Name-Resolution.md)); its imports are looked up in the environment, and the signature and the catalog they give are made, with the types the ABI manifest supplies to the module itself; it is elaborated and its Core checked ([Elaboration](../02-Surface-Language/01-Elaboration.md)); the interfaces translation reads are gathered; it is translated to Mid IR, optimized, and lowered to bytecode; and its interface is assembled ([Interface](../05-Backend/03-Interface.md)). **A stage that reports an error is the last that runs**, and every error it reports is reported: what a later stage would make of what an earlier one refused follows from an error already reported. A module that does not compile is the last the build compiles.

**The driver is neutral about effects.** Reading a file, running a macro's parser ([Syntax Extensions and Parsers](../../proposals/09-Syntax-Extensions-and-Parsers.md)), and taking what each phase makes are the host's, handed to the driver as functions over a monad the host chooses; a build that cannot go on is a value the driver returns, and no effect it raises. A parser is run with the interfaces of the modules of the build compiled so far in hand, a macro of the build being declared by one of them. What the host is handed:

| When | What |
| --- | --- |
| a module's compiling begins | how far the build has gone, the file, and the module |
| elaboration ends | the checked Core |
| translation ends | the Mid IR |
| the optimizer begins, after each round that changed the module, and when it stops | the Mid IR, and the round |
| a module is lowered, its interface assembled and added to the environment | the bytecode, the side table locating what it holds in the source, and the interface |
| a module is done | the file, the module, and the warnings compiling it gave |

No pass rewrites a module yet, so the optimizer stops before a first round, and a trace of its rounds holds none. Which files a build is given, and what is done with the bytecode once written — code for a target — are the host's as well.

### What a build reports

**An error of a module is an error of the stage that reported it**: its syntax, text that does not lex or parse or syntax no later stage reads; its resolution, the expansion of its macro calls among it; the environment, interfaces that make no signature or that translation cannot read; its elaboration; and the backend. **An error of the build is about directories, files, and modules**: source directories that do not name their modules apart, a file in no source directory, a path naming no module, a name another source directory keeps, a file given twice, two files naming one module, a header naming another module than its path, a module named as one the build environment holds, a file that cannot be read, and modules importing one another.

**An error names every place it is about**, the one it is chiefly about first. A place is a range of the source: a range in what an expansion produced is taken back to the call written in the source, through every expansion it stands in ([Surface AST](../02-Surface-Language/08-Surface-AST.md)), and a parser that failed is reported where in its input it failed, then at the call. An assignment that broke a row constraint names the equation and the site the constraint came from. An error about the build environment names no place, and neither does a fault of the elaboration mechanism, of translation, or of lowering.

**A fault of the compiler's is said to be one.** The Core checker refusing what was elaborated, the mechanism used against its contract, translation or lowering refusing a checked module, and an interface that does not assemble are reported as internal errors, so that an author tells a program to correct from a compiler to report.

**A warning is resolution's**, each at the place it is about, and is reported with the module that compiled.

### `stellac build`

**`stellac build` builds a package to its build directory**, with the driver above. What it is given:

| Option | Is |
| --- | --- |
| `--workdir` | the root of the package; by default the directory the command runs in |
| `--src` | a pattern, from the root, of the source files to build; given any number of times, and `src/**/*.stel` where none is |
| `--output` | where the build directory goes, `output` by default; a relative path is under the root, and what is absolute is what the host says is |
| `--trace-opt` | a module whose optimizer rounds are traced |
| `--emit-core` | each module's Typed Core as `<M>.core.json`, which this version does not write and warns of |
| `--steam-cmd` | the Steam executable a compile-time session is started with, `steam` by default |

**It writes `<output>/_build/<M>.dmo` and `<output>/_build/<M>.dmi` for each module, as a pair**, once the module is compiled: a module whose pair could not be written in full leaves neither file of it. It writes `<output>/_build/<M>.mir`, the optimizer's trace, for the module `--trace-opt` names. A compile-time session is started where the first macro is called, and none where no macro is; it is closed once the modules are built. **A macro of the package runs from the bytecode the build wrote for its module**: before its parser is run, the session loads that module, after each module of the package it reaches through its imports, and each once; a macro whose module's pair could not be written is not run, and stops the build.

**A build succeeds only where all it was to write was written.** A file a phase could not write fails the build once the modules are built, so that what an earlier build left in the build directory is never taken for what this one made; a session that did not close cleanly fails it too. A build that fails says why, each error at the file and the place it is about, and ends with a status other than zero.

## Declaration typing and the entry point

Term typing checks the interior of declarations; this section gives the rules for declarations themselves.

A top-level right-hand side is checked with **ambient effect row `()`**. Defining a value performs no effects; effects occur when the value, being a function, is applied.

Declarations extend the signature, so the judgement makes `Σ` explicit.

```text
Σ ⊢ decl ⊣ Σ'        declaration checking; Σ' adds the declared names to Σ
```

```text
  σκ = forall k̄. σ      ·, k̄ ⊢ σ : Type      Σ ; ·, k̄ ; · ⊢ e : σ ! ()
  ──────────────────────────────────────────────────────────────────
  Σ ⊢ nonrec x : σκ = e  ⊣  Σ, M.x : σκ

  each i: σκ_i = forall k̄_i. σ_i
  Σ' = Σ, M.x_1 : σκ_1, …, M.x_n : σκ_n            ← register every scheme first
  each i: v_i is a FunVal (D14)
          ·, k̄_i ⊢ σ_i : Type
          Σ' ; ·, k̄_i ; · ⊢ v_i : σ_i ! ()          ← each v_i under its own k̄_i
  ──────────────────────────────────────────────────────────────────
  Σ ⊢ rec { x_i : σκ_i = v_i }  ⊣  Σ'

  σκ = forall k̄. σ    ·, k̄ ⊢ σ : Type    every arrow of σ is pure (D23)
  ──────────────────────────────────────────────────────────────────
  Σ ⊢ foreign [#observ(none)] f : σκ  ⊣  Σ, M.f : σκ [#observ(none)]

     the directive is recorded and nothing of it is checked; absent, the
     entry is read as one that may observe

  ──────────────────────────────────────────────────────────────────
  Σ ⊢ attribute a τ̄ (ℓ : τ = c) …  ⊣  Σ, M.a : (τ̄ ; ℓ : τ = c …)      registered, not yet checked

  Σ ⊢ decl ⊣ Σ'
  ──────────────────────────────────────────────────────────────────
  Σ ⊢ @[ attr ] decl ⊣ Σ'          the attribute is checked by the module rule
```

**An attribute declaration adds an entry to `Σ` and declares no value**: no term refers to one. Declaring it registers it and checks nothing, and neither does carrying one: both are checked once the whole module's signature is complete ([below](#the-module-rule)), so a declaration may carry an attribute declared after it, and a default or an argument may name a value declared after it.

**The local context `Γ` cannot hold kind schemes**, so mutual recursion in a `rec` group cannot be supplied through `Γ`. Since Core's top-level names are fully qualified, every scheme is registered in `Σ` first and each `v_i` is then checked under its own `k̄_i`.

This lets mutually recursive declarations **carry different kind schemes**. A recursive reference is an ordinary global name reference `M.x_j [[κ̄]]`, and kind instantiation is handled by the existing rule.

```text
rec { Main.f : forall k. forall (a : k). Proxy [[k]] a -> Int = …
    ; Main.g : Int -> Int                                       = … Main.f [[Type]] [Int] … }
```

The join point context is empty. Join points do not cross a function boundary, and so do not cross a declaration boundary either.

### Type-level declarations are collected first

`data` and `effect` declarations may be mutually recursive — `data Tree = Node Forest` with `data Forest = Nil | Cons Tree Forest` — which a left fold cannot express. The kinds of every type constructor and effect constructor are therefore collected first.

```text
  from every data declaration   data T forall k̄. (ā : κ̄) = …    T : forall k̄. κ̄ -> Type
  from every effect declaration effect E (ā : κ̄) …    E : κ̄ -> Effect
    where each κ̄ is a qkind (D24)
  ──────────────────────────────────────────────────────────────────
  Σ_ty = Σ_Prim ∪ Σ_ABI(M) ∪ Σ_imp ∪ { all of the above }
```

**An entry arriving through an import is checked as its declaration would have been**, where the signature is assembled: a type constructor's kind scheme, an effect's parameters and operations, and an attribute declaration's parameter types and defaults. An interface is read for its structure alone ([Interface](../05-Backend/03-Interface.md)), so this is where an entry no declaration of this module produced is held to the rules.

`Σ_Prim` is the signature of `Prim` ([Prim and Base](02-Prim-and-Base.md)), which no module imports — a header's `import Prim` selects names and adds no import — and every module may name. `Σ_ABI(M)` is what the ABI manifest supplies to `M` itself, empty for every module it does not name, and the manifest names `Base.*` modules and the target namespaces it describes, and no others; a module holding a manifest intrinsic needs its own entries in scope before its declarations are collected.

Core names are fully qualified, so nothing here can collide the way an unqualified name would: a module declaring `Int` contributes `Main.Int`, which is a different entry from `Prim.Int` and shadows it in no way. What the union does require is that **`Prim` be a reserved module name**, so that no module can supply a second `Prim.Int` — a rival `Base.Int.add` is excluded by package resolution instead, since no property of a Core module distinguishes one ([Prim and Base](02-Prim-and-Base.md)); that a module declare no name twice within one namespace, as it must anyway; and that an entry arriving through two import paths be the same entry, which it is, since a name belongs to the module that declares it.

Under `Σ_ty` the interiors are checked and the signature extended. This stage does not depend on order.

A type constructor entry is **intrinsic** or **data**. Nothing adds a constructor to an intrinsic entry, and `switchCtor` requires a data one ([Typing Rules](../03-Typed-Core/05-Typing-Rules.md)).

An intrinsic entry carries a **canonical-value class** — literal, function, record, variant, or opaque — which says how a value of that type is built and what may examine one. Rules consult it rather than the entry's origin ([Prim and Base](02-Prim-and-Base.md)).

**No Core declaration produces an intrinsic entry.** `data` and `newtype` produce data entries, and a `foreign` declaration declares a value. **A surface `foreign type` adds one to the signature** the module and its importers are checked against — an intrinsic of the class opaque under its module's own name, which no reserved module may declare — and produces no Core declaration ([Foreign Types](../../proposals/06-Foreign-Types.md)). Any other intrinsic reaches `Σ` as part of `Σ_Prim`, which the compiler holds, through the ABI manifest, which a compiler and its backends implement together, or, for a guest synthesizer alone, in the `Stella.Elab` bundle the compiler generates; the module it then belongs to is under `Base`, under a target namespace the manifest names, or `Stella.Elab`, and is imported like any other ([Prim and Base](02-Prim-and-Base.md)).

```text
  Σ_ty ⊢ each constructor type Ctor : forall k̄. forall (ā : κ̄). τ̄ -> T ā  is well formed
  if newtype: exactly one constructor with exactly one field
  ──────────────────────────────────────────────────────────
  a data declaration adds constructors, tags, arities, and field types to Σ

  Σ_ty ⊢ each operation signature op : forall (b̄ : κ̄'). σ ->* τ  is well formed (κ̄' a qkind)
  ──────────────────────────────────────────────────────────
  an effect declaration adds its operations to Σ

  Σ_ty ⊢ foreign f : σκ ⊣ …
  ──────────────────────────────────────────────────────────
  collecting these yields Σ_decl
```

### The module rule

Value declarations are folded from `Σ_decl` leftwards.

```text
  Σ^0 = Σ_decl        each i: Σ^i ⊢ bg_i ⊣ Σ^{i+1}        (bg is a nonrec or a rec)
  every exported name is present in Σ^n
  every attribute declaration: ·  ⊢ each τ : Type, and each default c has τ under Σ^n
  every attached attribute: it names an a ∈ Σ^n, it is normalized, and each argument has its parameter's type under Σ^n
  ──────────────────────────────────────────────────────────
  Σ_imp ⊢ module M where import … ; export ē ; decl_1 … decl_n   ok
```

**Attributes are checked under the signature the whole module contributes**, `Σ^n`, so an attribute and the value or constructor an argument names may be declared anywhere in the module, before or after the declaration carrying it. An attribute declaration's parameter types are closed — well kinded at `Type` with nothing in scope — and a default has its parameter's type. An attached attribute names a declared attribute, is normalized — as many positional arguments as parameters, and every keyword argument in the order declared — and each argument has its parameter's type, by the rules [Attributes, Modifiers, and Directives](../02-Surface-Language/07-Attributes-Modifiers-and-Directives.md) gives. Nothing else about the declaration depends on it.

The right-hand side of `nonrec x : σκ = e` must not refer to `x` itself or to any later value declaration; every cycle belongs to a `rec` group. Elaboration performs the dependency analysis, gathers strongly connected components into `rec` groups, and emits them in topological order. This invariant lets the fold close in a single left-to-right pass.

**The fold is the rule for Core, and the order it folds is settled after elaboration rather than before it.** Elaboration reads a catalog of every name, attribute, and scheme it may resolve against — the imported interfaces and this module's own declarations — assembled before any right-hand side is elaborated, which is what a synthesis goal woken between two binding groups requires. The dependency edges are a separate matter: a synthesizer inserts a reference to the dictionary it found, and an inserted handler is another such reference, neither of which stands in any right-hand side as written. So the strongly connected components and the topological order are computed once elaboration has solved every goal, over the `Global` references the committed right-hand sides actually carry ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)). What the catalog says exists and what a right-hand side refers to are separate, and only the second decides the order.

A design collecting signatures first and permitting forward references is also possible. Stella takes the form of CoreFn's binding groups, in which order carries meaning, because order being readable from the term is what makes Core determine its semantics uniquely.

### The entry point

```text
  ( M.main : IO Unit ) ∈ Σ
  ─────────────────────────────
  M is an executable module
```

Together with D20 this establishes mechanically that unhandled effects are never executed. The type of `main` is `IO Unit`, an ordinary type with no effect row, so a computation carrying effects cannot have it.

A module that is not executable either has no `main` or gives `main` a different type. That is not an error; it means the module is a library.
