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
       | @[ attr ] decl

σκ ::= forall k1 .. kn . σ                (empty for most declarations)
```

`forall k̄.` may be omitted from any declaration that admits one, and an `effect` declaration admits none ([Kinds](../03-Typed-Core/01-Kinds-and-Types.md)). A declaration that binds kind variables is instantiated at each use site by `[[κ̄]]`.

**The order of value declarations is a dependency order.** A `nonrec` does not refer forwards, and every cycle is contained in a `rec` group.

`import` records the dependencies that name resolution established. Since every Core name is fully qualified, `import` has no effect on type checking; it is retained for build ordering and linking.

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

**The module declares it in ordinary source, and name resolution gives it its internal identity.** The constructor is written under an ordinary name with the attribute `@[elaborationOnly]` on the declaration of its type. When the module is resolved, the source constructor binder is mapped to the internal qualified name the list gives, and that name is the constructor's identity from there on: its `CtorDecl`, every application of it and every pattern on it inside the module, the full signature built from the module, its `ExportCtor`, and the `.dmo` all use the internal name, and none of them the ordinary one. It is not a renaming at export, which Core would not admit: an `ExportCtor` names a constructor the signature declares under that same name. **The ordinary name exists in the declaring module's source alone**, where it resolves to the internal identity as any constructor's name resolves to its own, which is how the module writes the functions over it. The attribute is an error on a declaration the list does not name, and so in any module but the ones listed.

```stella
module Base.Continuation (Continuation, continue) where

@[elaborationOnly]
newtype Continuation a b (r :: Row Effect) = Continuation (a -> b / {| ...r |})

continue :: forall a b r. Continuation a b r -> a -> b / {| ...r |}
continue (Continuation f) = f
```

**The list fixes the correspondence**, so that an implementation has one answer: which module may declare the entry, the type and source constructor the attribute is on, and the internal identity that constructor takes.

| Module | Type | Source constructor | Internal identity | Referred to by |
| --- | --- | --- | --- | --- |
| `Base.Continuation` | `Continuation` | `Continuation` | `Base.Continuation.$Continuation` | the desugaring of a `reifiable full` clause ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)) |

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

`import M as A` combined with `A.( … )` fails the second, since `A.x` remains usable everywhere. The property ML's `let open` has is reproducible only with a header form of this kind.

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
@[typeclass.instance]
nonrec eqInt : Record ( eq : Int -> Int -> Boolean ) = …
```

An attribute **has no meaning for the Core type checker**, which ignores attributes entirely.

Attributes exist so that a resolver can search for declarations carrying one. They must therefore be persisted in a compiled module's interface and be queryable from elaborators in other modules ([Elaboration](../02-Surface-Language/01-Elaboration.md)).

The namespace of attributes and the syntax of their values are decided by libraries. The compiler carries a string key and a structured value, nothing more.

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

  Σ ⊢ decl ⊣ Σ'
  ─────────────────────────      attributes do not affect type checking
  Σ ⊢ @[ attr ] decl ⊣ Σ'
```

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

`Σ_Prim` is the signature of `Prim` ([Prim and Base](02-Prim-and-Base.md)), which no module imports and every module may name. `Σ_ABI(M)` is what the ABI manifest supplies to `M` itself, empty for every module it does not name, and the manifest names `Base.*` modules and the target namespaces it describes, and no others; a module holding a manifest intrinsic needs its own entries in scope before its declarations are collected.

Core names are fully qualified, so nothing here can collide the way an unqualified name would: a module declaring `Int` contributes `Main.Int`, which is a different entry from `Prim.Int` and shadows it in no way. What the union does require is that **`Prim` be a reserved module name**, so that no module can supply a second `Prim.Int` — a rival `Base.Int.add` is excluded by package resolution instead, since no property of a Core module distinguishes one ([Prim and Base](02-Prim-and-Base.md)); that a module declare no name twice within one namespace, as it must anyway; and that an entry arriving through two import paths be the same entry, which it is, since a name belongs to the module that declares it.

Under `Σ_ty` the interiors are checked and the signature extended. This stage does not depend on order.

A type constructor entry is **intrinsic** or **data**. Nothing adds a constructor to an intrinsic entry, and `switchCtor` requires a data one ([Typing Rules](../03-Typed-Core/05-Typing-Rules.md)).

An intrinsic entry carries a **canonical-value class** — literal, function, record, variant, or opaque — which says how a value of that type is built and what may examine one. Rules consult it rather than the entry's origin ([Prim and Base](02-Prim-and-Base.md)).

**No declaration produces an intrinsic entry.** `data` and `newtype` produce data entries, `foreign` declares a value and not a type, and the surface has no third form. An intrinsic reaches `Σ` as part of `Σ_Prim`, which the compiler holds, through the ABI manifest, which a compiler and its backends implement together, or, for a guest synthesizer alone, in the `Stella.Elab` bundle the compiler generates; the module it then belongs to is under `Base`, under a target namespace the manifest names, or `Stella.Elab`, and is imported like any other ([Prim and Base](02-Prim-and-Base.md)).

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
  ──────────────────────────────────────────────────────────
  Σ_imp ⊢ module M where import … ; export ē ; decl_1 … decl_n   ok
```

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
