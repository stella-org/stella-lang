# Semantics

Evaluation is strict and call-by-value. Because effect rows expose the points at which effects occur, Core must fix the evaluation order.

## Evaluation order

| Construct | Order |
| --- | --- |
| `e1 e2` | `e2` → `e1` → apply |
| `extend k e1 e2` | `e1` → `e2` |
| `update k e1 e2` | `e1` → `e2` |
| `merge e1 e2` | `e1` → `e2` |
| `let x = e1 in e2` | `e1` → `e2` |
| `case (e1 … en) of dt` | `e1` → … → `en` → `dt` |
| `jump j (e1 … en)` | `e1` → … → `en` → transfer |
| `perform k.op [τ̄] e` | `e` → capture the continuation |
| `handle e with h` | install the handler → `e` |
| `handle e with h @ (e1 … en)` | `e1` → … → `en` → open the region → install the handler → `e` |
| `writeCell k e` | `e` → replace the cell |

**`e1 e2` evaluates the argument before the function** (D35). Application is the
only construct of which that is true; every other row above reads left to right.

Since application is left-associative and each argument is evaluated before the
function it is applied to, a spine is evaluated **right to left**, and the
applications then happen left to right.

```text
f x y z   is   (((f x) y) z)

z → y → x → f → apply f x → apply that result y → apply that result z
```

An argument therefore reaches a value before anything the callee does, however
deep the spine. What this buys is that a whole spine can be collected into one
multi-argument call without moving any effect ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)).
Under the opposite order the evaluation of `f x` — which may perform, fault, or
diverge — stands between the arguments, so `f [x, y]` would reorder them.

The order is observable and is part of the language rather than a convention of
one backend. `f (perform A.x Prim.Unit) (perform B.y Prim.Unit)` performs `B.y`
first, and a fault or a divergence in a later argument happens before the callee
or any earlier argument is evaluated.

**Nothing in the surface is exempt.** A multi-argument operation and a syntax
macro both expand into curried application, so both evaluate right to left as
any other application does; there is no second rule for them
([Effects](03-Effects.md)).

### What "apply" resolves to

After `e2` and `e1` are evaluated to values, the value form of `e1` determines what happens.

| Value form of `e1` | Behaviour |
| --- | --- |
| `λ (x : τ) . e` | β-reduction: evaluate `e[x := v2]` |
| `M.Ctor [τ̄] v̄` with `\|v̄\| < arity` | append the argument, giving `M.Ctor [τ̄] (v̄, v2)`. **The result is again a value; no computation occurs** |
| an application of `foreign f` | call the implementation, a primitive step, which yields a value or a fault. That it reaches the **world** nowhere is a conformance obligation on the implementation and not a consequence of D23 alone; a world effect happens when the runtime executes the returned `IO`. An **observational** effect is a separate matter and the call may have one, unless the declaration asserts `#observ(none)` (D41) |

A saturated constructor application does not have a function type and so never appears in the position of `e1`.

**Consequence for backends.** A partially applied constructor may be passed around as a value, so a backend must be able to represent one. Whether it generates curried functions or a partial-application object carrying the arity and the collected arguments is the backend's choice; Mid IR retains constructor application in a form that lowers to either.

## Erasure: overview

A number of forms carry no run-time content and are removed before evaluation on a backend. The erasure function and its properties appear below, once every form it removes has been introduced.

## Recursive bindings

`letrec { x̄ = v̄ }` allocates an uninitialized location for each `x_i`, evaluates each `v_i`, and writes the result back. Guardedness (D14) makes each `v_i` a function value whose evaluation does not read any `x_j`, so an uninitialized reference cannot occur.

## Handlers and continuations

Handlers are deep. `perform k.op` transfers control to the **innermost** handler whose key is `k`. A `full` clause receives the argument together with the continuation up to that handler, and resuming it reinstalls the same handler; a `fast` clause receives the argument alone, and control returns to the point of the `perform` when its body produces a value (D28).

**Handlers of one key do nest at run time**, and the innermost wins. A function that handles `E` internally is pure to its caller, so calling it through `openEff [( E )]` from under an outer handler for `E` puts two on the stack at once. `Ev_k` is what picks between them: every `handle` on the path from the chosen one to the hole has some other key.

What sharpness gives is narrower and static: **no row holds one key twice**, so a `perform` names the element it means with a key alone, and needs nothing to say which occurrence. A design permitting duplicates within the row, as Koka's scoped labels do, must name an occurrence instead — which `E` of the several the row carries — and `mask` manipulates that offset. In Stella the notion of an offset does not arise, and that is the by-product of D4.

### How many times a continuation may be resumed

**Core imposes no limit** (D18). A continuation `k_i` is an ordinary function value, and its type `τ_i' -{ρ}-> β` says nothing about how often it is used. The reference semantics is therefore multi-shot.

The question belongs to `full` clauses, which are the ones that bind a continuation. A `fast` clause binds none and constructs none (D28), so implementing one asks no continuation of a backend. That is a statement about the clause: a program containing one is not thereby one-shot, since the clause's body may perform an operation of the residual row whose `full` handler resumes several times.

- calling it zero times abandons the computation, as an interpreter of `Partial` into `Maybe` does
- calling it once is ordinary resumption
- calling it more than once branches the computation: non-determinism, backtracking, probabilistic programming

Even a one-shot restriction would be **affine** — at most once — rather than linear, since abandonment is expressed by zero calls.

Restricting this in Core would require affine types for continuations. That would noticeably enlarge the trusted core in exchange for a static guarantee about one backend's convenience, so v0.1 does not include it.

### Implementation capability, and provisional non-conformance

The cost is backend-specific.

| Lowering | Arbitrary call depth | Multi-shot | Cost on JavaScript |
| --- | --- | --- | --- |
| exceptions with a locally reified continuation | no | yes | low |
| generators with `yield*` | yes | no | moderate |
| full CPS conversion | yes | yes | high |
| frames and a run loop of the backend's own, as the machine keeps | yes | yes | high, less where purity keeps a call on the host stack |
| Wasm stack switching | yes | no | low (native) |

Achieving both arbitrary call depth and multi-shot on JavaScript requires the backend to represent a continuation itself — by full CPS conversion, or by frames and a run loop of its own — and either costs the native stack and stack traces wherever it applies. Generators handle arbitrary depth via `yield*`, and a driver loop gives deep handler semantics directly, but JavaScript offers no way to clone a generator, so generators are strictly one-shot.

Each backend therefore declares what it can implement. This is **not a capability difference permitted by the language semantics**; it is provisional tolerance of non-conformance.

- **JavaScript backend**: an execution model that represents a continuation itself, one of the two multi-shot rows above ([JavaScript](../05-Backend/05-JavaScript.md)). Until it passes the cases that decide it — a `full` clause resuming twice, and a continuation carrying the cells of a region it was captured outside — it stands as one-shot here and in the gap below.
- **Wasm backend**: one-shot for now, following the stack-switching proposal.
- **Native backend**: nothing prevents multi-shot.

### The known soundness gap in v0.1

Stated precisely:

> **The v0.1 JavaScript and Wasm backends do not satisfy type soundness.** Since the reference semantics is multi-shot, a program that resumes a continuation more than once is well typed. On these backends such a program raises a run-time error.

v0.1 **accepts this as a known gap**, under three conditions.

1. **Failure is loud and specific.** A second resumption raises a dedicated run-time error, comparable to OCaml 5's `Continuation_already_resumed`. It must not be undefined behaviour and must not silently produce a wrong result.
2. **A static best-effort check is performed.** Only `full` clauses are in question, a `fast` clause having no continuation to resume. Detecting multiple resumption within a `full` clause is undecidable in general, since `k` can be stored and called in a loop, but the **syntactically evident** cases are detectable: a clause that mentions `k` more than once, or passes `k` to another function, warns at compile time. Most accidents are caught there, leaving the run-time check as a backstop. Writing a clause `fast` where its shape allows removes it from the question altogether.
3. **Closing the gap is a requirement for v1.0**, recorded in [Open Questions](../99-Open-Questions/01-Open-Questions.md).

The routes to closing it appear in the table above: an execution model representing a continuation on JavaScript, or a cloning primitive entering the Wasm stack-switching proposal. Making the reference semantics target-parameterized is a third possibility, but it would mean the same Core has different meanings on different backends, which conflicts with the backend independence of Mid IR.

### Consequence for Mid IR

Mid IR is designed in Phase A; effect lowering belongs to Phase E. Because of that order, **the representation of continuations in Mid IR must not assume one-shot**. This is a constraint to observe already in Phase A, and it is why Mid IR is specified to carry handler and continuation operations.

A `fast` clause needs no such representation, so Mid IR must also keep the two clause forms apart, allowing a backend to lower one as an ordinary call and reserving the cost of a continuation for the other.

## Reduction

The table above fixes the order in which subterms are evaluated. This section gives the reduction relation itself.

Two relations are distinguished.

| Relation | On | Preserves types |
| --- | --- | --- |
| `G ⊢ e → c` | Core terms, to a configuration | yes, whenever c is a term |
| `⌊e⌋ →ᵤ …` | erased terms | not applicable; types are gone |

A configuration is either a term or a fault.

```text
c ::= e  |  fault φ
```

Preservation constrains only the case in which `c` is a term; a fault has no type to preserve.

Keeping them apart matters because the coercion forms that erasure removes — `openEff`, `weaken`, `[[κ̄]]` — **change a term's type**. Removing them is not a step of typed reduction.

### The global environment

Reduction is parameterized by a global environment, obtained by linking a module with those it depends on.

The signature `Σ` is fixed throughout and left implicit, as it is in the typing rules: `cursorΣ` and the rules below consult it whenever a declared type is wanted. `G` is what linking produces, and availability is decided there.

```text
G ::= ·
    | G, M.x : σκ = v          a top-level value definition
    | G, M.f : σκ = δ_f        a foreign, with its implementation
    | G, M.Ctor                a data constructor
```

A global name reduces by looking itself up, which is also where a kind scheme is instantiated.

```text
  (M.x : forall k̄. σ = v) ∈ G
  ──────────────────────────────
  G ⊢ M.x [[κ̄]] → v[k̄ := κ̄]
```

This preserves the type: `M.x [[κ̄]] : σ[k̄ := κ̄]`, and `v` has type `σ` under `k̄`.

A constructor spine is already a value, saturated or not, so it needs no unfolding rule of its own; the spine formation rule below turns the atomic reference into one.

### Module initialization

`G` holds values, whereas a `nonrec` declaration admits any pure expression. The two are connected by **evaluating right-hand sides at link time**.

The order mirrors the three stages of declaration checking ([Modules](../06-Modules/01-Modules.md)). Type checking collects every constructor, operation, and `foreign` into `Σ_decl` before checking any value declaration, so a `nonrec` may legitimately refer to a `foreign` or a constructor that appears later in the text. Initialization must therefore populate those first, or such a module would stall.

```text
  G_Prim = the data constructors of Prim, which is Prim.Unit alone

  G_decl = G_Prim
         ∪ the definitions of the imported modules
         ∪ every constructor declared by M
         ∪ every foreign implementation δ_f declared by M

  then, folding only the value binding groups in declaration order:

    nonrec x : σκ = e     G_i ⊢ e →* c           (at ambient row ())
                          if c = v:        G_{i+1} = G_i, M.x : σκ = v
                          if c = fault φ:  initialization fails with φ

    rec { x̄ : σ̄ = v̄ }     G_{i+1} = G_i, M.x_1 : σκ_1 = v_1, …, M.x_n : σκ_n = v_n
```

`G_Prim` mirrors `Σ_Prim` on the value side ([Prim and Base](../06-Modules/02-Prim-and-Base.md)). `Prim` is not imported, so without it a `Prim.Unit` occurring in the module would have nothing to unfold to, and condition (1) of `Σ ⊨ G` would fail. The implementations the runtime ABI is obliged to supply arrive with the imports, since the module that declares them is imported like any other.

A `rec` group installs **every entry at once, with the right-hand sides themselves**. Guardedness makes each `v_i` a value already, so nothing is evaluated, and a recursive reference inside `v_i` is `M.x_j [[κ̄]]`, an ordinary global name resolved by the lookup rule. No local recursive closure is involved, and each `v_i` keeps the kind binder `k̄_i` under which it was checked.

The fold over value declarations is well defined because they are in dependency order and cycles are confined to `rec` groups.

Evaluating eagerly rather than on first reference is the choice consistent with strict evaluation, and it is observable: **a top-level declaration whose right-hand side diverges hangs initialization even if nothing refers to it.** Lazy global lookup would leave such a declaration harmless. Stella takes the strict reading.

### Faults

A pure primitive may fail. Indexing an array out of bounds is the standard example, and no type in Stella describes it.

A failure of this kind is **not an effect**. It is not intercepted by `handle`, it does not appear in an effect row, and it is not the `Partial` effect, which is an ordinary handleable effect for non-exhaustive matches (D10). It is a fault, in the same category as exhausting the stack.

Reduction therefore relates a term to a configuration, `G ⊢ e → c`, where `c` is a term or a fault. The rule propagating a fault out of an evaluation context appears with the contexts below.

**Which entries may fault, and on which inputs, belongs to the `Base` ABI specification** ([Open Questions](../99-Open-Questions/01-Open-Questions.md)) rather than to Core. Core only records that a fault is a possible outcome of applying a `foreign`.

### Conformance of the global environment

A `foreign` declaration's type is trusted ([Modules](../06-Modules/01-Modules.md)), and D23 constrains only the **arrows appearing in that type**. It says nothing about whether the implementation returns what it claims, performs effects behind Core's back, or terminates. Those are obligations on the implementation, and the properties below depend on them, so they are stated rather than assumed.

#### The three classes of effect

An effect in Stella belongs to one of three classes, and the conditions below are written against the classification rather than against one word.

```text
proper
  row-tracked. Declared with `effect`, reached by `perform`, and dealt with
  by a handler. This is the class the word ordinarily names

reified
  a computation a classical monad has made into a value: `IO`, and a State
  or an ExceptT a library defines. A saturated application constructs one
  and does not run it; what runs an IO is the drive loop (D25)

observational
  whatever a foreign's saturated application may do besides returning its
  value. It appears in no type, and no handler deals with one
```

**The three are not exclusive.** One foreign may carry a reified effect and an observational one at once: an entry returning `IO` that also writes to memory when it is applied has both, and the two are settled separately.

The third class is what a mutable array behind a pure interface is: `Base.Array.unsafeSet` writes, its declared type says `Unit`, and no row carries anything. Declaring such an entry effectful in its type is not available — it would return `IO`, and the pure `mapArray` written over it could not then exist ([Modules](../06-Modules/01-Modules.md)).

**What makes an effect observational is that something other than the returned value may be noticed.**

> A saturated foreign invocation **has an observational effect** when anything besides the value it returns may make erasing, duplicating, sharing, or reordering that invocation observable.

**Producing a fault is one such observation and is not a class of its own.** Dropping a call that would have faulted removes the fault, and reordering two of them changes which one is taken, so faulting is exactly the thing the definition names. Nothing is gained by grading observational behaviour more finely than this: the reason Stella reaches for FFI sparingly (D19) is that what lies past the boundary cannot be characterized, and a summary that pretended otherwise would be a summary of what an implementation happens to do today.

**`#observ(none)` asserts the absence of the class, and the assertion is strong.** A saturated application of an entry carrying it reads and writes no hidden state, produces no fault, creates no identity anything can observe, performs no external effect at the point of application, and returns observationally equivalent results for observationally equivalent arguments. It terminates, applies no Stella function value, and throws nothing, which the conditions below ask of every entry in any case.

**There are two rules and no third.** A declaration carries the annotation, and the entry has no observational effect; or it does not, and the entry may have any. Nothing is inferred from the type, from the name, or from who supplies the implementation.

**What the annotation says nothing about is the reified class.** `#observ(none)` and returning `IO` are independent and compose: `#observ(none) foreign log : String -> IO Unit` performs nothing when it is applied and merely constructs an action, and the output happens where the drive loop runs that action. Whether an entry returns `IO` is read off the result type and is stated nowhere ([Interface](../05-Backend/03-Interface.md)).

```text
Σ ⊨ G   holds when

  (1) G covers every global name mentioned by the module under evaluation,
      and by the definitions in G itself

  (2) for each (M.x : forall k̄. σ = v) ∈ G,  under Σ:
        ·, k̄ ; · ; · ⊢ v : σ ! ()
      that is, a global definition is a well-typed value with no effects

  (3) for each (M.f : σκ = δ_f) ∈ G, and for every spine ς that is saturated
      for M.f with cursorΣ(M.f, ς) = ⟨ σ ; θ ⟩  (see The spine cursor below),
      writing v̄ = values(ς), and **where the ABI preconditions of M.f hold**:
        δ_f(v̄) is defined
        δ_f(v̄) is either a value of type θ(σ) or a fault
        δ_f(v̄) performs no proper effect, and runs no reified computation
               it constructs
        δ_f(v̄) applies no Stella function value
        δ_f(v̄) terminates
        δ_f(v̄) has no observational effect, and so returns a value
               rather than a fault,
               where Σ records #observ(none) for M.f
```

#### An ABI precondition is where condition (3) stops asking

**An entry may be specified with a precondition, and where one is violated the ABI fixes nothing.** Condition (3) is quantified over the calls that respect it, which is what the clause added to it says, and the effect of that is narrow and deliberate: for a violating call an implementation owes no value of the result type, owes no fault, and owes nothing in common with another implementation.

**One entry of `stella-base-0.1` has such a precondition, and it covers one case of that entry.** `Base.Array.unsafeIndex` faults on an index outside the array, as every backend must; the precondition is reached only after the index is found to be in range, and it is that the slot has been written. A slot `Base.Array.unsafeNew` left unwritten is one the ABI does not say how to read ([Prim and Base](../06-Modules/02-Prim-and-Base.md)). Requiring a fault there instead would oblige every backend to carry an initialization bit and to check it on every read, and that check would stand on the hot path of the one operation a portable array library is built out of — which is why it is not required. It is not forbidden either: a backend that pays for the check is conformant, and a program violating the precondition then runs there and nowhere else. The cost of the precondition is this paragraph and the premise below; the cost of removing it is paid by every array read in every program.

**A precondition is not an observational effect, and confusing the two loses both.**

| | What it asks | What it is read by |
| --- | --- | --- |
| `#observ(none)` | may a call be dropped, duplicated, or moved | an optimizer |
| **an ABI precondition** | does this call, on these arguments and in this state, have a specified meaning at all | whoever writes the call |

`Base.Array.unsafeSet` carries no precondition at all — an index outside the array faults — and it is observational all the same, because it writes; and `unsafeIndex` on an unwritten slot is a precondition violation whether or not anything would have optimized it. Neither answers the other's question.

**Discharging a precondition belongs to the program and to nothing that checks it.** No type records one, no analysis here decides one, and a machine is neither obliged to detect a violation nor forbidden from doing so; what discharges it is the library standing over the entry. `Data.Array` writes every slot of an array before it returns one, and an application reaching `unsafeIndex` through that library never reaches an unwritten slot. **A program that violates one is outside the guarantees below, type safety included**, which is the whole of what `unsafe` names in these entries.

**`Σ ⊨ G` is what every implementation owes, and it is not what this relation needs.** A second condition sits beside it, and the two are kept apart because they bind different parties: conformance is owed by whoever supplies a `δ_f`, while the one below says which environments the rules below describe at all.

```text
G is Core-modelled   when for each (M.f : σκ = δ_f) ∈ G, and for every spine ς
                     that is saturated for M.f, writing v̄ = values(ς):
                       returning an outcome — a value or a fault — is the whole
                              of what δ_f(v̄) does
                       v̄ determines that outcome, and nothing else
                              contributes to it
                       δ_f(v̄) reads no state that v̄ does not carry
                       δ_f(v̄) writes no state
                       δ_f(v̄) creates no identity that v̄ does not determine,
                              a freshly allocated one among them, observed or not
```

**Determining the outcome is not enough, and the clauses after the first are not decoration.** An entry writing through an array it is handed returns `Unit` whatever it wrote, so the arguments determine its outcome perfectly and it is still not what the rule below reads `δ_f` as. What disqualifies it is the write, which the rule names nowhere. The condition is therefore about the whole of a call and not about its result: an outcome the arguments fix, and nothing else happening.

**Neither of the two conditions implies the other, and an earlier draft of this section claimed that one did.** They disagree in both directions, and the disagreement is not a technicality.

**They forbid different identities.** `#observ(none)` forbids creating an identity **anything can observe**, and this condition forbids creating one **the arguments do not determine**, observed or not — the rule below equates a saturated call with `δ_f(v̄)`, so two calls on equal arguments must give the same term, and a fresh `ω` on each is two terms. An entry handing back an allocation no Stella program can tell from another therefore satisfies the directive and fails this condition.

**And this condition permits a fault, which the directive does not.** `Base.String.codePointAt` is the standing case above.

**What each is for is what keeps them apart.** The directive says a call may be moved, dropped, or shared, which is a statement about optimization. Being Core-modelled says the syntactic relation below represents the implementation uniquely, which is a statement about this document. Most ordinary entries satisfy both; **neither follows from the other**, and both are stated where they are needed ([Design Decisions](../01-Introduction/03-Design-Decisions.md), D41).

**An entry may conform without being Core-modelled**, and `Base.Array.unsafeSet` is the case: it satisfies `Σ ⊨ G` — it returns what it claims, runs no reified computation, applies no Stella function, terminates, and asserts no `#observ(none)` it would be breaching — while it writes to a store the reduction relation records nowhere. Such an entry is admissible, and a machine runs it; what it is not is described by the reduction relation (D41).

**Faulting does not cost an entry its place here.** A `δ_f` that faults on exactly the arguments it always faults on is a function like any other, so `Base.String.codePointAt` is Core-modelled and the fault branch of progress is reached by it. What the condition excludes is a hidden read, a write, and an identity the arguments do not determine, observable or not — and nothing else.

**The third condition is on the term rather than on the environment**, and it is what the precondition above costs.

```text
e respects preconditions under G
                     when no saturated foreign invocation reached from e by
                     the relation below violates the ABI precondition of the
                     entry it invokes
```

**This one is not decided anywhere, and saying so is part of stating it.** Whether a program ever reads an unwritten slot is not settled by its type, by any analysis in these documents, or by anything a machine does at run time. What discharges it is the library that owns the unsafe entry, and what a violation costs is everything below: a term that violates one has no guarantee of preservation, of progress, or of anything else this section states.

**The three conditions fail in three different ways**, which is why none of them absorbs another.

| | Who it binds | What its failure does |
| --- | --- | --- |
| `Σ ⊨ G` | whoever supplies a `δ_f` | an implementation is in breach; the environment is not one any backend may offer |
| Core-modelled | nothing, being a property of `G` | the rule below gives a saturated `foreign` no step, so the term is unmodelled rather than wrong |
| preconditions respected | the program, and the library standing over the entry | the step is taken and what it yields is unspecified, so the properties below say nothing about what follows |

Condition (2) applies to the entries a `rec` group installs as well. Each `v_i` is checked under its own `k̄_i` and refers to its neighbours through `Σ`, which the declaration rules populated before any value declaration was checked.

Condition (3) is stated through the cursor because the result type of a polymorphic foreign depends on the instantiation the spine carries. Applying `forall a. a -> a` at `[Int]` obliges `δ_f` to return an `Int`, and the raw declared type does not say so.

**A `δ_f` may carry a function value but may not apply one.** That restriction is what lets the requirements above hold together. The rule for a saturated `foreign` is one atomic step to a value or a fault, so a `δ_f` applying a Stella function would step to neither where that application diverges — Core claims nowhere that a function terminates — and progress would fail for a term that is not stuck but running. **Where the function came from makes no difference**, so the condition names none: an argument, a field of a record or of a constructor among the arguments, a closure retained from an earlier call, or one reached through a global are one case, as D23 treats every runtime-bearing position of a declared type alike. Carrying one is untouched by this: `Base.IO.bind` takes `a -> IO b` and stores it in the `IO` value it builds, and what applies it is the runtime executing that value, which is outside this reduction relation (D25).

An entry that applies a function it is given — a pure `map` over an array, say — therefore needs more of the model than this: a configuration for a foreign in progress, or a second judgement to carry the applications. Neither is here, so no such entry is admitted ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

Condition (3) is what makes a `foreign` returning `IO` inert until the runtime executes it. **That property does not follow from D23.** D23 makes the declared type honest about where effects may appear; conformance of `δ_f` is what makes the implementation match the declaration. A backend is responsible for both.

Admitting a fault in (3) is what keeps the condition consistent with progress: a saturated `foreign` always either produces a value or produces a fault, and never leaves a term stuck.

#### An observational effect is outside what this relation models

An entry with observational effects reads and writes memory, and **the relation above names none of it**. The gap is not a matter of emphasis, and it is worth stating exactly where it falls.

**The state is not in the term.** A mutable array is an `opaque ω [τ]`, and a `writeCell`-like write performed inside `δ_f` leaves that `ω` as it was: the term after the write is the term before it. So `Base.Array.unsafeSet` writes state the configuration does not record, and `Base.Array.unsafeIndex` **reads** it — the `ω` it is handed names an array whose current contents are nowhere in `v̄`, so the same arguments give different values according to which writes preceded them. Neither is the function of `v̄` that the rule below reads `δ_f` as. **Any argument that the state "is really in the payload" is wrong**, and an earlier draft of this section made it.

**What follows is that the step is not defined, and not merely that it is not deterministic.** The rule is `M.f ς → δ_f(values(ς))`, which reads `δ_f` as a function of `values(ς)`. For an entry that reads hidden state it is not one, so **that rule gives such an entry no step at all**: there is nothing here to be non-deterministic, because there is nothing here.

**Being Core-modelled is the line, and it is not the line `#observ(none)` draws.** It is a condition of its own beside `Σ ⊨ G` and not a clause within it, because the two bind different parties: conformance is what an implementer owes and admits `unsafeSet`, while being Core-modelled is what these rules need and does not. The relation is defined against a `G` that is both, and every property below carries both as premises.

**Three notions come apart here and keeping them apart is what makes the boundary usable.**

| | What it is | Who reads it |
| --- | --- | --- |
| `#observ(none)` | a declared guarantee: no hidden read or write, no fault, no observable identity | an optimizer, and a conformance test |
| `MayObserve` | how an entry carrying no directive is **treated** | an optimizer |
| **Core-modelled** | returning an outcome the arguments fix, a value or a fault, is the whole of what a call does | this relation, as a premise beside `Σ ⊨ G` |

**An entry may be Core-modelled without carrying the annotation.** `Base.String.codePointAt` faults outside its range, so it is `MayObserve` — dropping a call of it drops the fault — and its outcome is nonetheless determined by the index and the string, which is an immutable one, so it is Core-modelled and this relation handles it. **Faulting is what puts an entry in the second row and not in the third.** What falls outside is the entry whose behaviour is not exhausted by an outcome its arguments fix: `Base.Array.unsafeNew`, which creates an identity nothing in `v̄` determines; `Base.Array.unsafeSet`, which writes; and `Base.Array.unsafeIndex`, which reads what those writes left. The third is the one most easily overlooked, because its fault is the conspicuous thing about it and the read is not.

**This is about what can be guaranteed and not about what an implementation does.** `MayObserve` is a treatment and asserts nothing of the implementation behind it: one that happens to read and write nothing makes its program deterministic in fact, and nothing here contradicts that. What an absent directive removes is the ground for saying so, which is the whole purpose of a conservative default.

**The price is plain and is worth stating rather than absorbing.** `Prelude`'s `mapArray` is written over `unsafeNew`, `unsafeSet`, and `unsafeIndex`, so **a program that maps over an array is outside what the properties below cover.** That is not a corner of the design; it is what makes settling the model below the next thing worth settling, rather than something to leave indefinitely.

**Two ways are open and one has to be taken** ([Open Questions](../99-Open-Questions/01-Open-Questions.md)). A configuration may be given an observational store, with `δ_f` a transition over it, which defines the step and recovers every program at the price of putting state into the trusted core — the thing D25 exists to avoid. Or the relation may stay as it is and an entry that is not Core-modelled be a **trusted boundary**, described by conformance. **This document takes the second as a provisional position and not as the answer**: it is what lets the rest be written, and what it costs is written above rather than left to be discovered.

**This is the ordinary case and not an exotic one**, which is why a style guide does not settle it. `Prelude`'s `mapArray` is written over `unsafeNew`, `unsafeSet`, and `unsafeIndex`, so a program that maps over an array reaches an observational entry whether or not its author has heard of one.

### Values

```text
v ::= c
    | λ (x : τ) . e
    | Λ (a : κ) . v
    | Λ (_ : C) . v
    | M.Ctor ς                 a constructor spine
    | M.f ς                    a foreign spine that is not saturated
    | rec_i(x̄ : σ̄. v̄)         a component of a local recursive group
    | {} | extend k v1 v2
    | inject k v
    | weaken k [τ] v          a value of a wider variant
    | openEff [ρ] v           a function value at a wider effect row
    | opaque ω [τ]            a value of an intrinsic type, produced by a foreign

ς ::= ·  |  ς, [[κ̄]]  |  ς, [τ]  |  ς, [•]  |  ς, v      an argument spine
```

### Opaque values

A `foreign` returns a value of its instantiated result type, and what shape that value has follows from the type.

| Result type | The value `δ_f` returns |
| --- | --- |
| a data type | a constructor spine |
| an intrinsic type | the canonical form of `Σ(T)`'s class ([Prim and Base](../06-Modules/02-Prim-and-Base.md)) |

The second row covers more than one case. A `foreign` whose result is `Int` returns a literal, one whose result is a function type returns a function value — `foreign make : forall a. a` instantiated at `Int -> Int` does exactly that, below — and one whose result is a `Record` returns `{}` or an `extend`. Only the `intrinsic opaque` class is left without a form of its own.

`opaque ω [τ]` is what `δ_f` returns there. `ω` is the payload the backend holds — a JavaScript thunk, a Wasm reference, a native handle — and Core knows only that it is there.

```text
  τ = T τ̄     Σ(T) = intrinsic opaque     Γ ⊢ τ : Type
  ────────────────────────────────────────────────────
  Γ;Δ ⊢ opaque ω [τ] : τ ! ρ
```

The premise names the **canonical-value class** `Σ` records of `T` ([Prim and Base](../06-Modules/02-Prim-and-Base.md)), not merely that `T` is intrinsic. Admitting any intrinsic type here would admit `opaque ω [Boolean]`, and a `guard` would then meet a value that is neither `true` nor `false`; the same argument applies to `Record` against `select` and to `Function` against application. Progress holds class by class, and this is the premise that keeps it so.

**The payload is what distinguishes one opaque value from another.** Two `IO Unit` values obtained from different foreign applications are different values, and a form carrying only `τ` could not say so.

This is a run-time form: elaboration never produces one, and **no rule takes one apart or compares two**. Core carries an opaque value from the `foreign` that produced it to the `foreign` that consumes it, and observes nothing in between — which is what keeps `IO` representation-independent.

`IO` is the case that matters for D25. Reduction halts once it has constructed a value of type `IO`, and `opaque ω [IO Unit]` is what it halts on; executing that value is the runtime ABI's obligation, not a step of this relation.

Erasure keeps the payload, which carries the run-time content, and drops the type.

```text
⌊opaque ω [τ]⌋ = opaque ω
```

A global constructor or foreign accumulates its arguments on a **single ordered spine**. Each entry is a kind, type, or constraint instantiation, or a value, and the order is whatever the declared type calls for; nothing requires the erased entries to precede the values. `values(ς)` is the subsequence of value arguments, which is what erasure keeps and what `δ_f` receives.

Without a spine, a polymorphic `foreign` could not be used at all: `Base.IO.pure : forall a. a -> IO a` requires `Base.IO.pure [Int]`, and the rule for type application applies only to a `Λ`.

A **constructor spine is always a value**, saturated or not: a saturated one is a completed structure, an unsaturated one behaves as a function. A **foreign spine is a value only while it is unsaturated**; once saturated it is a redex that invokes `δ_f`.

`weaken` and `openEff` are **value forms, not redexes**. Reducing them away would change the type — `weaken k [τ] v : Variant ( k : τ | r )` while `v : Variant r` — and D8 provides no subtyping to identify the two. They are consumed by the constructs that examine them: pattern matching looks through `weaken`, and application looks through `openEff`.

### Run-time forms

Seven forms arise during reduction and are never produced by elaboration.

```text
match θ dt            descending a decision tree
openEffC [ρ] e        a computation whose effects are bounded by a wider row
rec_i(x̄ : σ̄. v̄)       the i-th component of a local recursive binding group
opaque ω [τ]          a value an implementation returned, typed above
region [r] θ in e     an open region of cells, θ a finite map from key to value
handleO e with h      the handler a region was opened for
handleI e with h      the same handler reinstalled by a resumption
```

The last is the only one a `δ_f` produces, and the only one that is a value rather than a step in progress; its rule is given with the values.

```text
  Γ;Δ ⊢ e : τ ! r    Γ ⊨ r # ρ
  ────────────────────────────────
  Γ;Δ ⊢ openEffC [ρ] e : τ ! (r ⊎ ρ)

  Γ' = Γ, x̄ : σ̄     each i: v_i is a FunVal (D14) and Γ'; Δ ⊢ v_i : σ_i ! ()
  ──────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ rec_i(x̄ : σ̄. v̄) : σ_i ! ρ

  nf(ι) = ⟨ G ; ∅ ⟩    dom(θ) = dom(G)    each k ∈ dom(θ) :  Γ;Δ ⊢ θ(k) : G(k) ! ()
  Γ, r : Type; Δ ⊢ e : τ ! ( region r ι | ρ )      Γ ⊨ RegionKey ∉ ρ
  r ∉ ftv(τ) ∪ ftv(ρ)
  ─────────────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ region [r] θ in e : τ ! ρ

  h = { handles ent ; cells [r] ( k̄ : σ̄ ) ; return (x : α) -> e_r ; cl_i }
  r ∈ Γ                                             ← an occurrence, not a binder
  ι = ( k̄ : σ̄ )      ρ' = ( region r ι | ρ )
  Γ ⊢ ( ent | ρ ) : Row Effect      Γ;· ⊢ e : α ! ( ent | ρ )      payload(ent) = E τ̄
  Γ ⊨ RegionKey ∉ ρ        Γ ⊢ ι : Row Type        the k̄ are distinct
  Γ, x : α; · ⊢ e_r : β ! ρ
  each i: the clause premises of the source rule, at ρ', under Γ
  { op_i } = dom(Σ(E))    and the op_i are distinct
  r ∉ ftv(β) ∪ ftv(ρ)
  ─────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ handleO e with h : β ! ρ'
  Γ;Δ ⊢ handleI e with h : β ! ρ'
```

**`cells [r] ι` binds `r` in a source handler and refers to it in a run-time one.** The two forms above are reached only under an enclosing `region [r] θ in [ ]`, whose rule checks its body under `Γ, r : Type`; the `[r]` each carries is the occurrence that binding resolves. **The opening step is where the binder moves**, from the handler to the region the same step wraps around it, and it is the only step of the relation that moves one.

**The move is capture-avoiding, and the rule says so rather than leaving it to be argued.** A handler's `cells` binder scopes over its operation clauses alone, while the region the step creates scopes over the initial values and the handled computation besides. That the name is free nowhere in the context is settled already: the typing rule requires `r ∉ dom(Γ)` ([Typing Rules](05-Typing-Rules.md)). What it does not settle is a binder of that name standing **within** the handled computation or an initial value, which the source term is free to have, those binders sharing no scope with `cells`. Widening the region over them would bring two binders of one name into one scope, and Core terms are unique up to α-equivalence — a convention substitution relies on, passing under a binder without renaming it. The step therefore renames to a globally fresh `r'`, which is why the rule writes `h[r := r']` rather than `h`. Nothing else in the relation moves a binder, so this is the only place the question arises.

**`h[r := r']` is binder-aware.** What it renames is the `[r]` token of `cells` and the occurrences of `r` within that binder's scope, which is **every operation clause entire — its type annotations as well as its body**. A `full` clause writes its continuation's type `τ_i' -{ρ'}-> β`, and `ρ'` is `( region r ι | ρ )`, so renaming bodies alone would leave the old `r` standing in an annotation and the installed handler ill-scoped. What lies outside the scope is `handles ent`, the layout, and the return clause, and the renaming leaves all three alone. No `r` stands free there to begin with, the binder being fresh for `Γ`; one **bound** within the return clause's body is a different variable, and the fresh `r'` is what keeps it so.

Well-scopedness of the run-time forms is then a property of the region, not of the handler. A `handleO` or `handleI` mentioning `r` stands within the `region [r]` that binds it; what carries one elsewhere carries the region with it.

`openEffC [ρ] e` widens the **ambient row of a computation**, where `openEff` widens the **effect row inside a function's type**. Both are needed and neither subsumes the other: `openEff` is what allows a pure function to be passed where a wider arrow type is expected, and `openEffC` is what allows the result of applying such a function to sit in a context whose ambient row is the wider one.

`rec_i` carries the type annotations of the group it came from, which is what makes its typing rule derivable and hence what makes preservation hold for `letrec`. It is a **local** form only. A top-level `rec` group installs its right-hand sides into `G` directly, and its recursive references are global names.

`region [r] θ in e` is a region whose initial values have been evaluated. It carries `θ` — **the cells themselves, by value** — together with the region variable and the conditions the source rule imposed, which is what makes its rule derivable and hence what makes preservation hold across a write (D36). The values live here and nowhere else: there is no store, no address, and no two ways to reach one cell.

`handleO` and `handleI` are the same handler installed, and the two are kept apart because **a region has one owner and any number of reinstatements**. `handleO` is what the opening step puts inside the region; `handleI` is what a resumption rebuilds, standing wherever the clause that holds the continuation applied it, which is inside the owner's region and not adjacent to it. Both are typed at `ρ'`, both standing within the region. They differ in one rule alone, the one for a value, and that difference is the whole reason for the marker: **an owner finishing ends the region, a reinstatement finishing does not.**

The return clause is typed at `ρ` and so is not usable at `ρ'` without widening; where it runs inside the region, the rule wraps it in `openEffC`.

### The spine cursor

Reduction carries no `Γ`, so saturation must be decidable from the declaration and the spine alone. `cursorΣ` is a partial function that walks the **declared** type, consuming one spine entry at a time. It performs no well-formedness checking.

```text
cursorΣ(M.g, ς)  =  ⟨ σ ; θ ⟩       σ is the unconsumed remainder of the declared type
                                     θ is the accumulated kind and type substitution
```

```text
cursorΣ(M.g, ·)            = ⟨ σκ ; id ⟩              where ( M.g : σκ ) ∈ Σ
cursorΣ(M.g, (ς, [[κ̄]]))   = ⟨ σ ; θ[k̄ := κ̄] ⟩        where cursorΣ(M.g, ς) = ⟨ forall k̄. σ ; θ ⟩
cursorΣ(M.g, (ς, [τ]))     = ⟨ σ ; θ[a := τ] ⟩        where cursorΣ(M.g, ς) = ⟨ forall (a : κ). σ ; θ ⟩
cursorΣ(M.g, (ς, [•]))     = ⟨ σ ; θ ⟩                where cursorΣ(M.g, ς) = ⟨ C => σ ; θ ⟩
cursorΣ(M.g, (ς, w))       = ⟨ τ2 ; θ ⟩               where cursorΣ(M.g, ς) = ⟨ τ1 -{()}-> τ2 ; θ ⟩
```

It is undefined in every other case. At most one clause applies at each step, since the shape of the unconsumed declared type distinguishes them.

Nothing constrains the order of entries: a declared type may interleave quantifiers, constraints, and arrows freely, and the cursor follows it. A type such as `Int -> forall a. a -> a` is therefore usable, with `[String]` supplied after the first value argument.

The arrow consumed by the last clause is pure. A constructor's arrows are pure by declaration, and a `foreign`'s are pure by D23.

A kind instantiation `[[κ̄]]` consumes the whole vector at once and can occur at most once, since kind schemes are prenex (D3).

#### Saturation is a position in the declared type

**A spine is saturated** when `cursorΣ(M.g, ς) = ⟨ σ ; θ ⟩` and the **unconsumed declared type `σ`** is not a `forall`, a constraint arrow, or a function type.

The test is on `σ`, not on `θ(σ)`. Substitution can introduce arrows that the declaration never called for, and treating those as argument positions would absorb arguments that do not belong to the foreign.

```text
foreign id : forall a. a -> a

M.id ·                       ⟨ forall a. a -> a ; id ⟩         expects a type
M.id ([Int -> Int])          ⟨ a -> a ; [a := Int -> Int] ⟩     expects one value
M.id ([Int -> Int], f)       ⟨ a ; [a := Int -> Int] ⟩          saturated
```

The last line is saturated because the declared remainder is the variable `a`, even though `θ(a) = Int -> Int` is a function type. So `δ_id(f)` runs and returns `f`, and the application `(M.id ([Int -> Int], f)) 0` proceeds as an ordinary application of the returned function. Testing `θ(σ)` instead would have absorbed `0` into the spine and called `δ_id(f, 0)`.

`foreign make : forall a. a` instantiated at a function type behaves the same way: `M.make ([Int -> Int])` is saturated at once, and whatever function `δ_make()` returns is applied normally.

**Arity is a static property of the declaration.** The number of value-argument positions is the number of arrows on the declared type's spine, which is what the cursor walks and what substitution never changes. Erasure therefore preserves it: after type arguments are gone, a backend still calls `δ_f` with exactly that many run-time arguments.

### Typing a spine

Typing a spine is the cursor together with the well-formedness of each entry.

```text
  cursorΣ(M.g, ς) = ⟨ σ ; θ ⟩       every entry of ς is well formed, as below
  ────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ M.g ς : θ(σ) ! ρ
```

An entry is well formed when, writing `⟨ σ' ; θ' ⟩` for the cursor **before** it is consumed:

| Entry | Condition |
| --- | --- |
| `[[κ̄]]` | `Γ ⊢ κ̄ qkind` and `\|κ̄\| = \|k̄\|` |
| `[τ]` | `Γ ⊢ τ : θ'(κ)`, where `σ' = forall (a : κ). …` |
| `[•]` | `Γ ⊨ θ'(C)`, where `σ' = C => …` |
| `w` | `Γ;Δ ⊢ w : θ'(τ1) ! ρ`, where `σ' = τ1 -{()}-> τ2` |

Separating the two is what lets reduction proceed without a `Γ`. **Saturation and the reduction rules consult `cursorΣ` alone**; the conditions in the table are discharged once, when the term is type checked. In particular the entailment `Γ ⊨ θ'(C)` for a `[•]` entry is a type-checking obligation and is never re-examined at run time, consistently with constraints carrying no run-time content.

### Forming and reducing a spine

The atomic global reference forms the initial spine. A defined global unfolds to a value instead; a constructor and a foreign have nothing to unfold to.

```text
  ( M.Ctor ) ∈ G  with  ( M.Ctor : σκ ) ∈ Σ
  or  ( M.f : σκ = δ_f ) ∈ G
  ─────────────────────────────────────────────
  G ⊢ M.g [[κ̄]] → M.g ([[κ̄]])
```

Where the kind scheme is empty, `[[κ̄]]` is elided on both sides and the rule reads `M.g → M.g ·`.

An unsaturated spine absorbs the argument its cursor calls for; a saturated foreign invokes its implementation.

```text
α ::= [τ]  |  [•]  |  v            a spine argument after formation
```

```text
  (M.g ς) α                →  M.g (ς, α)           when ς is not saturated for M.g
                                                    and cursorΣ(M.g, (ς, α)) is defined

  M.f ς                    →  δ_f( values(ς) )     when ς is saturated for M.f,
                                                    G is Core-modelled, and the
                                                    ABI preconditions of M.f hold
```

**The premises on the second rule are not decoration, and the two say different things.** `δ_f( values(ς) )` names the outcome the arguments determine, so the rule says nothing where they determine nothing (above): an implementation reading hidden state is one this rule gives no step to, and that is the whole of what "outside the relation" means. The precondition premise is narrower and fails at one call rather than for a whole environment — a `Base.Array.unsafeIndex` reading a slot nothing wrote has a step taken in any real machine and no step here, because what that step yields is what the ABI declined to fix. Both are written on this rule because this is the one rule where either bites; every rule is read against such a `G` and such a term.

`[[κ̄]]` is absent from `α` because the whole kind vector is consumed at formation and a kind scheme is prenex, so no second kind instantiation can arise.

The two rules do not overlap. A saturated foreign spine reduces to `δ_f` **before** it can be applied to anything further, so a result that happens to be a function is applied by the ordinary rule for application rather than being absorbed.

The second rule is also what makes an arity-zero `foreign` work. A declaration such as `foreign clock : IO Time` forms a spine that is saturated immediately, so it steps to `δ_clock()` rather than sitting as a value that is neither reducible nor complete.

A saturated **constructor** spine is a value and does not reduce; a saturated **foreign** spine is a redex. The difference is that a constructor has an implementation nowhere but in its own structure. A constructor's declared result is `T ā`, never an arrow, so the question of absorbing further arguments does not arise for it.

Erasure discards the erased entries and keeps the values.

```text
⌊M.g ς⌋ = M.g ⌊values(ς)⌋
```

### Evaluation contexts

An evaluation context marks the single position at which reduction may occur. Its shape encodes the order tabulated above.

```text
Ev ::= []
     | e Ev  |  Ev v                        argument before function (D35)
     | Ev [τ]  |  Ev [•]
     | openEff [ρ] Ev  |  openEffC [ρ] Ev
     | extend k Ev e  |  extend k v Ev
     | update k Ev e  |  update k v Ev
     | merge Ev e  |  merge v Ev
     | select k Ev  |  restrict k Ev
     | inject k Ev  |  weaken k [τ] Ev  |  absurd [τ] Ev
     | let x : τ = Ev in e
     | case (v̄, Ev, ē) of dt
     | match θ (guard Ev dt1 dt2)
     | letjoin j (x̄ : τ̄) : τ = e1 in Ev
     | jump j (v̄, Ev, ē)
     | perform k.op [τ̄] Ev
     | handle e with h @ ( v̄, Ev, ē )
     | handle Ev with h  |  handleO Ev with h  |  handleI Ev with h
     | writeCell k Ev
     | region [r] θ in Ev
```

```text
  G ⊢ e → e'                        G ⊢ e → fault φ     Ev ≠ []
  ──────────────────                ─────────────────────────────
  G ⊢ Ev[e] → Ev[e']                G ⊢ Ev[e] → fault φ
```

That `handle Ev with h` is a context expresses evaluation proceeding **under** an installed handler, and it carries no `@ ( … )` because the step that opens the region consumes it: the initial values are evaluated first, in the context above it, and once they are values the whole form becomes a region wrapping an installed handler. That `letjoin … in Ev` is one lets the body of a join point binding be evaluated normally. A fault propagates out of every context, including `handle`, since no handler can intercept it.

Capturing a continuation requires a second notion: a context installing no handler for the key in question.

```text
Ev_k ::= an evaluation context in which every `handle _ with h'`, `handleO _ with h'`,
         and `handleI _ with h'` on the path to the hole has a key other than k
```

Reaching a cell requires the same notion once more, over regions rather than handlers.

```text
Ev_c ::= an evaluation context in which no `region [r] θ in _` on the path
         to the hole has k in dom(θ)
```

`Ev_c` picks the **innermost** region declaring `k`, exactly as `Ev_k` picks the innermost handler of a key. **Regions nest at run time.** A handler owning one may be applied within the computation another such handler handles, so a path to the hole may pass through several `region [r] θ in _`. What typing admits at most one of is a region in a **row**, which is what makes the region an expression can *reach* unique; it does not make the term carry one. Reduction has no types to consult and finds the region by walking, and `Ev_c` is what says which one it finds.

A `jump` appears only in tail position, so the position it may occupy is narrower than a general context.

```text
Tl ::= []  |  letjoin j' (x̄ : τ̄) : τ = e' in Tl
```

### Ordinary reduction

```text
  (λ(x : τ). e) v                    →  e[x := v]
  (Λ(a : κ). v) [σ]                  →  v[a := σ]
  (Λ(_ : C). v) [•]                  →  v

  (openEff [ρ] v) w                  →  openEffC [ρ] (v w)
  openEffC [ρ] v                     →  v


  let x : τ = v in e                 →  e[x := v]

  select k (extend k v1 v2)          →  v1
  select k (extend k' v1 v2)         →  select k v2               when k ≠ k'
  restrict k (extend k v1 v2)        →  v2
  restrict k (extend k' v1 v2)       →  extend k' v1 (restrict k v2)   when k ≠ k'
  update k (extend k v1 v2) v3       →  extend k v3 v2
  update k (extend k' v1 v2) v3      →  extend k' v1 (update k v2 v3)  when k ≠ k'
  merge {} v                         →  v
  merge (extend k v1 v2) v3          →  extend k v1 (merge v2 v3)
```

`absurd [τ] v` has no rule: its argument has type `Variant ()`, which is uninhabited, so the redex does not arise.

**Application through `openEff`.** Discarding the coercion outright would not preserve typing. Consider a pure `f : Int -> Int` inside

```text
let x : Int = (openEff [( E )] f) 0 in perform E.op Prim.Unit
```

The whole term is typed at ambient row `( E )`, and the rule for `let` requires both its parts to share that row. Rewriting the bound expression to `f 0` would give it row `()`, which no longer matches the body, and no common ambient row exists. Widening the type of the function value is therefore replaced by widening the **ambient row of the resulting computation**, which `openEffC` records. Once that computation reaches a value, the coercion is discharged: a value is pure, so `openEffC [ρ] v → v` keeps both the type and the row.

**Foreign and constructor application** is given by the spine rules above. A foreign reduces once its spine is saturated, and `δ_f` yields a value or a fault.

**Recursive bindings** install recursive closures, and a closure unfolds only where it is eliminated.

```text
  letrec { x̄ : σ̄ = v̄ } in e          →  e[ x̄ := rec̄ ]    where rec_i = rec_i(x̄ : σ̄. v̄)

  rec_i(x̄ : σ̄. v̄) w                  →  (v_i[ x̄ := rec̄ ]) w
  rec_i(x̄ : σ̄. v̄) [σ]                →  (v_i[ x̄ := rec̄ ]) [σ]
  rec_i(x̄ : σ̄. v̄) [•]                →  (v_i[ x̄ := rec̄ ]) [•]
```

Unfolding is confined to elimination position, so the rules do not overlap and no term steps to itself. Guardedness (D14) makes each `v_i` a function value, which is what allows initialization to install `rec_i` without evaluating anything; it does **not** claim that a recursive computation terminates, and Core makes no such claim anywhere.

An implementation allocates locations and back-patches rather than duplicating the binding group. The two agree because no `v_i` reads an `x_j` while it is itself being installed.

### Pattern matching

Descending a decision tree takes reduction steps of its own, so that a `guard`'s condition can be evaluated in place and each of its steps remains observable from the surrounding handler.

`match θ dt` is a run-time form, not source syntax. `θ` maps occurrences to values.

```text
  case (v̄) of dt                     →  match {s_i ↦ v_i} dt

  match θ (leaf e)                   →  e
  match θ (bind x = o in dt)         →  match θ (dt[x := θ(o)])      substitute first
  match θ (guard true dt1 dt2)       →  match θ dt1
  match θ (guard false dt1 dt2)      →  match θ dt2

  match θ (switchCtor o { Ctor_i -> dt_i } [default -> dt_0])
     →  match θ dt_i        when θ(o) is an application of Ctor_i
     →  match θ dt_0        otherwise, if a default is present

  match θ (switchLit o { c_i -> dt_i } default -> dt_0)
     →  match θ dt_i        when θ(o) = c_i
     →  match θ dt_0        otherwise

  match θ (switchKey o { k_i -> dt_i } [default -> dt_0])
     →  match θ dt_i        when θ(o) injects k_i, looking through weaken
     →  match θ dt_0        otherwise, if a default is present
```

Substituting in `bind` **before** the recursive step is what allows a later `guard` to mention the bound variable; deferring the substitution would leave the condition with a free variable and no way to evaluate.

`θ(o)` follows the projection path of the occurrence, which involves no computation. `switchKey` looks through any `weaken` wrapping the value to find the key actually injected.

Local totality ([Terms and Matching](04-Terms-and-Matching.md)) guarantees that one case always applies, so `match` never gets stuck.

`guard` is the only sequential test; every `switch*` is a single dispatch, so the written order of its branches has no influence.

### Join points

```text
  letjoin j (x̄ : τ̄) : τ = e1 in Tl[jump j (v̄)]
      →  letjoin j (x̄ : τ̄) : τ = e1 in Tl[ e1[x̄ := v̄] ]

  letjoin j (x̄ : τ̄) : τ = e1 in v    →  v
```

`Tl` is a tail context, and a join point is out of scope under `λ`, `Λ`, and `handle`, so the position of the `jump` lies within the same function activation as the `letjoin`. That is what allows a backend to compile a jump as a transfer of control rather than as a continuation.

The second rule discards a binding whose join point is no longer reachable.

### Operations and handlers

`H` below stands for any of `handle`, `handleO`, and `handleI`: the two rules for a `perform` are the same whichever it is, neither of them reading a region or disturbing one.

```text
  H Ev_k[ perform k.op [σ̄] v ] with h    →  e_i[ b̄_i := σ̄,  x_i := v,
                                                k_i := λ(y : τ_i'). H' Ev_k[y] with h ]
                                            where h = { handles ent ; … }, key(ent) = k,
                                              its clause for op is
                                              full op [b̄_i] (x_i, k_i) -> e_i,
                                              and H' is handleI where h owns a region
                                              and handle where it does not

  H Ev_k[ perform k.op [σ̄] v ] with h    →  let y : τ_i' = e_i[ b̄_i := σ̄,  x_i := v ] in
                                              ( H Ev_k[y] with h )
                                            where h = { handles ent ; … }, key(ent) = k,
                                              and its clause for op is
                                              fast op [b̄_i] (x_i) -> e_i
```

**Both rules require `key(ent) = k`.** `Ev_k` says only that no *nearer* handler carries the key; that the one chosen carries it is a separate condition, and without it a handler of some other effect declaring an operation of the same name would match. The key is read from `ent`, which is what the handler writes, and never from the clause's name.

**A resumption rebuilds `handleI`, never `handleO`.** A region has one owner, and it is the handler the opening step installed; what a continuation reinstalls stands inside that region rather than owning one. This is the distinction the `handleO` marker exists to record, and the rules for a value below are where it is read.

**A `fast` clause binds its body with a `let` rather than placing it in the hole.** The body is a computation of the clause's own row, and the hole is at the handled computation's, which carries no region; binding the value and putting *that* in the hole is what makes the two agree. No continuation is constructed either way (D28), and for a handler owning no region the two formulations agree, the clause's row lacking the handled key by sharpness in both.

**That the region wraps the handler is what puts a cell where a clause can reach it.** Both rules place the clause body *outside* the handler — and the region stands outside that, so the body is still within it. Had the region been installed inside, a clause would run past its own cells and reach none.

### Where a handler finishes

```text
  handle v with h                             →  e_r[x := v]
                                                 no region; unchanged

  handle e with h @ ( v̄ )                     →  region [r'] ( k̄ ↦ v̄ ) in
                                                   ( handleO e with h[r := r'] )
                                                 where h = { handles ent ; cells [r] ( k̄ : σ̄ ) ; … }
                                                   and r' is globally fresh; the renaming is
                                                   capture-avoiding and binder-aware

  region [r] θ in ( handleO v with h )        →  e_r[x := v]
                                                 the owner finishes: the region closes and the
                                                 return clause runs outside it, in one step

  handleI v with h                            →  openEffC [( region r ι )] ( e_r[x := v] )
                                                 where h declares cells [r] ( k̄ : σ̄ ) and ι = ( k̄ : σ̄ );
                                                 a reinstatement finishes: the return clause runs
                                                 and the region it stands in is untouched

  region [r] θ in v                           →  v
                                                 a full clause's answer: the region closes with
                                                 no return clause, that clause having already run
```

Four paths reach a value and the four rules are what tell them apart.

| Path | Rule | Return clause | Region |
| --- | --- | --- | --- |
| the owner's computation finishes | the third | runs, at `ρ` | closes |
| a `full` clause produces the answer | the fifth | does not run, having run already or not at all | closes |
| a resumption's computation finishes | the fourth | runs, widened to `ρ'` | stays open |
| a `full` clause resumes off the tail, or more than once | the `full` rule above, then the fourth once per resumption | runs once per resumption | stays open throughout |

**The third rule is compound, and that is what keeps the final state out of the answer of an ordinary return.** Closing the region and running the return clause are not two steps with a moment between them at which both a cell and an answer exist; and the return clause stands at `ρ`, so it could not name a cell even were one still open ([Typing Rules](05-Typing-Rules.md)).

**The fifth rule is what the `full` path needs.** A `full` clause replaces the handler with its own body, so what the region comes to wrap is that body, and when the body reaches the answer the region has nothing left to serve. `r ∉ ftv(β)` is what makes discarding it sound: the answer's type cannot mention the region, so no part of the answer can be reaching into it.

**The fourth rule widens, and that is not decoration.** A reinstatement's return clause runs where a region is open, so its row must be `ρ'` while the clause is typed at `ρ`; `openEffC` records the difference and erases (D8).

Three things are visible in the `full` rule.

**The handler is reinstalled.** The continuation `k_i` rebuilds `H' Ev_k[y] with h`, so resuming returns under the same handler. This is what makes handlers deep (D15). `H'` is `handleI` where the handler owns a region and `handle` where it does not; either way the handler is the same one, and only its standing as a region's owner is not passed on.

**Only the key of the handled element is consulted.** A handler writes the element whole, `handles ent`, because typing needs its payload; reduction reads `key(ent)` and nothing else, so an erased handler keeps the key alone.

**The innermost handler of the key is the target.** `Ev_k` lets no `handle` of key `k` stand between the chosen one and the hole, which is what makes it innermost; handlers of one key may nest, and this is how one is picked. No offset is needed to say which element of the row is meant, since sharpness leaves only one of that key. Two instances of one effect do not interfere either: a handler keyed `cache` is not a handler for `counter`, and a `perform counter.get` passes straight through it.

`k_i` is an ordinary function value. Nothing in the rule restricts how often it may be applied, which is the sense in which the reference semantics is multi-shot (D18).

**The `fast` rule constructs no continuation** (D28). The clause body is bound by a `let` and the handler rebuilt around the same `Ev_k` with that binding in the hole, so control reaches the handled computation again without a function value ever being made. The `let` is what reconciles the two rows: the body stands at the row a clause is typed at, the hole at the handled computation's, and a variable is at home in either.

**The body runs outside `Ev_k` as well as outside the handler, and the first is observable.** That it stands outside the handler itself changes nothing, since a clause body's row lacks `key(ent)` by sharpness and it cannot perform on the key being handled wherever it runs. `Ev_k` is another matter: it may install a handler of some other key, or open a region declaring a cell key the body names — a function that handles an effect internally is pure to its caller, and one reached through `openEff` from under `h` puts its handler and its region inside `Ev_k`. The body reaches neither. What it installs itself is inside the body and is reached first, as usual; past that, what it looks for is found outside `h`. An operation it performs is answered by a handler outside `h`, and a cell it reads or writes is found outside `h` too — in `h`'s own region where `h` owns one, that region standing outside `h`, and otherwise in whichever region further out declares the key. A machine that runs the body on top of the whole continuation, rather than beside it, therefore passes over `Ev_k` whenever the body looks for a handler or a cell ([Bytecode](../05-Backend/01-Bytecode.md)).

A body that never reaches a value leaves the handled computation unfinished. The rule says what becomes of a value the body produces and requires no value of it; diverging, faulting, and performing an operation of `ρ` that is never resumed are the three ways that happens, the last of them recorded in the row ([Effects](03-Effects.md)).

Since nothing is captured, the `fast` rule raises none of what D18 leaves open on its own account: it binds the body once and holds no continuation that could be applied again. The construct able to demand a multi-shot continuation is therefore `full` alone, which is what confines the gap recorded above to `full` clauses.

**That is not the same as the program being one-shot.** Where the body performs an operation of `ρ` and that operation's `full` handler applies its continuation twice, that continuation rebuilds its own handler around `Ev_k` and so runs `Ev_k` twice — the computation after the original `perform` is duplicated, by the other handler's continuation rather than by this rule.

`fail τ` reduces through these rules too, being derived notation for `perform Partial.abort [τ] Prim.Unit`; which of the two applies is settled by the form of the installed handler's clause for `abort`.

### Cells

```text
  region [r] θ in Ev_c[ readCell k ]      →  region [r] θ in Ev_c[ θ(k) ]        k ∈ dom(θ)

  region [r] θ in Ev_c[ writeCell k v ]   →  region [r] θ[k ↦ v] in Ev_c[ Prim.Unit ]
                                                                                k ∈ dom(θ)
```

**A write rewrites the evaluation context.** Nothing is mutated and nothing is shared: the region is a part of the term, and the step replaces it with another region. This is what makes a cell a binder with a lifetime rather than a location (D36).

What follows is the interaction with continuations, and **which continuations it holds of is the whole of it.** A continuation is `λ(y : τ_i'). H' Ev_k[y] with h`, so what it carries is whatever `Ev_k` contains — and whether that includes a region depends on where the capturing handler stands.

| The capturing handler | Does `Ev_k` contain the region | What two resumptions see |
| --- | --- | --- |
| installed **outside** the region | yes | each begins from `θ` as it stood at the capture |
| the handler **owning** the region | no, the region stands outside it | both share the region, so a write under the first is visible to the second |

The second row is not an omission. A handler's own cells are its state across the operations it handles, and a `full` clause that resumes twice is resuming its own computation twice; the cells staying live through that is what makes them the handler's. The first row is what makes composition order observable, and it is the one that distinguishes this design from a store.

```text
-- runCounter owns a region whose cell n holds 0.
-- Nd is handled OUTSIDE it, by  full flip (_, k) -> pair (k True) (k False).
-- Ev_k for that flip contains runCounter's region, so each resumption
-- begins with n at 0.
```

**That the snapshot is free where it matters is the point of the placement.** A `fast` clause captures nothing (D28), so the common path — a clause that reads and writes and hands control back — copies no cell at all; where a capture does happen, the values ride along in a context that was being copied regardless. This is what a store would not give: two resumptions would share one location whatever the composition order, and the first row of that table would read like the second.

## The runtime boundary

Core reduction halts once it has constructed a value of type `IO`. **This is by design, not an omission** (D25).

Executing an `IO` belongs to the runtime ABI, which is a separate normative specification. Core's semantics ends at the boundary, and the ABI is obliged to define:

- execution of `Base.IO.pure` and `Base.IO.bind`
- execution of native leaf actions, that is, the `IO` values that `foreign` declarations construct
- the world state or external events these act upon
- the invocation of `main : IO Unit`, the point at which a program begins

The two sides of the boundary carry different kinds of obligation, and conflating them overstates what the type system delivers.

| | Established by |
| --- | --- |
| A `foreign` type is honest about where effects may appear in its arrows | D23, checked syntactically ([Modules](../06-Modules/01-Modules.md)) |
| A `foreign` implementation constructs a reified computation rather than running one, and performs no proper effect | `Σ ⊨ G` condition (3) above, a conformance obligation on the backend |
| It has no observational effect either — no hidden read or write, and no fault | the same condition, **where the declaration asserts `#observ(none)`**. An entry carrying no directive owes none of this |
| An `IO` value is executed, and executed once per execution of the value containing it | the runtime ABI |

That `Js.Console.log s` defers its effect therefore rests on the second row, not the first. D23 makes the declaration incapable of *claiming* to be effect-free while sitting on an effectful arrow; it cannot make an implementation behave.

Placing execution outside Core keeps the trusted core free of **world** state: a file, a clock, and a console are reached by running an `IO` and by nothing else. What it no longer does on its own is leave the reduction relation closed and deterministic, an entry reading hidden state having no rule here at all; that is **guaranteed** of a program whose every `δ_f` is Core-modelled — a premise beside `Σ ⊨ G`, and which an unannotated entry may well be, `Base.String.codePointAt` among them — and for one whose foreigns are not it is unshown rather than false (above). The cost is that the ABI must be specified separately before a program can be run end to end ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

## Erasure

Erasure `⌊·⌋` removes the forms that carry no run-time content.

```text
⌊Λ (a : κ) . v⌋   = ⌊v⌋        ⌊e [τ]⌋           = ⌊e⌋
⌊Λ (_ : C) . v⌋   = ⌊v⌋        ⌊e [•]⌋           = ⌊e⌋
⌊T [[κ̄]]⌋         = ⌊T⌋        ⌊M.x [[κ̄]]⌋       = ⌊M.x⌋
⌊openEff [ρ] e⌋   = ⌊e⌋        ⌊openEffC [ρ] e⌋  = ⌊e⌋
⌊weaken k [τ] e⌋  = ⌊e⌋

⌊letjoin j (x̄ : τ̄) : τ = e1 in e2⌋  = letjoin j (x̄) = ⌊e1⌋ in ⌊e2⌋

⌊{ handles ent ; cells [r] ( k̄ : σ̄ ) ; return (x : τ) -> e_r ; cl_i }⌋
    = { key key(ent) ; cells ( k̄ ) ; return x -> ⌊e_r⌋ ; ⌊cl_i⌋ }

⌊full op [b̄] (x : σ, k : τ) -> e⌋  = full op (x, k) -> ⌊e⌋
⌊fast op [b̄] (x : σ)        -> e⌋  = fast op (x)    -> ⌊e⌋

⌊handle e with h @ ( ē )⌋  = handle ⌊e⌋ with ⌊h⌋ @ ( ⌊ē⌋ )
⌊handleO e with h⌋         = handleO ⌊e⌋ with ⌊h⌋
⌊handleI e with h⌋         = handleI ⌊e⌋ with ⌊h⌋
⌊region [r] θ in e⌋        = region ⌊θ⌋ in ⌊e⌋
⌊readCell k⌋               = readCell k
⌊writeCell k e⌋            = writeCell k ⌊e⌋
```

This is **not** a reduction relation. `openEff`, `openEffC`, `weaken`, and `[[κ̄]]` change a term's type or its ambient row, and `[[κ̄]]` additionally discards an instantiation that the typed rules require. A backend erases first and then evaluates; the typed relation above evaluates without erasing.

An erased handler carries the key alone: the payload of the element is what says which operations the clauses must exhaust, and that is settled before evaluation begins. The result type of a join point goes the same way, being written for the checker rather than for reduction.

**A region keeps its keys and its values and loses everything else.** The region variable `r` and the types the layout assigns are annotations for the checker; the keys are not, since reduction pairs them with the initial values in order and `Ev_c` walks by them. So an erased handler carries the key sequence and an erased region carries `θ`, which is the run-time content there is (D36).

**The `full` and `fast` markers survive erasure.** They carry no type information; they say what a clause binds and which reduction rule applies to it, and a backend lowers the two differently — a `fast` clause needs no representation of a continuation at all. Core writes the marker on every clause, so which rule applies is settled in the erased term as well.

A variant value loses its `weaken` wrappers, so an erased `switchKey` dispatches on the key the value carries directly. Recursive closures survive erasure, since `rec_i(x̄. v̄)` carries computational content.

## Properties

The following are stated as the properties the implementation is expected to have. They are not proved here. [Implementation Plan](../01-Introduction/04-Implementation-Plan.md) describes how each becomes a property test.

Every property assumes three things, and each does work the others do not (above). Without `Σ ⊨ G` the global environment may supply an ill-typed definition or a `δ_f` that returns the wrong thing. Without `G` being **Core-modelled** the relation gives a saturated `foreign` no step at all, so there is no reduction sequence to quantify over — which is why an environment holding `Base.Array.unsafeSet` is outside every statement below, and one holding `Base.String.codePointAt` is not. Without `e` **respecting preconditions** a step is reached whose outcome the ABI declined to fix, so what follows it is not a term these statements describe.

**The third is the one a reader is likely to want narrower, and it cannot be.** It is not a condition on `G`, since the same environment runs a program that reads only written slots and one that does not; and it is not decidable here, since nothing in these documents analyses which slots a program has written. **What it is, is a debt the library owes**, and `Data.Array` is where it is paid: an array leaves its constructors with every slot written, and an application reaching `Base.Array.unsafeIndex` through that library is a term that respects preconditions without its author having thought about it.

**Preservation.** If `Σ ⊨ G`, `G` is Core-modelled, `e` respects preconditions under `G`, `Γ; Δ ⊢ e : τ ! ρ`, and `G ⊢ e → e2` for a **term** `e2`, then `Γ; Δ ⊢ e2 : τ ! ρ`.

A step to `fault φ` is outside the statement: a fault carries no type.

Both the type and the ambient row are preserved exactly. Widening is never discarded by a step: applying through an `openEff` moves it to `openEffC`, and `openEffC` is discharged only against a value, whose type does not mention the ambient row. Handling an operation likewise leaves the row unchanged, since the clause body is typed at the residual row that the `handle` already had.

**Progress.** If `Σ ⊨ G`, `G` is Core-modelled, `e` respects preconditions under `G`, and `·; · ⊢ e : τ ! ()`, then `e` is a value, or there exists `e2` with `G ⊢ e → e2`, or `G ⊢ e → fault φ` for some fault φ.

The third case is what admitting faults in condition (3) of `Σ ⊨ G` buys. A saturated `foreign` whose implementation fails would otherwise be neither a value nor a redex.

Condition (1) of `Σ ⊨ G` is what linking establishes. Without it a global name has nothing to unfold to, and the property fails for a reason unrelated to the type system.

**Effect safety.** If `Σ ⊨ G`, `G` is Core-modelled, `e` respects preconditions under `G`, and `·; · ⊢ e : τ ! ()`, then no reduction sequence from `e` reaches a term of the form `Ev_k[ perform k.op [σ̄] v ]` in which no handler of key `k` encloses the hole.

The claim is **not** that operations are never performed. A term may be well typed at ambient row `()` and still perform operations internally: `handle (perform E.op v) with h` is such a term, and its reduction does reach the clause for `op`. What the empty row guarantees is that no operation **escapes**: every `perform` that runs is enclosed by a handler for its key, so evaluation never gets stuck on an unhandled operation.

This is the property the whole design rests on, and it is the one that testing is least likely to reveal. A violation does not crash: it produces a program that silently performs effects it declared it would not. D7 places effect rows on arrows, D20 keeps `IO` out of the effect world, and D23 forbids effectful `foreign` arrows, all in service of this single statement. Note that D23 alone is not sufficient: a conforming `δ_f`, condition (3) of `Σ ⊨ G`, is equally required, since `handle` intercepts only `perform` while a `foreign` application calls its implementation directly.

**Erasure.** If `Σ ⊨ G`, `G` is Core-modelled, `e` respects preconditions under `G`, and `G ⊢ e → e2`, then `⌊e⌋` reduces to `⌊e2⌋` in zero or one steps under the erased relation, the zero-step case being a step that only introduced or discharged a coercion. If `G ⊢ e → fault φ` then `⌊e⌋` reduces to the same fault `φ`; an erased evaluator and a typed one fail identically. The value restriction is what makes this hold: the body of a type or constraint abstraction is already a value, so erasing the abstraction cannot move evaluation to a different point.

**Non-conformance of the v0.1 backends.** The reduction rule for a `full` clause places no bound on applications of `k_i`, so a term applying it twice is well typed and has a defined reduction sequence. The v0.1 JavaScript and Wasm backends do not reproduce that sequence; they raise a run-time error at the second application. This is the precise content of the soundness gap recorded above.
