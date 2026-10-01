# Open Questions

Questions that v0.1 leaves open, with what is already known about each.

## Required for v1.0

**Close the soundness gap for multi-shot continuations.** The v0.1 Wasm backend does not satisfy the reference semantics; a second resumption raises a run-time error ([Semantics](../03-Typed-Core/06-Semantics.md)). This is a soundness gap that v0.1 accepts deliberately and that v1.0 must close. The JavaScript backend does not have it, representing a continuation itself with frames and a run loop of its own ([JavaScript](../05-Backend/05-JavaScript.md)).

Two routes are available for Wasm. Wait for a cloning primitive to enter the stack-switching proposal. Or make the reference semantics target-parameterized, which conflicts with the backend independence of Mid IR.

Until then, multiple resumptions that are **syntactically evident** — a clause mentioning `k` more than once, or passing `k` elsewhere — should warn at compile time.

## The type system

**Type-level functions and their termination, which is to say whether to move to Fω.** Adding a lambda over `Row ε` makes `Map f ρ` expressible, but conditions preserving the confluence and termination of row normalization must be settled first (D6).

This also changes the class of the calculus. Introducing a type-level lambda makes Core System Fω (D1) and brings type-level β-reduction into type equality, so that "equality is syntactic apart from row normalization" no longer holds and both equality and row unification need redesigning.

**Whether to provide annotated predicative rank-n checking.** Core can express `forall` at any rank, and unification does not identify two binders across one: two `forall`s are compared through a correspondence of their binders, and a metavariable whose solution would need the other side's binder is refused rather than guessed at ([Elaboration](../02-Surface-Language/01-Elaboration.md)). Accepting an annotated higher-rank type is therefore a **separate judgement** rather than something unification grows into.

What such a judgement does is standard, and it is bidirectional rather than equational. A `forall` is handled differently in each direction, and the two directions must not be run together.

**An annotated parameter is bound at a polytype and instantiated at each use.**

```purescript
use :: (forall a. a -> a) -> Pair Int Boolean
use f = Pair (f 1) (f true)
```

Checking the lambda against the arrow the annotation gives binds `f` at `forall a. a -> a` rather than at a monotype, and every occurrence of `f` instantiates that scheme afresh: `a := Int` at `f 1`, `a := Boolean` at `f true`, the two independent of each other. Opening `a` as one rigid variable instead would admit neither use, a single rigid `a` being neither `Int` nor `Boolean`.

**An expression checked against an expected `forall` is where a binder is opened rigidly.** `(\x -> x) :: forall a. a -> a` is checked by opening `a` as a fresh rigid variable and checking the body at `a -> a`, so that what is accepted holds for every instantiation rather than for one; metavariables created under the opened binder record it in their scope. Which of the two a given position calls for is what **polarity** decides — a type the context supplies is instantiated, a type the context demands is skolemized — and the relation that puts them together, holding where the type an expression has can serve where the context's type is wanted, is **subsumption**.

Neither direction asks unification to compare two written `forall`s: one instantiates a scheme into metavariables before unifying, the other opens a binder before creating any. So the case the unifier refuses, a metavariable whose scope is one side's binder meeting the other's, arises in neither. Three judgements come apart at that point and are better kept apart than pressed into one: **monotype unification**, **α-equality of polytypes**, and **subsumption with skolemization**.

**How much higher-rank polymorphism to infer.** Little or none, and this is not the same question as the one above. Rank-1 inference is complete without any of it, a scheme being instantiated before unification sees it, so what is at stake is only how much an author may leave unwritten at a higher-rank boundary. The shape to expect is the one PureScript has: an unannotated `let` or `where` is inferred and generalized within rank-1, while polymorphic recursion and the introduction or use of a higher-rank type require a written signature.

Note that this is independent of D3: kinds are rank-1 while types are unrestricted.

**Impredicative polymorphism** is a third question again, and nothing in view asks for it.

**Kind-polymorphic functions.** D3 places no kind quantifier in the type of a value.

```purescript
reflect :: forall k (a :: k). Proxy a -> String     -- not expressible
```

Kind-polymorphic **data types** such as `Proxy` are expressible; a kind-polymorphic **function** would require adding `forall (k : Kind). τ` to the type language. Since v0.1 has no type-level generic programming, the need does not yet arise.

It arises when `Map` or label polymorphism is introduced in Phase D, and should be judged together with reconsidering D2. Withdrawing D2 and unifying kinds with types, as PureScript 0.14+ does, would dissolve this question and the duplication of the rank question at once.

**Kind-polymorphic effect constructors.** An effect constructor carries no kind scheme ([Kinds](../03-Typed-Core/01-Kinds-and-Types.md)), so `effect E forall k. (a : k)` cannot be declared and a `Row Effect` element needs no instantiation.

Restoring it costs more than adding a row to that table. The element becomes `E [[κ̄]] τ̄`, and a row's normal form then carries a kind vector beside its argument vector. Row equality and unification compare payloads, so both would compare kinds as well. Entailment is unaffected: it decides by the keys of a normal form and the atomic facts of `Γ*`, and never examines a payload, however rich the payload becomes. Whether an effect parameterized over a kind other than `Type` is ever wanted is the question; no use has arisen. The addition is backward compatible, since an empty scheme writes nothing.

**The value domains of literals — settled.** `Int` is a 32-bit signed integer, `Number` is IEEE 754 binary64, `Char` is a Unicode scalar value, and a `String` is a sequence of those (D27, D37). Literal identity is equality of the value, which for a `Number` is equality of its bit pattern with all NaNs taken as one ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

A domain belongs to Core rather than to a backend, since two backends disagreeing on one would give a Core term two meanings. Representation stays each backend's own, and what remains of the question is elsewhere: whether arithmetic wraps or faults belongs to the ABI specification, and which surface token denotes which value belongs to the lexer, below.

**Label polymorphism and a `Symbol` kind.** D13 restricts labels to literals, so the kind grammar has nothing corresponding to `Symbol` and labels are not types.

**The principal use of `Symbol` is already served.** Reflecting type-level labels to run-time strings — PureScript's `IsSymbol` and `reflectSymbol` — is the work of a metaprogram using `normalizeRow` ([Elaboration](../02-Surface-Language/01-Elaboration.md)), so a JSON encoder derived from a closed record row is unaffected.

What remains missing is **label-polymorphic functions**: a library function that takes which field to operate on as an argument.

```purescript
over :: Proxy l -> (a -> b) -> { l :: a, ...r } -> { l :: b, ...r }   -- not expressible
```

Direct access is unaffected, since `rec.name` becomes `select name rec`, so only libraries are affected.

**The condition for introducing it.** Adding `Symbol` to the kinds entails re-validating row normalization: once symbols are types, the `s` of a `SymbolKey s` may be a type variable, row keys cease to be rigid, and the decidability of `nf` collapses.

The condition is the one already imposed on effect row elements: **keep label variables out of Core's row-extension position, confining them to constraints and the elaboration layer.** This is how PureScript handles label variables through `Cons` and `RowToList` while keeping them out of `RCons`. So long as the condition holds, adding `Symbol` is compatible with D4 and D16.

**Type equality and GADTs.** D1 does not adopt FC coercions. This should be revisited when GADTs, type-level equality proofs, or something equivalent to `Coercible` for newtypes becomes necessary.

**Relaxing the value restriction.** If restricting the body of a `Λ` to a value form becomes a burden on elaboration, it may be relaxed to requiring only an empty effect row, in which case the erasability of `Λ` needs separate justification.

D17 has increased the weight of this item: under direct style the right-hand side of a surface `let` may perform effects, so the value restriction continuously underwrites the fact that let-generalization does not generalize a non-value right-hand side. Any relaxation should be evaluated against that frequency.

**Mutually dependent instance dictionaries.** A dictionary is an ordinary value (D11), and an instance is an ordinary `nonrec` whose right-hand side is a record ([Modules](../06-Modules/01-Modules.md)). Two such declarations cannot refer to each other: a `rec` group admits function values alone (D14), and a `nonrec` refers to nothing declared later. What raises the question is where a method of one class is defined through a combinator of another — `map = liftA1`, `apply = ap` — which makes the dictionaries of one hierarchy mutually referential. PureScript meets it there and emits lazily forced bindings to break the cycle.

**The cycle runs one way through a `λ` and the other way not.** A superclass field holds the dictionary of the class above it, and holds it as the record is built; a borrowed method is a closure, and mentions the dictionary it borrows from only when called. A hierarchy is declared from the top down — a `Functor` dictionary before the `Apply` dictionary that carries it — so the reference that stands under no `λ` is **backwards**, to a value initialization has installed already, and the one that is forwards is the one under the `λ`. The present rule refuses the second regardless, where nothing would be forced.

Three ways are open, and the first needs nothing of Core.

- **A library discipline.** Each method is defined directly rather than through a combinator of a class above it, and the cycles do not arise. What it costs is a familiar way of writing an instance.
- **A guarded forward reference.** Value declarations keep their order and a backward reference is what it always was; a reference to a **later** declaration is admitted where it stands under a `λ`. This is a rule about a sequence of `nonrec` declarations and not a generalization of a recursive group, so D14, `rec`, and `letrec` are untouched — generalizing `rec` instead would ask more, a group of mutually referential records needing an allocation and a backpatching rule that Mid IR's `letrec`, which allocates closures and then fills their capture lists, does not provide.

  What it does ask for is **declaration checking in two stages**: every value's scheme registered before any right-hand side is checked, so that a name under a `λ` is in `Σ` when the body that mentions it is. The declarations keep their order and initialization is unchanged, but [Modules](../06-Modules/01-Modules.md) fixes the fold as a single left-to-right pass and that is what would give way — the design it names as the alternative, collecting signatures first and permitting forward references, is this one. The Core AST and reduction are untouched.
- **Lazily forced globals.** A group is installed as thunks and forced on demand, a re-entrant forcing being a run-time error. It admits the most and costs the most: it restores the uninitialized reference D14 exists to reject, adds a third form to `GlobalInit` ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)), and leaves initialization an order the text no longer fixes.

**What the second does not settle is an initializer that calls one of those closures.** `b = (select next a) Prim.Unit` forces a closure of `a` while `b` is being initialized, and that closure may reach a declaration standing after `b`. A syntactic condition does not see it, so the option arrives with either a run-time error at the moment of the reach — narrower than what D14 rejects, and of the same kind — or a condition stronger than guardedness.

Nothing needs settling before Phase C: that is where dictionaries arrive, and they are what the standard library needs this for first. **The shape is not theirs alone**, though — `a = { next: λ_. b }` beside `b = { next: λ_. a }` is a pair of mutually referential records with no class in sight — and the three ways above answer it wherever it arises. D14's reversibility is high, and the second way asks nothing of D14 at all.

**The operational cost of D8.** Should explicit insertion of `openEff` make elaboration unduly complex, the fallback is a decidable effect subsumption judgement `ρ ≤ ρ'`, decidable by inclusion of normal forms, which would keep type equality syntactic. Note that retreating would lose the diagnostic precision D8 provides ([Effects](../03-Typed-Core/03-Effects.md)).

**Whether `split` is needed.** The inverse of `merge`, `Record (r ⊎ s) -> Tuple (Record r) (Record s)`, cannot be executed unless the labels of `r` are known. Whether it is needed should be validated in Phase D.

## Effects

**Declaring non-conformance.** Under D18 the v0.1 Wasm backend remains non-conforming and provisionally tolerated.

D28 settles part of this. A clause is `full` or `fast`, and a `fast` clause constructs no continuation, so implementing one demands no multi-shot continuation and the construct that can demand one is `full` alone ([Semantics](../03-Typed-Core/06-Semantics.md)). A program containing `fast` clauses is not thereby one-shot: duplication arises wherever a `full` handler on the residual row applies its continuation more than once.

What remains is **how to declare and check the extent of non-conformance among `full` clauses**. Detecting a second resumption at run time suffices for now, but a program able to state that a handler requires multi-shot could fail at build time on a backend that does not conform. Answering it means a third level beside `full` and `fast`, separating a `full` clause that resumes at most once from one that genuinely branches the computation. Whatever shape it takes stays backward compatible, a `full` clause reading as unrestricted.

The other is **confirming the Wasm stack-switching proposal**. The tables in [Semantics](../03-Typed-Core/06-Semantics.md) assume that its continuations are one-shot and linear and that no cloning primitive is in the MVP. This is secondhand and should be verified against primary sources before Phase E.

**Effect-polymorphism of handlers that sequence native actions.** By D23 and the purity of `Base.IO.bind`, a handler that sequences a native action **before the continuation** must take a closed row ([Effects](../03-Typed-Core/03-Effects.md)). This is not true of `IO`-returning handlers in general: one that merely resumes synchronously, or merely abandons the continuation, may remain effect-polymorphic.

In the standard library this constraint falls on terminal interpreters, producing a non-uniformity in which only the terminal stage has a different shape.

**Higher-order operations.** An operation today is first order: its signature is `σ ->* τ`, arguments to the left of the one `->*` and the type it resumes with to its right (D21), and Core operations take one argument ([Effects](../03-Typed-Core/03-Effects.md)). A higher-order operation — one taking a computation that the handler runs, as a scoped `catch` or `local` does — has a signature `->*` cannot write, since which of its arguments are computations run under the handler, and at what row, is part of its meaning. Admitting general higher-order effects therefore restates the rule that an operation's signature has exactly one `->*` on its spine, together with what Core gives such an operation and what a clause receives for it ([Syntax](../02-Surface-Language/05-Syntax.md)).

Making it uniform requires either indexing `IO` by an effect row, or giving `Base.IO.bind` a different semantics as a runtime primitive aware of the handler context. The latter must solve the problem that deferring `k` until the `IO` executes takes the residual effect outside the handler's dynamic context.

**Independent implicit handlers, and whether an order can be forced.** An implicit handler is inserted only where the plan is totally ordered by its dependencies (D29), so two capabilities lowering independently into one target — `Console` and `File` both into `LiftIO` — are an ambiguity, and such a site writes the composition itself ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)).

Two routes would lift it, and neither is available yet. One is a **proof that handlers meeting the conditions commute**, which needs an account of what a `fast` clause's performances do under a residual handler that resumes other than once (D28); the conditions as they stand do not supply one. The other is a **declared order**, which must come from the declarations rather than from the spelling of identifiers or the order of imports, or the meaning of a program would turn on either. Evidence about how often the case arises should come before the choice.

**How a helper could be written against a handler's cells.** A handler's cells are reached from its operation clauses, and a local function in a clause body reaches them where its type is inferred. A helper that must be written down does not: its row would have to mention `region r ι`, and no source syntax writes a `RegionKey` (D16, [Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)).

**What is missing is a spelling, not strength.** A written region element would discharge nothing on its own: `handle` reads an effect application out of the element it names, and a region carries none, so a `handle` naming a region is rejected whatever the surface admits ([Typing Rules](../03-Typed-Core/05-Typing-Rules.md)). Nor is rank-2 quantification called for. Such a helper is rank-1 — `forall (e : Row Effect). RegionKey ∉ e => forall (r : Type). Unit -{( region r ι | e )}-> τ` — and a clause calling it instantiates `r` from the ambient row, which is the row its own handler's region stands in. The `Lacks` is what `( region r ι | e )` needs to be sharp, and carrying it changes nothing about the rank. Rank-2 is what a `runST`-shaped function needs, one taking a region-polymorphic computation as its argument, and a helper of this kind is not one.

The question comes down to a surface spelling for the region element, which is the one thing D16 withholds. What a spelling would buy is factoring a clause body into named helpers, which is convenience rather than expressiveness, and evidence that clause bodies grow large enough to want it should come before the choice.

**Whether an implicit handler may take parameters.** The mechanism exists — a value parameter could be a synthesis goal, resolved by the hook type classes use — so this is a question of whether it is wanted rather than of whether it can be built, and it waits on Phase C in any case ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)). The argument against is that a parameter worth writing is one the caller means to choose.

**Masking and scoped labels for effect rows.** Effect rows are sharp (D4), so Koka's `mask<exn>` is not expressible. Named instances, below, cover many of the uses, but temporarily hiding one occurrence of an effect may still require something separate.

Forwarding belongs to the same gap, and what it cannot cross is a **key**, not an effect. A clause cannot pass its operation on to an outer handler of the same key, since `handle` removes that element from the row and the clause body is typed without it ([Effects](../03-Typed-Core/03-Effects.md)). Two instances of one effect are unaffected: a handler keyed `cache` may perform on `counter` freely, those being different keys. What is needed is a semantics that distinguishes the current handler for `k` from an outer handler of `k`, and a second occurrence of the key in the row is only one way to obtain it. Three candidates are available.

- **Masking, or scoped duplicates.** The distinction is carried by the row, as in Koka
- **An explicit `forward`.** The distinction is carried by a term that skips the current handler
- **A partial handler that keeps the element.** Its rule takes `( ent | ρ )` to `( ent | ρ )`, so the keyed element remains in the row and the operations the clauses do not name travel outwards. A single key suffices

**Multiple instances of one effect constructor — settled.** An effect element may carry a written `SymbolKey`, so `( cache : State Int, counter : State Int )` is well-kinded and two instances of one effect are distinguished by their keys (D16, [Effects](../03-Typed-Core/03-Effects.md)).

Making the key the whole element type would have removed the limitation too, and remains unavailable: whether `( State ?a, State Int )` has one element or two would depend on solving `?a`, so the point at which sharpness can be decided would depend on the progress of inference — the very property D4 exists to eliminate. A written key is rigid, and decides nothing later than it decides now.

What the surface writes for such an instance, and how ordinary code names one, is not settled ([Effects](../03-Typed-Core/03-Effects.md)).

## FFI and backends

**Writing the `Base` ABI specification.** The shape is settled: `Base.*` is the versioned runtime contract, its ABI entries are graded by profile while its protocols are not, and `Σ` records neither the grading nor what a backend implements ([Prim and Base](../06-Modules/02-Prim-and-Base.md)). What remains is the content.

- **Which entries each `Base` module holds**, and the observable meaning of each, stated in terms that name no backend
- **Which manifest intrinsic type constructors the ABI manifest supplies, portable and target alike.** `Base.Array.Array` and the uncurried families are intrinsic without being part of Core, so no declaration in any module can produce them. Each needs its opaque representation and its `foreign` operations fixed together
- **Which profiles exist beyond `core-runtime` and `standard`**, and what a backend states to claim one
- **Which entries may fault, and on which inputs.** A pure entry such as an unchecked array index can fail, and no Stella type describes it. A fault is not an effect and no handler intercepts it ([Semantics](../03-Typed-Core/06-Semantics.md)); Core records only that applying a `foreign` may produce one. Enumerating them and their preconditions belongs here.

  **Arithmetic is the case that shows this is not a matter of listing the obvious ones.** Whether `Base.Int.add` may fault is a question about the entry and not about a host: a backend on a host that traps on overflow can wrap instead, and one on a host that wraps can check instead, so either answer is implementable everywhere. What the ABI settles is which of them every backend owes — the same observable meaning on all of them, as with `String` (D27). **The thirty-four operations of `stella-base-0.1` are settled**: every one faults on nothing except the entries carrying an index or a range, which fault outside it, `Base.Int.quot` and `Base.Int.rem`, which fault on a zero divisor, `Base.Char.fromCodePoint`, which faults on what is no scalar value, and `unsafeNew`, which faults on a negative count ([Prim and Base](../06-Modules/02-Prim-and-Base.md)). **One case is settled as a precondition rather than as a fault**: reading a slot `unsafeNew` left unwritten is specified for nothing, which is the single such case in this version and is what D42 introduces the notion for. The rest of the surface is what remains, and for an entry not yet fixed a consumer treats it as one that may fault. Nothing in the compiler or in a lowering may decide it, and neither may a target's convenience
- **Admitting a higher-order ABI entry.** A `δ_f` may carry a function value but may not apply one, which is what keeps the reduction rule for a saturated `foreign` atomic ([Semantics](../03-Typed-Core/06-Semantics.md)). An entry that would apply one — `Base.Array.mapPure`, the pure fast path for `mapArray` ([Modules](../06-Modules/01-Modules.md)) — therefore has nowhere to live yet. Admitting one takes a decision about the operational model: a configuration for a foreign in progress, with the callback's applications as steps of their own, or a second judgement carrying them beside the reduction relation. Either makes divergence inside a callback expressible, which is what the atomic rule cannot state; the choice is which one the four properties are then restated over
- **What running a program to completion reports.** Executing `main`'s `IO` is the runtime ABI's obligation, and what a process makes of the outcome is not fixed: which exit status a completed run has, what one a fault has, and where a fault is reported. A machine executing an entry point therefore fixes only that the `IO` is executed to completion or that a fault ends the run ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

  **The `steam` command fixes a convention of its own in the meantime**, and it is written down as one: `0` for a run that finished, `1` for a refusal before the entry point ran — a file unread, bytes rejected, a module that did not load, no entry point to find — `2` for a fault after it began, and `3` for an interpreter bug wherever it arose. That is what a shell can act on today; it binds no other front end, and settling the question here would replace it rather than be contradicted by it
- **How an implementation is given the runtime capability it needs to refuse.** It imports one today, and a brand a module keeps to itself identifies nothing across two copies of that module: a duplicated helper makes a refusal a host object, which is caught where a scalar was owed and **not caught at all where the result is `unit` or `opaque`**, neither of which reads what came back — `IO Unit` being the frequent shape ([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)). One instance is therefore a precondition of the build. Having the runtime hand the capability to an implementation — an init export it calls, rather than an import the implementation resolves — would make it unbreakable, at the cost of a different authoring contract for every implementation that refuses; which to take is open
- **What asynchrony is in Stella, and therefore whether a host implementation may await.** Nothing fixes one today: no type, no effect, and no operation says what it would be for a program to wait, so **the foreign boundary is synchronous and a host implementation returns a value it already has** ([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)). A promise crosses as an ordinary `opaque` value, which a program may hold and hand back and nothing else. **Admitting an awaiting form at the boundary first was considered and withdrawn**: the interpreter would have had to answer what a rejection and a second wait mean, which is to settle the language question in the one place with no standing to settle it, and the drive loop would carry a suspension for a wait no Core term can observe. What settles it is the reified class — whether `IO` is the only one, or an asynchronous companion joins it, and whether waiting is a proper effect a handler deals with instead (D41). One shape for the proper-effect answer is a **marker element with no operations**: a key the row carries to say that a computation may wait, which declares no operation, so that no handler removes it and only the boundary that runs the program discharges it, beside an effect of its own for failure, which waiting does not include. Core has no such key today — every `EffectKey` names a declared effect, and it is a `handle` that removes one from a row ([Effects](../03-Typed-Core/03-Effects.md)) — so this shape adds a concept rather than an instance of one. Until then a target reaches an asynchronous host API by giving it a synchronous face
- **Whether a manifest entry is bound to the `.dmo` it describes.** A `.dmo` carries no type, so a manifest that went stale without changing a name or an arity agrees with everything a loader can compare and marshals by a kind the declaration no longer has ([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)). Today the pair is a build obligation, as a `.dmo` and its `.dmi` already are. Binding an entry to a digest of the module it was written for would close it, at the cost of rewriting the manifest whenever a module is recompiled for any reason; which side of that to come down on is open
- **Which types may appear in a `foreign` declaration — settled.** Only those that can cross the boundary: the scalars, `Unit`, an `intrinsic opaque`, and a result of type `IO τ` (D44, [Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)). A `Record r` or a user-defined data type is **refused where the declaration is written**, rather than left to convention: passing one raw would fix its representation for every backend and publish what is explicitly not a published ABI. The mechanism is the one marshalling needed anyway — a signature derived from the declared type — so the restriction is what that derivation failing means, and not a second apparatus. What crosses for an abstract type is a wrapper written in Stella over the transparent one
- **How a `foreign` declaration is associated with its per-backend implementations — settled.** A compiler emits a **foreign manifest** naming, for each module, what the target reaches its implementations through, and the interpreter assembles its table from that (D43, [Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)). The implicit convention PureScript uses — a `.js` file beside the module — is rejected: it fits a backend whose implementations are source files in the tree and excludes one whose are not, so adding that backend would be a change to the format rather than a new entry in a file. What the compiler builds is the part the format fixes — the module, the foreign names, and the signatures it derives from the declared types (D44) — and the target's own part passes through unread, so adding a backend edits no module

These lie outside Core, but the longer they are deferred the more the standard library settles into a shape that depends on FFI. The first version, `stella-base-0.1`, should be fixed while writing the Phase A JavaScript backend.

**Which foreigns an optimizer may move — settled in outline.** Optimization belongs to Mid IR, and three invariants decide what it may do to an effect: it may not duplicate one, erase one, or reorder two. Structural `IO` needs little help with them. Once `Base.IO.pure` and `Base.IO.bind` are concretized — `IO a` as a nullary thunk, a bind as an explicit node that runs one — what is left is an ordinary call, which an optimizer already declines to move.

**What is settled is the shape of what an optimizer reads.** An effect belongs to one of three classes — **proper**, **reified**, and **observational** — which are not exclusive, and a declaration asserts the absence of the third with `#observ(none)` ([Semantics](../03-Typed-Core/06-Semantics.md), [Modules](../06-Modules/01-Modules.md)). The summary is two fields: `observational`, which is `None` where the annotation is written and `MayObserve` where nothing is, and `returnsIO`, derived from the result type. **Faulting sits inside `observational` rather than beside it**, so there is no third field. They travel in a `.dmi` ([Interface](../05-Backend/03-Interface.md)), and neither a `.dmo` nor the host's foreign table records either ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

**What remains open is which entries carry the annotation.** For a `Base` entry the answer is the ABI specification's, and it follows from what that specification already owes — an entry it fixes as never faulting, and whose result depends on its arguments alone, is one that may carry it. For an ordinary `foreign` the answer is its declarer's. Neither is a question the optimizer has to wait for: an entry with no annotation is a barrier, which is correct however many entries end up that way.

The rest of this entry is why the type cannot answer the question, and what the annotation costs.

**What that leaves uncovered is the entry whose type is pure and whose behaviour is not.** An allocation is one such case and a write is another, and neither is sent to `IO` by it: `IO` is for reaching the **world**, while state a call creates and hands back, or state its arguments reach, stays on the pure side ([Prim and Base](../06-Modules/02-Prim-and-Base.md)). So `Base.Array.unsafeNew` is `MayObserve` — it creates an identity a program can tell from another, which is exactly what makes duplicating or merging two calls of it observable — and `Base.Array.unsafeSet` is `MayObserve` for the write it performs. The second is the one a type is least likely to warn a reader about, and it is what a portable array library is written with. The construction entries of `Base.Array` are now fixed, so the names here are the entries themselves ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

```purescript
mapArray f xs =
  let ys = unsafeNew (length xs) in            -- no slot written yet
  let loop i =
        if i < length xs then
          let x = unsafeIndex xs i in
          let _ = unsafeSet i (f x) ys in
          loop (i + 1)
        else ys
  in loop 0
```

**The `unsafeSet` is a dead binding and is not a dead call**, and keeping the two apart is the whole of it. Eliminating the dead *assignment* is correct and costs nothing: the name `_` is unused, so it goes, and the call is still evaluated for what it does. What is not correct is going on to drop the **call**, which an eliminator does when it decides on the strength of the type alone that a call producing an unread `Unit` computes nothing. Then `mapArray` returns whatever `unsafeNew` left, and **what that is, is not a wrong value but no value at all**: `unsafeNew` writes no slot, and reading one it left unwritten violates the precondition of `unsafeIndex` ([Prim and Base](../06-Modules/02-Prim-and-Base.md), D42). So the transformation does not produce a program that computes the wrong thing; **it turns a program that respected preconditions into one that does not**, which takes it out of every property the semantics states rather than making it state a different answer. Every type in sight is pure, the write is observable through the `unsafeIndex` a later reader performs, and nothing an optimizer can see relates the two. The entry that hides a write is the same entry that lets a pure `mapArray` be written at all.

**A fault is the same thing again, reached from the other side.** `Base.Array.unsafeIndex` faults outside its range, so a call of it whose result goes unused is not removable either, and two of them may not be reordered against each other. Its type is `Array a -> Int -> a` and says nothing of it. This is not a second axis: dropping the call removes the fault, which is precisely something other than the returned value being noticed, so faulting is **inside** the observational class by the definition of it. An entry carrying `#observ(none)` therefore does not fault, and one without it may.

So the fact to be recorded is not "pure or effectful". It is **what an optimizer may do to a call of this entry** — whether an unused result makes it removable, whether it may be reordered against another such call, and whether two calls of it may be shared — and the type answers none of those. One bit answers all three, which is as fine a grading as this boundary supports.

**The reach is wider than the two backends in view.** JavaScript and Wasm both ride the host's collector, which is part of why a mutation behind a pure entry looks harmless today. A native backend brings its own, and whether a safepoint may be placed across a call that mutates memory outside `IO` is a question to answer before such a backend exists rather than after.

**What `#observ(none)` does not settle is the operational model, and that is the open part of D41.** An entry reading or writing memory the reduction relation names nowhere is not the function of its arguments that the rule `M.f ς → δ_f(values(ς))` writes it as. **So the step is undefined rather than non-deterministic**, and [Semantics](../03-Typed-Core/06-Semantics.md) adds **Core-modelled** — returning an outcome the arguments fix, a value or a fault, is the whole of what a saturated call does, so it reads no state its arguments do not carry, writes none, and creates no identity they do not determine — as a premise of the relation beside `Σ ⊨ G`. A third premise stands with them, that the term respects the ABI preconditions of the entries it calls (D42), and the four properties carry all three. The two are separate because they bind different parties: conformance is what an implementer owes and admits `unsafeSet`, while this is what the rules need and does not.

**The line is not the one `#observ(none)` draws, and this is worth keeping straight.** `Base.String.codePointAt` faults, so an optimizer treats it as `MayObserve`; its outcome is nonetheless determined by its arguments, a `String` being immutable, so it is Core-modelled and the relation handles it, faults and all. What falls outside is the whole of the mutable trio — `Base.Array.unsafeNew` for the identity it creates, `unsafeSet` for the write, and `unsafeIndex` for the read of what that write left — and with it `Prelude`'s `mapArray`. **`unsafeIndex` is the one to watch**, since its fault is what a reader notices about it and its read of unrecorded state is what puts it here.

Two ways are open. An **observational store** may be added to the configuration, with `δ_f` a transition over it: the step becomes defined, the properties recover every program, and state enters the trusted core, which is what D25 exists to keep out. Or the relation may stay as it is and such an entry be a **trusted boundary** described by conformance, which is the provisional position and which leaves the restriction standing.

**What is at stake is which programs the properties cover**, so leaving it open indefinitely is not neutral. An earlier draft of this entry argued that the state is in the payload of an opaque value and that the relation therefore stays closed; that argument is wrong — `unsafeSet` leaves the `ω` in the term exactly as it was — and it is recorded here because it is the one a reader is likely to reconstruct.

**What carries a module one way and an answer the other.** The shell is the CLI's and the evaluator is a session of Steam beside it ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)), and **what a report's answer means is settled**: a request naming a global is answered with a structural snapshot of the value it holds, and printing one is a layer above it. That is the report boundary alone — a compile-time session passes live values and handles, never snapshots of them. **What carries the two is settled**: descriptor 3 of the session process, length-prefixed frames holding JSON objects, and an envelope of requests, responses, and notifications numbered by each side ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)). What is open is the schema of a structural snapshot where it leaves the process, and the report profile the request naming a global belongs to.

**The compile-time session protocol.** A guest synthesizer asks more of the interpreter than either mode fixes: applying a guest value to arguments, carrying a `Goal`, a `Type`, and an `Expr` across as opaque handles, serving an `Elab` request and continuing the same attempt with the answer, and discarding guest execution state where an attempt is abandoned ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md), [Abstract Machine](../07-Runtime/01-Abstract-Machine.md)). **Where it lives is settled**: it is not a third mode but a profile of the one long-lived `session` mode, fixed when the session opens, and it shares that mode's framing, which is tagged from its first version so that a message kind may be added without a second boundary ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)). Separating the profiles is what keeps a REPL from reaching a compiler's metavariables. **What carries it is settled with the session itself** — the channel, the frames, the envelope, and the handshake ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)); a callback is a request of the session nested inside a request of the client, which independent numbering admits. **Loading a module and applying a guest function to tokens are settled** — the `modules` and `invoke` capabilities ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)). **The kernel callback is settled** — an `invoke` naming its attempt, the `kernel` request an invocation makes for each command and the answer that resumes it, and abandonment ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)). **What a run comes to is settled** — each way an invocation fails ends the attempt as a defect of what ran it, a guest's `throw` being the one rejection, and a cancellation calls the compilation off ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)). What is open is whether an attempt exhausted or interrupted should have outcomes of its own rather than halting (below).

What D40 settles is the part that would otherwise be hardest: the protocol holds a suspended guest computation for the length of one request and never **between attempts**, since what an attempt abandons is discarded rather than kept.

**A guest computation that loops inside one attempt is stopped by both**: a budget of machine steps the `invoke` carries, and a cancellation the client sends, which the interpreter takes between stretches of steps ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)). Fuel still bounds only the scheduler's retries. What is not settled is what the scheduler makes of the two: a budget used up halts the attempt as a defect today, where `Attempt` could instead carry an `Exhausted` or an `Interrupted` of its own, told apart from a defect and from a rejection.

**A fast path for pure cases.** `mapArray` runs the Stella loop even when the effect row is empty, rather than falling through to `Array.prototype.map`. An elaboration macro that inspects the effect row can resolve this ([Modules](../06-Modules/01-Modules.md)); it waits on the Phase B foundation and on the operational model that admits a higher-order ABI entry at all (above), and on neither Phase E nor anything in it.

**Runtime representations shared between the JavaScript and Wasm backends.** How far these can coincide.

## Modules and surface syntax

**Anonymous `...` at `Row Type`.** The rule is that anonymous spreads in one signature denote one variable per kind ([Rows](../03-Typed-Core/02-Rows.md)). This is right for effect rows, but at `Row Type` the wish for two independent open rows arises more often.

Should that frequency prove high, the option is to **limit anonymous `...` at `Row Type` to one per signature**, making two or more an error that demands names. No incorrect program is admitted either way, since an over-strong signature fails at the call site, so the decision can wait for evidence about how much is written.

Neither rule is backward compatible with the other. Code that writes names works under both, so making multiple anonymous spreads a warning is a way to defer the decision.

**Brackets for variant rows.** Records use `{ … }` and effects use `{| … |}`, so variants need brackets of their own. A variant element is keyed by a `TagKey` written `#Ok`, or by a `SymbolKey` where a name is wanted, and the spread `...ρ` is shared; only the brackets remain to be chosen ([Rows](../03-Typed-Core/02-Rows.md)).

**The surface spelling of a literal.** The value domains are settled (D37), and which token denotes which value is not: `42`, `0x2a`, and `0b101010` are one literal, `"\n"` and `"\u{A}"` are another, and what a lexer admits — separators in a numeral, an exponent, an escape — is its own question. Nothing of it reaches Core, which holds the value and compares nothing else.

**Classical monads and `do` syntax.** D17 settles effect sequencing as direct style but leaves open whether monads as data structures, such as `Maybe` or a parser, should be writable with something like `<-`. **The direction is coexistence**; the syntax is not fixed.

The condition for coexistence is known: `bind` must be effect-polymorphic ([Effects](../03-Typed-Core/03-Effects.md)).

```text
bind : forall m. … => forall a b. forall (e : Row Effect).
       m a -> ( a -{e}-> m b ) -{e}-> m b
```

Core can express this and requires no additional constructor. Because the continuation carries the effect row, a monadic binding and an effectful call may be mixed in one block.

The reason for not deciding is that **`do` should be a library syntax macro**, following the same policy that keeps `class` and `instance` from being primitive keywords. The compiler need not know about `do`. Once the Phase B foundation exists, whether to provide it is a library's decision, and competing spellings may coexist.

There is a roadmap consequence: `do` with `bind` requires a `Monad` class and therefore **Phase C or later**, since desugaring produces a `{{ Monad m by Typeclass.resolve }}` synthesis goal. Direct style needs only Phase A and the effect part of Phase E, so it is available strictly earlier.

**Surface syntax for local open.** D22 separates declaring a dependency from introducing names into scope, but the spelling and details are open.

- Whether `lazy` is the right keyword. What is deferred is the point at which names enter scope, not the loading of a module
- Whether to provide both the expression form `M.( e )` and a block form `import M in e`
- Rules for nesting local opens and for shadowing outer bindings
- That the namespace token `A` is managed in a namespace separate from values and types
- **Whether a header may select or hide names**, as in `import Js.String (JSString)`. The three forms above bring in everything a module exports or nothing at all, and nothing between. A selective list leaves D22 intact, since the header still names the module and the dependency is on the module rather than on a name within it; what it changes is only which names enter scope unqualified

None of this reaches Core.

Should a design without the header entry be adopted later, it must be stated in the build system's specification that **dependencies are not determined by the header alone**; planning incremental builds and parallel compilation would then require scanning module bodies. That is where OCaml sits, and D22 avoids it.

**Strengthening the module system.** D22 forgoes functors and sealing by signature. Whether export lists alone suffice for abstraction in a large library needs validation in practice. Strengthening the system requires returning to the design of Core, so the decision has low reversibility and should be assessed once the shape of the standard library is visible, in Phase C or later.

## Implementation

**Compiling metaprograms during bootstrap — settled in outline.** Policy is guest Stella code and mechanism is the compiler's, and the circle is cut by layers rather than by an exception: a kernel elaborator using no class, no macro, and no synthesis compiles `Stella.Elab` and a small guest synthesizer, which then runs on Steam against the host's mechanism (D39, [Elaborator API](../02-Surface-Language/03-Elaborator-API.md)).

The content of `Stella.Elab` is settled: one kernel operation, `command`, whose requests and answers mirror the kernel's vocabulary, with views of the same shape the host reads through, and over it a typed operation for each kernel operation, `transact`, and `synthesizer` ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)). What remains is the caching and loading below.

**Caching and loading compiled metaprograms.**

**Coherence and termination guarantees for the standard type class resolver.** These are library policy, and Core imposes nothing ([Elaboration](../02-Surface-Language/01-Elaboration.md)).

**A serialization format for Core**, corresponding to CoreFn's JSON. What a module's interface carries — types, attributes, effect declarations, constructor tags, bodies eligible for inlining — is directly tied to the unit of separate compilation.

D34 settles where the artefacts are and which of them others build on: the compiler writes a `.dmi` and a `.dmo` per module, and what a backend outside it reads is the lowered form rather than Typed Core ([Bytecode](../05-Backend/01-Bytecode.md)). Two things remain. The **rest of the content of a `.dmi`** is determined by what optimization across a module boundary requires, and is settled when the optimizer is written; what a compiler already needs of an import is fixed, namely the definitional arity of each value it exports ([Interface](../05-Backend/03-Interface.md)). The **exported types** wait on this question rather than on the optimizer: an importing module is type checked against the signature of each import, and a signature is Core types. Whether **Typed Core is serialized at all** is separate: nothing outside the compiler consumes it, and whether the compiler itself wants to cache it is a question about incremental builds rather than about what is published.

**Kind inference for mutually recursive data and effect declarations.** Core assumes every kind is explicit; the procedure by which elaboration supplies them must be settled.

## The runtime ABI

D25 places execution of `IO` outside Core, which leaves a specification to be written. Until it exists, no program can be run end to end, so it is required before the vertical slice can do more than type check and compute pure values.

It must define:

- execution of `Base.IO.pure` and `Base.IO.bind`
- execution of native leaf actions, the `IO` values that `foreign` declarations construct
- the world state or external events these act upon, and whether execution is deterministic with respect to them
- the invocation of `main : IO Unit`, and what a program's exit value is
- what happens when a native action raises, since D23 keeps such behaviour out of the type

Two properties should be stated there rather than in Core. That an `IO` value is inert until executed is what Core guarantees to the ABI, given a conforming `G` — D23 keeps effects out of the arrows of a `foreign` type, and condition (3) of `Σ ⊨ G` keeps an implementation from running a reified computation it constructs. **Condition (3) does not keep every effect out of an implementation**: an entry carrying no `#observ(none)` may read and write hidden state and may fault when it is applied, and what stays deferred is the reified computation and nothing else ([Semantics](../03-Typed-Core/06-Semantics.md)). That the ABI executes each action exactly once per execution of the value containing it is what the ABI guarantees in return.

Whether the ABI is shared between the JavaScript and Wasm backends, or specified per backend with a common core, is open. It interacts directly with the `Base` ABI specification above, since native leaf actions are exactly what the `core-runtime` profile obliges a backend to implement.
