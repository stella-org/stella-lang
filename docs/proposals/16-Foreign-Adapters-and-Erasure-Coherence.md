# Typed Foreign Adapters and Erasure Coherence

Status: Proposed

## Purpose

This proposal repairs the account of polymorphic `foreign` calls in the typed and erased
operational semantics. The third proof-oriented review of the F* mechanization found that the
current conformance condition cannot be inhabited by shipped polymorphic intrinsics such as
`Base.IO.pure : forall a. a -> IO a`, which may return an opaque value whose Core annotation is
`IO a`.

A smaller example in the Core semantic model is:

```text
foreign mkNil : forall a. Unit -> List a
```

It must reduce at `[Int]` to a value such as `M.Nil [Int]` and at `[String]` to a value such as
`M.Nil [String]`. D44 prevents this particular declaration from being exposed through the ordinary
host-FFI boundary; it is used only to make the semantic mismatch visible. In both examples, the
annotations are required to type the reduct, but the current semantics gives `δ_f` only
`values(ᾱ)`. It deliberately withholds the kind, type, and constraint applications in the chain
because a backend evaluates an erased call.

The two requirements are individually right and jointly incomplete:

- the **typed** reduction needs the instantiation in order to construct a typed Core reduct; and
- the **run-time implementation** must not receive or depend on information erasure removes.

The repair separates those two levels for the **Core-modelled** part of a foreign implementation.
A typed semantic adapter receives the instantiation as ghost information and constructs the
annotated outcome used by typed reduction. Its erased counterpart still receives erased value
arguments alone. An erasure-coherence condition requires their entire observable outcomes to
agree and therefore prevents the ghost instantiation from changing run-time behaviour.

This correspondence contract is not general conformance. A conforming host implementation may
still read or write state outside the Core configuration, as the mutable-array entries do today.
Such an entry remains admissible but is not Core-modelled and has no step in the Core reduction
relation. Its ABI precondition and outcome may depend on the host state; the new contract does not
turn either into a function of the arguments alone.

The same review found two related closure conditions:

1. at a fixed host state, an ABI precondition must not distinguish typed values that erase to the
   same run-time values; and
2. a value returned by a foreign must be covered by the global environment, including global
   references latent under a lambda, handler, decision tree, or other value constructor.

Without the second condition, one-step progress still holds, but a foreign may return a closure
that becomes stuck at an undefined global on a later step. The existing conformance condition on
definitions in `G` does not cover values newly returned by `δ_f`.

This proposal changes the semantic contract of `G`; it does not change source syntax, Core typing,
the Core checker's acceptance relation, the ABI calling convention, or generated backend code.
The instantiation accepted by the typed adapter is proof data, not a new run-time argument.

## Problem

### The typed reduct needs information the implementation cannot observe

For a saturated, well-typed chain

```text
M.f [[κ̄]] ᾱ
```

let the cursor produce the residual result `⟨ σ ; θ ⟩`, so the call has result type `θ(σ)`, and let
`v̄ = values(ᾱ)`. The current typed rule is written schematically as

```text
M.f [[κ̄]] ᾱ  →  δ_f(v̄)
```

while conformance asks that `δ_f(v̄)` be a value of type `θ(σ)` under the run-time contexts of the
call, or an ABI fault.

For `mkNil [τ] Unit`, the same `v̄ = [Unit]` occurs for every `τ`. One function of `v̄` cannot
return both `M.Nil [Int]` and `M.Nil [String]`. Requiring a single returned term to have every
instance type is not an abstraction barrier; it is an impossible obligation. The same problem is
visible in every polymorphic foreign that returns an `opaque` value carrying its intrinsic type.

Passing `κ̄` and the type arguments of `ᾱ` to the actual backend implementation would make the
typed rule easy to write, but would contradict erasure. The erased relation calls a foreign after
kind, type, and constraint applications have disappeared. A backend must neither receive those
arguments nor choose a different run-time result from them.

### The current erasure equation conflates two functions

The current specification writes:

```text
⌊δ_f(v̄)⌋ = δ_f(⌊v̄⌋)
```

The left side needs a function producing annotated Core values. The right side is the backend
implementation on erased values. Treating them as one function hides the information mismatch
above.

It also leaves unclear what equality requires when a call is outside an implementation's domain,
when it faults, or when two typed argument lists differ only in erased annotations. Erasure safety
needs agreement of the complete outcome, not only of successful result values.

### Preconditions must be stable under erasure

Separating an ABI precondition from the partial implementation is necessary but not sufficient if
the precondition is a predicate on typed Core syntax. A value argument may contain a type
application or an intrinsic annotation even though the foreign's head instantiation is not passed
to the predicate. Such a predicate could accept one annotated value and reject another value with
the same erasure.

An ABI precondition describes a run-time call. It may depend on host state, but at any fixed state
it must be stated on erased values or be proved invariant under erasure. The implementation's
obligation and the program's obligation remain distinct:

- conformance requires a defined, conforming implementation outcome whenever the ABI precondition
  holds for a well-typed call; and
- the safety properties assume that every foreign reached by the program satisfies that
  precondition.

Outside the precondition, the ABI fixes no result.

### A returned value may introduce an uncovered global

Condition (1) of conformance covers names mentioned by the definitions installed in `G`. It does
not presently say that a value freshly returned by a foreign is covered. An implementation could,
for example, return:

```text
M.MkTask (λ (u : Unit) / (). M.missing)
```

where `M.missing` has a declaration in `Σ` but no definition in `G`. The foreign step succeeds and
the result can be well typed. Applying the latent closure later has no unfolding step.

The returned value must consequently satisfy the same term-wide coverage predicate used for an
installed global definition. Constructors need no entry in `G`; defined globals need definitions,
and foreigns mentioned in the returned value need implementations.

## Required change

### Keep general conformance distinct from Core-modelled correspondence

Let `s` range over the host state relevant to an ABI contract. It is a metavariable in the
conformance specification, not a component added to the Core configuration. A general foreign
implementation has:

```text
Pᴴ_f(s, w̄)       the ABI precondition
Iᵀ_f(s, ι, v̄)      the typed contract view of the actual host implementation
```

Both may depend on `s`. The instance witness lets general conformance state the result type without
pretending that it is passed through the ABI. In particular, `unsafeIndex` may observe whether an
array slot has been written, and `unsafeSet` may change the array. Existing conformance continues
to admit these implementations when they meet their typing and ABI obligations. No argument-only
erased function or erasure-coherence equation is required at this level.

Inside `Pᴴ_f`, `Iᵀ_f` is defined and yields an annotated run-time value or an ABI fault. The
existing conformance conditions type that value under the call's run-time contexts and constrain
the whole call, including effects not represented by its outcome.

When `M.f` is additionally **Core-modelled**, its relevant behaviour factors through two pure
semantic functions of the arguments alone:

```text
δᵀ_f      the typed semantic adapter
δᵤ_f      the erased run-time function
```

The existing Core-modelled condition is what justifies this factorization: the outcome is fixed by
the arguments, the call reads no state that they do not carry, writes no state, and creates no
identity that they do not determine. The Core rules below use these functions only under that
condition. They impose no such factorization on a merely conforming implementation.

`δᵀ_f` receives:

- an **instance witness** `ι` extracted from the chain, containing the actual kind and type
  instantiations, or equivalently enough information to reconstruct the cursor substitution and
  its instantiated result type; and
- the typed value arguments `v̄`.

Its result is partial and, when defined, is an annotated Core value or an ABI fault:

```text
δᵀ_f(ι, v̄) = value v | fault φ
```

The exact representation of `ι` is not normative. It may retain the kind and type applications of
the chain, retain the complete non-value part of the application chain, or carry the cursor
substitution. It must determine the instantiated result type `θ(σ)`. Constraint applications carry
no proof object and need not contribute any run-time data.

`δᵤ_f` receives only erased values and returns an erased value or the same ABI fault:

```text
δᵤ_f(w̄) = value w | fault φ
```

For every permitted host state and call inside the precondition, the typed contract view of a
Core-modelled implementation agrees with `δᵀ_f`, and its erased outcome is the one described by
`δᵤ_f`. The instance witness is ghost information belonging to the typed semantics. It is not added
to the ABI, bytecode, JavaScript call, native call, or any other backend interface.

### Make ABI preconditions invariant under erasure at a fixed state

In the general contract, `Pᴴ_f` may inspect the host state and the erased value arguments:

```text
Pᴴ_f(s, ⌊v̄⌋)
```

Equivalently, an implementation may expose a typed predicate `Pᴴᵀ_f`, but it must satisfy:

```text
⌊v̄₁⌋ = ⌊v̄₂⌋  implies  (Pᴴᵀ_f(s, v̄₁) iff Pᴴᵀ_f(s, v̄₂))
```

The same `s` occurs on both sides: erasure invariance forbids dependence on annotations, not on
state. Thus the precondition of `unsafeIndex` may change after a write even when its erased array
and index arguments are unchanged.

An opaque erased value retains its payload, so an ABI specification may also state a predicate
about the run-time object denoted by that payload. For a Core-modelled entry, the precondition used
by the Core reduction must itself factor through the erased arguments as `Pᶜ_f(w̄)`, with
`Pᴴ_f(s, w̄)` agreeing with `Pᶜ_f(w̄)` at every relevant state. An entry whose precondition or
outcome additionally depends on hidden state not represented by those arguments is not
Core-modelled under the existing boundary; it remains permitted by general conformance.

### Require erasure coherence of the complete outcome

For every well-typed saturated call of a Core-modelled entry inside its state-independent
precondition `Pᶜ_f`, let `ι` be its instance witness and `w̄ = ⌊v̄⌋`. Require both semantic
functions to be defined and require:

```text
eraseOutcome(δᵀ_f(ι, v̄)) = δᵤ_f(w̄)
```

where:

```text
eraseOutcome(value v) = value ⌊v⌋
eraseOutcome(fault φ) = fault φ
```

This equality covers all of the outcome:

- whether the call returns a value or faults;
- the identity and payload of the ABI fault; and
- the erased value when it succeeds.

The definedness obligation is separate from the equality: within `Pᶜ_f`, neither side may be
undefined. Outside `Pᴴ_f`, the ABI fixes neither definedness nor an outcome, and the safety
properties make no claim.

As a consequence, inside the precondition, any two legal typed instantiations and typed value lists
whose erasures agree have typed outcomes with the same erased result or the same fault. `δᵀ_f` may
use `ι` to write `M.Nil [τ]` instead of `M.Nil [σ]`, but it may not use `ι` to choose Nil instead
of Cons, to choose a different opaque identity, to fault only at one instance, or to change a fault
payload.

### Use the typed adapter in typed reduction

The typed foreign rule becomes schematically:

```text
cursorΣ(M.f [[κ̄]] ᾱ) = ⟨ σ ; θ ⟩
ι = instance(M.f [[κ̄]] ᾱ)
Pᶜ_f(⌊values(ᾱ)⌋)
δᵀ_f(ι, values(ᾱ)) = o
──────────────────────────────────────────────────────────────
M.f [[κ̄]] ᾱ  →  o
```

with the existing premises that the chain is saturated, every value argument is a value, and `G`
is Core-modelled. The erased rule remains:

```text
Pᶜ_f(w̄)
δᵤ_f(w̄) = oᵤ
────────────────────────
M.f w̄  →ᵤ  oᵤ
```

Erasure coherence makes the typed foreign step correspond to exactly one erased foreign step,
with the same fault when it faults.

### Strengthen conformance of a foreign result

Condition (3) of `Σ; Γ_N ⊨ G` continues to range over every well-typed saturated foreign chain of
values under the same well-formed `Γ_R` and `Γ_N` as the call. For each call whose general ABI
precondition `Pᴴ_f(s, ⌊v̄⌋)` holds, retain the existing requirements and additionally require that a
successful value be covered by `G` at every term node.

For an entry that is also Core-modelled, require the separate correspondence contract:

1. `δᵀ_f` and `δᵤ_f` are defined inside the state-independent precondition;
2. the two outcomes satisfy complete-outcome erasure coherence;
3. the typed contract view of the actual implementation at every permitted host state agrees with
   `δᵀ_f`, and consequently erases to `δᵤ_f`;
4. a typed successful outcome is a run-time value of the instantiated cursor result type
   `θ(σ)`, under the same `Γ_R` and `Γ_N` as the call;
5. that value is covered by `G` at every term node; and
6. a declaration carrying `#observ(none)` returns a value rather than a fault and continues to
   satisfy its existing observational obligations.

The coverage requirement belongs in condition (3), rather than being folded into condition (1),
because it is an obligation on each value produced by the adapter. Condition (1) continues to
cover installed global definitions and the module under evaluation.

All existing requirements that the call terminate, perform no proper effect, run no reified
computation, and apply no Stella function value remain part of general conformance. As before, an
implementation that reads or writes unmodelled hidden state, or creates identity not determined by
its erased arguments, may conform but is not Core-modelled and has no foreign step in this relation.

## Examples

### A polymorphic constructor result

This is an example in the Core semantic model, not a host-FFI declaration accepted by the ordinary
surface-language boundary: D44 rejects exposing a user data constructor through that boundary.

For:

```text
foreign mkNil : forall a. Unit -> List a
```

the typed adapter may be:

```text
δᵀ_mkNil(⟨a := τ⟩, [Unit]) = value (M.Nil [τ])
```

while the run-time implementation is:

```text
δᵤ_mkNil([Unit]) = value M.Nil
```

and both sides of erasure coherence are `value M.Nil`.

### An intrinsic result required by the shipped environment

For:

```text
foreign pure : forall a. a -> IO a
```

the typed adapter may return `opaque ω [IO τ]` at instance `τ`, while the run-time implementation
returns `opaque ω`. Coherence requires the same erased payload `ω`; the instance may supply the
annotation but may not select a different identity.

### An invalid Core-modelled adapter

A Core-modelled adapter that returns `M.Nil [Int]` at `[Int]` and faults at `[String]` for the same
erased value arguments is invalid, even if each branch separately has an allowed typed outcome.
Their erased outcomes differ.

### An uncovered result

An adapter returning a closure whose body refers to a declared but uninstalled global is invalid.
Typing the closure is not enough; condition (3) also requires its result value to be covered.

## What does not change

- The type, kind, purity, saturation, and erased-tail restrictions on foreign declarations remain
  unchanged.
- A backend foreign receives exactly the run-time values it receives today. No kind, type, or
  constraint argument is added to an ABI.
- The reference Core checker does not execute or validate an implementation and gains no new
  acceptance check.
- The distinction between conformance, being Core-modelled, `#observ(none)`, and respecting ABI
  preconditions remains.
- A precondition violation remains outside the language's safety guarantees. This proposal only
  makes the precondition's view of a call agree with erasure while holding its host state fixed.
- Foreigns with observational state that the Core configuration does not model remain outside the
  Core-modelled reduction relation but remain eligible for general conformance, as specified today.

## Alternatives considered

### Pass type and kind arguments to the backend

This would make the typed outcome easy to construct but would change the ABI and invalidate the
erased relation. It would also let an implementation branch on information Core promises to erase.
Rejected.

### Forbid polymorphic foreign result types

This would reject ordinary interfaces such as `forall a. a -> IO a`, including shipped intrinsics
such as `Base.IO.pure`, and would rule out semantic adapters constructing polymorphic Core values.
It repairs the proof by removing useful programs rather than by stating the intended abstraction
boundary. Rejected.

### Require one annotated term to have every instance type

This is the current accidental requirement. An annotation such as `List Int` cannot simultaneously
be `List String`. Rejected as uninhabitable.

### Return an erased value and choose arbitrary annotations afterwards

An existential reannotation relation could recover some typed reduct, but would make the typed
semantics unnecessarily nondeterministic and would not say which annotations an implementation is
allowed to construct. The typed adapter gives a deterministic annotated representative while
coherence confines its freedom to erased information. Rejected.

### Check coverage only when the returned closure is entered

This postpones a global-environment obligation until progress has already been lost. Coverage is
structural and can be required when the value is produced. Rejected.

## Reference implementation and mechanization work

### Language specification

- Preserve general, possibly state-dependent foreign conformance, and state its precondition's
  erasure invariance with the host state fixed.
- For Core-modelled entries, split the typed semantic adapter from the erased argument-only
  function in the global environment and foreign reduction rules.
- Define the instance witness used only by the typed adapter.
- Require the precondition used by Core reduction to factor through erased arguments alone.
- Add complete-outcome erasure coherence, including fault identity and definedness inside the
  precondition.
- Add coverage of successful foreign outcomes to conformance condition (3).
- Rewrite the erased relation and Erasure property to refer to `δᵤ_f`, not to the typed adapter.

### Reference compiler and backends

No calling-convention or checker change is expected. The current backend path already erases Core
types before executing a foreign. Tests should confirm that polymorphic foreigns such as `IO.pure`
continue to receive value arguments alone and that no instance witness reaches generated code.

### F* mechanization

- Change the semantic environment so its typed adapter accepts an instance witness and typed value
  arguments.
- Keep the ABI precondition independent of the adapter. The mechanized `gpre` is the argument-only
  `Pᶜ_f` for the Core-modelled fragment; the general state-dependent `Pᴴ_f` remains an ABI
  conformance boundary outside this reduction model and is specified with fixed-state erasure
  invariance.
- In the typed foreign head rule, derive the instance witness from the chain and call the typed
  adapter.
- Strengthen `outcome_ok` with coverage of a returned value.
- Preserve the current separation between the implementer's conformance obligation, the program's
  `pre_ok` obligation, and semantic partiality outside the precondition.
- Prove that coverage is preserved by a foreign step and, with the existing definition-coverage
  condition, by every reduction step.
- When the erased relation is formalized, represent `δᵤ_f` and prove complete-outcome coherence.

The mechanization may introduce the typed adapter before the erased syntax is available, but the
environment must carry the coherence obligation in a form that can later be discharged rather
than treating it as a new run-time dependency on types.

## Acceptance criteria

- A Core-modelled semantic environment exists for `Base.IO.pure : forall a. a -> IO a`, with a
  typed intrinsic annotation and an erased opaque value carrying the same payload.
- As a Core-semantics example, adapters for `mkNil : forall a. Unit -> List a` can produce typed
  outcomes `M.Nil [τ]` and one erased outcome `M.Nil`; this does not make `mkNil` an ordinary host
  FFI declaration permitted by D44.
- Inside the ABI precondition, two well-typed saturated calls of one Core-modelled foreign whose
  value arguments have the same erasure produce typed outcomes with the same erasure: the same
  value shape and payload, or the same ABI fault.
- Inside the ABI precondition, a Core-modelled adapter cannot vary definedness,
  successful-versus-faulting outcome, fault payload, or erased value according to a kind or type
  instance.
- At the same host state, an ABI precondition cannot distinguish typed value arguments with the
  same erasure. It may change when that state changes.
- Inside `Pᶜ_f`, both semantic functions of a Core-modelled entry are defined.
- Outside the ABI precondition, conformance imposes no result.
- Inside the ABI precondition, a returned value is well typed at the instantiated cursor result
  under the call's own `Γ_R` and `Γ_N`, is a run-time value, and is covered by `G`.
- Inside the ABI precondition, a foreign returning a closure that mentions an uncovered defined
  global fails conformance.
- Every Core-modelled typed foreign step erases to one run-time foreign step with the same erased
  value or the same fault.
- Existing stateful entries such as the mutable-array operations remain eligible for conformance;
  entries whose precondition or outcome depends on unmodelled state remain outside the
  Core-modelled reduction relation.
- Existing foreign declarations, generated backend calls, and the Core checker's accepted program
  set are unchanged.

## Design decision

If accepted, record the following as D53, after the decisions reserved by Proposals 14 and 15.

| Decision | Rationale | Reversibility |
| --- | --- | --- |
| **D53. For a Core-modelled foreign, a typed adapter may read a ghost instance only to construct annotations; its erased argument-only function determines the complete run-time outcome, and the typed outcome must erase to it.** A general ABI precondition may depend on host state but is invariant under erased annotations while that state is fixed. Every successful conforming outcome is also covered by `G`. | A typed reduct needs its instantiation to carry the type the cursor computes, while an ABI must not observe erased information. Separating the two semantic functions makes both requirements expressible. Complete-outcome coherence prevents instance-dependent definedness, faults, identities, or value shapes in the Core-modelled fragment, and coverage closes multi-step progress after a returned closure is entered. Keeping this contract separate from general conformance continues to admit stateful mutable-array entries without pretending that their outcomes or preconditions are functions of arguments alone. | Low. This changes the semantic model and proof obligations but not source syntax, accepted Core, ABI calls, generated code, or backend behaviour. Reversing it would either expose types at run time or make common polymorphic foreigns impossible to model. |

## Specification files to update

- [Semantics](../technical-references/03-Typed-Core/06-Semantics.md): split typed and erased
  foreign functions; revise conformance, Core-modelled, preconditions, foreign reduction, the
  erased relation, and Erasure; require coverage of returned values.
- [Typing Rules](../technical-references/03-Typed-Core/05-Typing-Rules.md): define or reference the
  instance witness obtained from a typed chain and its cursor.
- [Design Decisions](../technical-references/01-Introduction/03-Design-Decisions.md): add D53.
- [Implementation Plan](../technical-references/01-Introduction/04-Implementation-Plan.md): add
  conformance and erasure-coherence regression cases.
- [Open Questions](../technical-references/99-Open-Questions/01-Open-Questions.md): keep the existing
  question about observational foreign state separate; this proposal does not solve or widen that
  model.

## Implementation order

1. Specify the instance witness, typed adapter, erased implementation, erased precondition, and
   complete-outcome erasure operation for Core-modelled entries; separately state general
   fixed-state precondition invariance.
2. Rewrite conformance condition (3), adding outcome coverage without imposing argument-only
   behaviour on every conforming implementation.
3. Rewrite the typed and erased foreign rules and the Erasure property.
4. Add the conformance examples and negative coherence cases in the specification and
   mechanization.
5. Update the design decision and implementation-plan regression table.
6. Confirm that compiler, backend, ABI, and end-to-end tests remain unchanged except for semantic
   documentation and any new conformance-model tests.
