# Foreign Results and Latent Reads

Status: Proposed

## Purpose

This proposal closes a hole between initialization safety (D14) and the conformance of a foreign
implementation (D53). The F* mechanization of the store rules found that a conforming foreign can
return a value that reads, when applied, a member of a recursive group that no argument could read.
The judgement of [Initialization Safety](../technical-references/03-Typed-Core/10-Initialization.md)
then admits a group whose initialization reaches `φ_init`.

The judgement treats a saturated foreign chain as a constructor: it promotes nothing, and what the
chain's value may read later is what its value arguments may read later.

```text
lat( M.f [[κ̄]] ᾱ ) = ⋃ lat(eₖ)
```

That rule is sound only if the value the call returns reads, later, nothing its arguments did not
already read later. Condition (3) of `Σ; Γ_N ⊨ G` does not say so. It types the result, bounds its
global names by those of `G` and of the arguments, and forbids the call itself from applying a
Stella function value. None of these bounds what the returned value reads once it is applied.

The repair adds one clause to condition (3): **a value a foreign returns may read later only what
one of its value arguments may already read later**. It changes no syntax, no typing rule, no
checker acceptance, no ABI, and no backend behaviour.

## Problem

### The judgement trusts what a foreign hands back

A foreign may carry a function value it is given, as `Base.IO.bind` stores `a -> IO b` in the
value it builds. The judgement's rule for a saturated chain reflects that: the chain's value holds
its arguments, so it may read later what they may. Nothing in the semantics confines an
implementation to carrying its arguments. An adapter receives the arguments as Core values, closures
included, and condition (3) asks only that what it returns be well typed and covered.

### A latent read is not every read the syntax holds

`lat(e)` counts what running a closure in `e` may read. It does not count every occurrence of a
member in `e`. A join point is read where it is jumped to, so the body of a `letjoin` that nothing
jumps to contributes nothing:

```text
lat( λ (u : Unit) / (). letjoin j () : Int = x in 0 ) = ∅
```

The occurrence of `x` is in the term, typed, and covered, and it is not read.

### A counterexample

This is an example in the Core semantic model. D44 keeps such a declaration from the ordinary
host-FFI boundary; it is used only to make the gap in conformance visible.

Let `Σ` declare a foreign of arity one

```text
foreign resurrect : (Unit -> Int) -> Record ( run : Unit -> Int )
```

whose typed adapter inspects its argument. Where the argument is
`λ (u : Unit) / (). letjoin j () : σ = force ν in 0`, a `λ` whose body is a `letjoin` with the
definition `force ν` and the continuation `0`, it returns

```text
extend run (λ (u : Unit) / (). let _ : σ = force ν in 0) {}
```

at whatever type `σ` the `letjoin` writes, and otherwise returns `extend run v {}` for its
argument `v`. This adapter conforms under the current condition (3):

- the result is a value of type `Record ( run : Unit -> Int )` under every `Γ_R` and `Γ_N` the
  call is typed under, since the argument already types `force ν` at `σ` there;
- its global names are those of the argument;
- the call terminates, performs no effect, and applies no Stella function value;
- the choice reads the shape of the argument and no type: erasure keeps `λ`, `letjoin`, `force`,
  and the literal, so an erased function on the erased argument makes the same choice, the typed
  adapter supplying `σ` from the argument's annotation, and erasure coherence holds.

Now take the group

```text
letrec {
  x : Int = (select run (resurrect (λ (u : Unit) / (). letjoin j () : Int = x in 0))) Prim.Unit
} in x
```

The judgement admits it:

- `resurrect (λ …)` is a saturated foreign chain, so its `lat` is that of the `λ`, which is `∅`
  (no `jump` to `j`);
- `select run` takes the record apart, and its `lat` is the record's, `∅`;
- applying the selected closure to `Prim.Unit` is an ordinary application, and promotes that
  `lat`, which adds nothing;
- so `imm` of the right-hand side is `∅`, and `x` reads no member before it.

At run time, allocation substitutes `force ν` for `x`, and forcing `ν` runs the right-hand side
under `fill ν` with `ν` `Evaluating`. The argument's join definition is `force ν` at `σ = Int`, so the
adapter returns the record whose `run` field is
`λ (u : Unit) / (). let _ : Int = force ν in 0`, the selection yields that closure, the
application runs its body, and `force ν` finds its cell `Evaluating`: the step is to
`fault φ_init`.

A similar adapter, recognizing a global reference in a dead join definition where this one
recognizes `force ν`, breaks a top-level `rec` group during the module fold: a dead reference to a
member not yet installed comes back alive and reaches a global with no definition.

## Required change

### Bound what a result may read later

In condition (3) of `Σ; Γ_N ⊨ G`, where `δᵀ_f(ξ, v̄)` is a value `v`, add:

```text
for every recursive group R, and whatever its members may read later (lat*):
    dom(latᴿ(v)) ⊆ ⋃ₖ dom(latᴿ(vₖ))
```

`latᴿ` is `lat` of [Initialization Safety](../technical-references/03-Typed-Core/10-Initialization.md)
taken for the group `R`, under the given `lat*`, and `dom` is the set of members it maps: the
inclusion is of the members the result may read later, not of their witnesses. A witness only
locates a refusal, and an adapter building a new application or closure around an argument makes
new ones; which of them a diagnostic reports is separate from this contract. A group is a
top-level `rec` group, its members read through their global names, or a local group after
allocation, its members read through `force ν` at their locations. The judgement of a nested
group already reads a location as reading nothing; for this clause, `force ν` at a location of `R`
is a read of the member `ν`, as an occurrence of a member's name is, and the inclusion is of the
sets of locations read.

The clause is stated for every group because the implementer does not know which group, if any,
the call is made while initializing. It is relative to the arguments, as the coverage clause of
D53 is: it does not ask the result to read nothing, only nothing new.

### What satisfies the clause

- An identity, and any adapter returning one of its arguments or a part of a data value it was
  given, since a value's parts are read later only as the value is.
- An adapter storing its arguments in a value it builds, as `Base.IO.bind` does, since a
  constructor's `lat` is that of what it holds.
- An adapter returning a new closure that applies an argument when it runs, since the application
  promotes no more than the argument's `lat`.
- An adapter returning a closure that mentions no member of any recursive group and no location.

### What it rules out

An adapter that looks inside a closure it is given and returns a term in which an occurrence that
was not read becomes read: a dead join definition, or any other part of a term the judgement does
not follow, brought into a position that runs.

### What does not change

- The clause is about successful outcomes. A fault returns no value and owes nothing.
- It constrains the typed adapter `δᵀ_f`. The erased function `δᵤ_f` needs no initialization
  analysis of its own: erasure coherence makes its result the erasure of the typed one.
- It asks nothing of `imm`. An adapter receives values, whose `imm` is empty, and returns a value.
- The judgement of [Initialization Safety](../technical-references/03-Typed-Core/10-Initialization.md)
  is unchanged. The clause is what makes its rule for a foreign chain sound.
- Typing, the Core checker, the ABI, and generated code are unchanged.

## Alternatives considered

### Count every occurrence as a latent read

Making `lat` count every occurrence of a member, a dead join definition included, would make the
syntactic bound of D53 enough. It would also refuse groups the judgement now admits for a reason
unrelated to evaluation order, and make the judgement less precise for every program to repair a
fault no ordinary implementation has. Rejected.

### Bound the names a result mentions

Asking that every location and member the result mentions occur in an argument, as D53 does for
global names, does not suffice: the counterexample's result mentions only what its argument
mentions. Rejected.

### Make a foreign chain promote

Treating a saturated foreign as an application that promotes the `lat` of its arguments does not
close the gap: the read the adapter brings back is in no argument's `lat`, so promoting them adds
nothing, and the counterexample's group is admitted as before. It would also refuse
`Base.IO.bind` storing a closure that reads a later member of a group of dictionaries and actions.
Rejected.

### State the bound in the mechanization only

The mechanization could assume the clause as a premise of its initialization theorem. It would then
prove a property of a specification other than this one, and the counterexample would remain a
conforming environment here. Rejected.

## Reference implementation and mechanization work

### Language specification

- Add the clause to condition (3) of conformance, beside the coverage clause of D53.
- State in [Initialization Safety](../technical-references/03-Typed-Core/10-Initialization.md), at
  the rule for a saturated foreign chain, that conformance is what makes it sound.

### Reference compiler and backends

No change. Shipped intrinsics carry their arguments or return opaque values, which read nothing.

### F* mechanization

- Extend the conformance of a foreign result with the clause, in the form the initialization
  invariant reads: a location read later by the result is read later by an argument.
- Prove that reduction keeps the location-level initialization invariant, the foreign rule by the
  clause, and that no reachable configuration steps to `φ_init`.

## Acceptance criteria

- The counterexample's adapter does not conform.
- An identity foreign, `Base.IO.bind`, and an adapter returning a closure that applies its argument
  conform.
- Every group the judgement admits reaches no `φ_init` under a conforming `G`, foreign calls in its
  initializers included.
- Existing foreign declarations, accepted Core programs, generated calls, and backend behaviour are
  unchanged.

## Design decision

If accepted, record the following as D54.

| Decision | Rationale | Reversibility |
| --- | --- | --- |
| **D54. A value a foreign returns may read later only members that one of its value arguments may already read later**, for every recursive group, a location read through `force` counting as a read of its member. The bound is on the members read, not on the witnesses that locate the reads. | The initialization judgement treats a saturated foreign chain as holding its arguments, which is sound only if the result reads nothing new. Typing and coverage of the result do not give it: an adapter that inspects a closure can make a read the judgement never followed into one that runs. | Low. It constrains Core-modelled implementations, not syntax, typing, the checker, or the ABI. |

## Specification files to update

- [Semantics](../technical-references/03-Typed-Core/06-Semantics.md): condition (3) of
  conformance.
- [Initialization Safety](../technical-references/03-Typed-Core/10-Initialization.md): the rule
  for a saturated foreign chain.
- [Design Decisions](../technical-references/01-Introduction/03-Design-Decisions.md): add D54.
