# Kind-Polymorphic Global Initialization

Status: Proposed

## Purpose

This proposal closes a soundness gap found by the second proof-oriented review of the F*
mechanization. A top-level value may bind kind variables while its right-hand side is an arbitrary
pure term. Module initialization evaluates that term once, before any use site supplies a kind
instantiation. If the evaluation allocates a local recursive cell or opens a region, the run-time
store or region frame may consequently contain a type mentioning the declaration's abstract kind
variables.

Run-time contexts deliberately admit no such variables. A location type and the typing data of an
open region frame are kinded in a closed context containing region names and no kind, type, or term
variable. This closedness is what makes a store and a frame stable under substitution and lets one
installed global be unfolded in an arbitrary caller. The current declaration rule can break that
invariant before the global is installed.

The gap is a failure of this **closed run-time context invariant**, not an execution path that
confuses two run-time type representations. Kinds are erased, and Core has no term that branches on
a kind. Sharing the allocation between kind instances is operationally harmless in that narrow
sense; it is nevertheless outside the stated static semantics, because no closed `Γ_N` or `Γ_R`
can type the configuration that initialization produced.

The repair is a value restriction on a top-level definition whose **kind scheme is non-empty**.
Such a right-hand side must already be a run-time value. It can then be installed without taking a
step under the abstract kind variables; any allocation in a function body happens only after the
global has been instantiated and the function is applied.

This proposal follows [Core Soundness Repairs Found by Mechanization](./14-Core-Soundness-Repairs.md)
but is separate from it. Proposal 14 was accepted and implemented before this issue was found.

## Problem

### A declaration is evaluated before its kind scheme is instantiated

A Core declaration has a kind scheme outside its term:

```text
nonrec M.x : forall k̄. σ = e
```

The right-hand side is checked under the abstract kind variables:

```text
·, k̄ ; · ; · ⊢ e : σ ! ()
```

but module initialization evaluates `e` once and installs the resulting value in the global
environment. A use `M.x [[κ̄]]` supplies `κ̄` only later, when the global is unfolded. Kinds are
erased, and the run-time environment has one installed value for `M.x`, not one evaluation or one
store per kind instantiation.

Pure evaluation may still allocate. In particular, `letrec` allocates by-need locations, and
`region` allocates a region and its cells. Consider the following schematic Core declarations,
where `Witness` is a nullary data type with a kind scheme:

```text
data Witness forall k. = Witness

nonrec M.cached : forall k. Unit -> Witness [[k]] =
  letrec {
    cell : Witness [[k]] = M.Witness [[k]]
  } in
  λ (u : Unit) / (). cell
```

The right-hand side is pure and initialization-safe. Evaluating it nevertheless allocates a
location whose type is `Witness [[k]]`, then returns a closure containing `force ν`. The kind
variable `k` has no place in the closed location context `Γ_N`. Later,
`M.cached [[Type]]` and `M.cached [[Row Type]]` unfold the same installed closure and refer to the
same location while requiring its type at two different instances.

An open region gives the analogous problem for `Γ_R`: its layout and the typing data stored on the
frame may mention `k`, although a run-time layout and frame must be well formed without a kind
variable in scope.

This is not specific to `nonrec`. Every member of a top-level `rec` group is also evaluated once
under its own kind scheme and installed for all later instantiations. The restriction must
therefore be checked separately for each member whose kind scheme is non-empty.

Kinds are exceptional here because their abstraction is outside the term. An ordinary type
variable is introduced by a term-level `Λ`, whose body is already subject to a value restriction;
evaluation cannot allocate beneath that binder before it is instantiated. A declaration's kind
scheme has no corresponding term constructor, so without this repair evaluation may run under its
abstract kind variables.

### Restricting the theorem would not repair the language

One could state module-initialization safety only for declarations with no kind variables. That
would make the proof avoid the counterexample, but the reference checker would continue to accept
it. The accepted program would have no store or frame typing satisfying the specification, and two
instantiations would still share the one allocation. Narrowing the theorem is therefore not an
alternative to repairing declaration checking.

### Per-instantiation initialization is a different language

Another possible design would evaluate and cache a separate right-hand side for each kind
instantiation. It is not the current operational model: kind arguments are erased, the global
environment holds one value per name, and neither the bytecode nor the linker has a kind-indexed
cache. Introducing one would change linking, erasure, global identity, and initialization order.
This proposal does not do so.

### Kind-schemed run-time contexts are a larger repair

A less restrictive alternative would make run-time entries themselves kind-polymorphic. A store
could record `ν : forall k̄. σ` and replace an allocated member by `force ν [[k̄]]`; region layouts,
frames, and cell operations would need the analogous treatment. Because kinds are erased and Core
cannot inspect one, sharing such an entry between instances need not change the observable result.

That alternative is not a local relaxation of the current rules. It gives run-time names kind
arguments and replaces the closed-context invariants established for stores and frames in Proposal
14. The allocation, force/fill, region, substitution, and preservation developments would all need
new statements. This proposal keeps the current run-time syntax and invariants and chooses the
smaller source restriction instead.

## Required change

For every top-level value binding, require either an empty kind scheme or a right-hand side that is
a value according to the value grammar of
[Semantics](../technical-references/03-Typed-Core/06-Semantics.md):

```text
σκ = forall k̄. σ      ·, k̄ ⊢ σ : Type
Σ ; ·, k̄ ; · ⊢ e : σ ! ()      k̄ = ·  or  valueΣ(e)
──────────────────────────────────────────────────────────────────────
Σ ⊢ nonrec x : σκ = e  ⊣  Σ, M.x : σκ
```

For a recursive group, apply the same side condition independently to every member:

```text
each i: σκ_i = forall k̄_i. σ_i
        Σ' ; ·, k̄_i ; · ⊢ e_i : σ_i ! ()
        k̄_i = ·  or  valueΣ'(e_i)
```

This is the dynamic value predicate, not the narrower static `valueForm` predicate used by the
value restriction on type and constraint abstractions. Every static value form is a run-time
value, but the converse deliberately does not hold. Module initialization needs exactly the
run-time condition: a value takes no step, so it performs no allocation under the abstract kind
variables. In particular:

- literals, lambdas, empty records, records and variants of values, and constructor-headed chains
  of values qualify;
- a type or constraint abstraction qualifies when its body is a value, retaining the existing
  guarantee that evaluation takes no step beneath it;
- an unsaturated foreign-headed chain of values qualifies, as do `openEff` and `weaken` around a
  value: all are values of the reduction relation already;
- `let`, `letrec`, `region`, `handle`, an application that is not a constructor chain, and every
  run-time allocation form do not qualify merely because they are pure or eventually reduce to a
  value; and
- a reference to a defined global does not qualify. `M.y [[κ̄]]` unfolds by one step, so a
  kind-polymorphic alias such as `nonrec M.x : forall k. σ = M.y [[k]]` is rejected unless
  elaboration has eta-expanded a function-typed alias into a lambda; and
- a saturated foreign-headed chain does not qualify: it is a redex, not a value.

The distinction is intentional. A value performs no module-initialization step. A lambda may
contain an allocation in its body, but that body is entered only after the global has been
instantiated and the lambda is applied. A non-value right-hand side with an empty kind scheme keeps
its current meaning and may still be evaluated once at link time.

This is a Core condition. Surface elaboration may diagnose the restriction earlier, but every
path producing Core must pass the Core declaration checker, and the checker must enforce it even
for hand-written Core.

## Surface-language diagnosis

The inferred surface path already applies an ML-style value restriction to kind metavariables as
well as type metavariables. A member without a written signature whose right-hand side is not a
value form is therefore made kind-monomorphic and cannot violate the new Core condition.

The remaining path is a member with a written signature. Such a signature may generalize only a
kind variable, for example through a type such as `Proxy (p :: k)`, while its body is not a value.
No term-level `Λ` is introduced for that kind scheme, so the existing abstraction value
restriction does not catch it.

This proposal chooses to classify the new Core rejection as an **author error at the original
surface binding**, alongside an ill-formed attribute application and a non-value body of a `Λ` or
constraint abstraction. The elaborator need not duplicate the dynamic value predicate: when final
Core validation reports this declaration error, it uses the declaration's origin and reports the
kind-polymorphic non-value initializer there. The statement that a Core checker rejection is the
elaborator's fault consequently gains this third exception.

Eta expansion remains relevant. A function-typed global alias that is safe to move becomes a
lambda and satisfies the restriction. A non-function alias remains a global reference, takes an
unfolding step, and is rejected; this is an intentional compatibility effect.

## Consequences for module initialization

Module initialization keeps its current left-to-right, evaluate-once semantics.

- A binding with an empty kind scheme is evaluated as before.
- A binding with a non-empty kind scheme is already a value and is installed without allocation or
  another reduction step.
- A recursive group keeps its initialization-safety check. The new condition is additional:
  initialization safety prevents an early read of another member, while the kind value restriction
  prevents allocation under an abstract kind variable.
- Instantiating a global still substitutes kinds when the installed value is unfolded. Any
  computation beneath a lambda or another later-eliminated value boundary starts only after that
  substitution.

The well-formedness conditions on `Γ_R` and `Γ_N` do not change. The point of the restriction is
that module initialization can continue to maintain their existing closedness.

## Reference-checker work

- In `Stella.Compiler.TypedCore.Declare`, after checking a binding's scheme and body, reject a
  non-value body when `binding.scheme.kindVars` is non-empty.
- Apply the check to both `DeclNonRec` and every binding of `DeclRec`.
- Add one predicate corresponding exactly to the value grammar in Semantics. It may share the
  existing chain view, cursor, and saturation code, but it must not use `Check.isValueForm` as the
  whole test: that predicate intentionally excludes some run-time values.
- Add a declaration error that distinguishes this restriction from the value restriction inside a
  `Λ`. The diagnostic should name the affected global and say that a declaration generalized over
  kinds must have a value right-hand side.
- Keep the existing type check and initialization-safety check. Passing the new predicate does not
  replace either one.
- Route this declaration error through surface elaboration as an author error at the original
  binding. Add it as the third documented exception to the rule that the Core checker refusing an
  elaborated module is the elaborator's fault. The Core checker remains authoritative.

No run-time, bytecode, linker, or backend change is required. Those components already implement
the evaluate-once global environment that makes the restriction necessary.

## Acceptance criteria

- A `nonrec` with a non-empty kind scheme and a `letrec`, `region`, `let`, or other non-value
  right-hand side is rejected by the Core declaration checker.
- A member of a top-level `rec` group is rejected under the same condition, independently of the
  other members' kind schemes.
- A binding with an empty kind scheme keeps accepting a pure non-value right-hand side.
- A kind-polymorphic lambda, type abstraction whose body is a value, record or variant of values,
  constructor-headed chain of values, and unsaturated foreign-headed chain of values is accepted.
- A kind-polymorphic binding whose body allocates only beneath a lambda is accepted; the allocation
  occurs after kind instantiation when the lambda is applied.
- A written surface signature that generalizes a kind but has a non-value body is reported as an
  author error at that binding, rather than as an elaborator defect.
- A kind-polymorphic defined-global alias is rejected when it remains a global reference. A
  function-typed alias that the elaborator eta-expands to a lambda remains accepted.
- The counterexample above is rejected before module initialization.
- Module initialization preserves well-formed `Γ_R` and `Γ_N` without putting a kind variable
  into a layout, a location type, or frame typing data.
- Existing declarations in the shipped `Base` and compiler-support modules continue to pass. This
  check includes searching for non-function kind-polymorphic aliases that remain global references.

## Clarify foreign conformance

The same specification review found one overbroad sentence in the conformance contract of
[Semantics](../technical-references/03-Typed-Core/06-Semantics.md). Condition (3) of `Σ ⊨ G` is
currently phrased over every saturated foreign-headed chain of values for which `cursorΣ` is
defined. The safety proof uses it only for a **well-typed** saturated chain, and only such a chain
guarantees that the values supplied to `δ_f` have the argument types selected by the cursor.

State condition (3) over well-typed saturated foreign-headed chains of values. Here **well-typed**
means a closed chain under well-formed run-time contexts `Γ_R` and `Γ_N`:

```text
·; · ⊢ M.f [[κ̄]] ᾱ : θ(σ) ! ()
```

where the judgement is read under `Γ_R` and `Γ_N`, the chain is saturated, and its cursor is
`cursorΣ(M.f [[κ̄]] ᾱ) = ⟨ σ ; θ ⟩`. The result promised by `δ_f` remains the instantiated cursor
result type, and the existing ABI-precondition premise remains in place. This change narrows an
implementation obligation to the calls a typed Stella program can make; it changes neither
declaration checking nor reduction.

## Specification files to update

- [Modules](../technical-references/06-Modules/01-Modules.md): add the kind value restriction to
  both declaration rules and explain its relation to the module fold.
- [Elaboration](../technical-references/02-Surface-Language/01-Elaboration.md): explain why inferred
  members already satisfy the restriction, specify the written-signature case, and classify the
  Core declaration error as an author error at the original binding.
- [Semantics](../technical-references/03-Typed-Core/06-Semantics.md): say that a kind-polymorphic
  initializer is installed as a value without stepping; state condition (3) over typed saturated
  foreign chains.
- [Core Type Checker](../technical-references/03-Typed-Core/07-Core-Type-Checker.md): include the
  declaration-level kind value restriction in the trusted checks.
- [Design Decisions](../technical-references/01-Introduction/03-Design-Decisions.md): record the
  evaluate-once kind value restriction as a lasting decision.
- [Implementation Plan](../technical-references/01-Introduction/04-Implementation-Plan.md): add the
  positive and negative declaration tests above.

## Design decision

Record the repair as **D52**, using the existing Decision / Rationale / Reversibility columns:

> **Decision:** A top-level definition generalized over kinds has a value right-hand side.
>
> **Rationale:** Module initialization evaluates a definition once, while a global's kind scheme
> is instantiated at every use. A non-value initializer could allocate a location or region whose
> type mentions an abstract kind variable and break the closed run-time context invariant.
> Requiring a value makes installation take no step under the abstract kinds; computation beneath
> the value begins only after instantiation. Definitions with an empty kind scheme retain ordered,
> evaluate-once initialization of arbitrary pure right-hand sides. The compatibility risk is low
> but non-zero: in particular, a non-function kind-polymorphic alias that remains a global reference
> is rejected, while a function alias eta-expanded to a lambda is accepted. Shipped modules are
> checked explicitly for this shape.
>
> **Reversibility:** low. Removing the restriction while preserving soundness would require
> kind-schemed run-time names or a different operational model such as kind-indexed global
> initialization, together with changes to linking, erasure, and the closed store/frame invariants.

## Implementation order

1. Add the Core declaration error and enforce the predicate for `nonrec` and `rec` bindings; route
   that error through surface elaboration to the original binding.
2. Add focused declaration-checker and surface-diagnostic tests, including the allocation
   counterexample, a written kind-polymorphic signature with a non-value body, a non-function
   global alias, and mixed-kind recursive groups.
3. Update the normative chapters and record D52.
4. Mirror the current `.github/workflows/ci.yaml` from a clean build, including its E2E fixture and
   integration steps, in addition to the compiler, CLI, Steam, Stellac, and backend test suites.
5. Re-run the F* development from an empty cache before proving module initialization safety.
