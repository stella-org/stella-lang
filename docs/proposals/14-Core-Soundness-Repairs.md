# Core Soundness Repairs Found by Mechanization

Status: Proposed

## Purpose

This document is the implementation brief for repairing the Typed Core specification and the
reference Core checker in response to the F* mechanization. The first proof-oriented review found
two direct holes in the upstream semantics:

1. the typing rule for an open region frame is not preserved by type substitution; and
2. the default branch of `switchKey` assigns a residual variant type that the value entering the
   branch does not have.

The mechanization had already exposed several related gaps before that review. They belong in the
same repair because they are prerequisites of the same preservation and progress proofs. This
document therefore gives one upstream work list rather than recording isolated local deviations in
the F* model.

The repairs below are normative decisions, not a menu of alternatives. Their common requirement is:

> A Core term accepted by the reference checker must remain typable after every reduction step,
> and every closed, pure accepted term must be a value, take a step, or fault in one of the ways the
> semantics specifies.

The local counterexamples have been checked against the F* definitions. Full preservation,
progress, effect safety, and initialization safety are later proof milestones; this proposal does
not claim those theorems before those milestones are complete.

## Scope and priority

The following items block the structural typing lemmas and must be completed before the
mechanization proceeds past typing.

| ID | Repair | Failure without it | Main upstream areas |
| --- | --- | --- | --- |
| S1 | Total canonical type equality for rows | Equality is not closed under substitution | Kinds and Types, Rows, `Row.purs`, `Equality.purs` |
| S2 | Well-formed, possibly inconsistent constraint assumptions | Preservation of type application fails | Kinds and Types, Rows, Typing Rules, `Context.purs`, `Entailment.purs`, `Kinding.purs`, `Check.purs` |
| S3 | One representation for global application chains | Progress fails under the value restriction | Terms, Semantics, Initialization, `Check.purs` |
| S4 | Closed typing data on open region frames | Preservation of type application fails | Semantics and run-time contexts |
| S5 | Sound residual typing for `switchKey` defaults | Preservation of `match` reduction fails | Typing Rules and Semantics |
| S6 | One explicit well-formedness contract for `Σ` | Constructor dispatch and canonical forms are unsound | Kinds and Types, Typing Rules, Semantics, `Signature.purs`, `Declare.purs`, `Prim.purs` |
| S7 | Complete typing and initialization rules for run-time forms | The statements of regularity, preservation, and initialization safety are not closed | Terms, Typing Rules, Semantics, Initialization |
| S8 | Join points scoped relative to the nearest non-tail position | Preservation of β-reduction and of the handler steps fails | Terms and Matching, Typing Rules, Semantics, Core Type Checker, `Check.purs` |

S4 and the value-retyping part of S5 are the two upstream semantic holes identified by the first
specification review. S1--S3 and S6--S7 collect the earlier findings of the mechanization and the
supporting repairs needed by those two holes. S8 was found while proving the substitution lemmas:
the tail-position condition on `jump` is not preserved by β-reduction.

## S1. Make type equality total while retaining set semantics for rows

### Problem

The specification defines the known part of a row normal form as a finite map from a key to a
payload. The function is consequently undefined on a row containing the same key twice. Kinding
normally rejects such a row, but type equality and substitution must also be meaningful in the
inconsistent contexts introduced by S2.

There is a smaller counterexample even before term typing is considered:

```text
r ⊎ r ≡ r
```

holds because the tail is a set. Substituting `( x : Int )` for `r` produces

```text
( x : Int ) ⊎ ( x : Int ) ≡ ( x : Int )
```

whose left-hand side has no finite-map normal form in the current definition. Equality is therefore
not unconditionally preserved by substitution.

Changing the tail to a multiset is not the repair. Rows remain keyed sets, and `r ⊎ r ≡ r` remains
an intended equality.

### Required change

Define a total canonical form for every type. A canonical row contains:

- a set of pairs `(key, canonical payload)`; and
- a set of canonical tails.

Union is set union followed by normalization. Equal `(key, payload)` pairs collapse; entries with
the same key and different payloads remain distinct. A row with no entries and one tail is
represented by that tail, so `a ⊎ ()`, `() ⊎ a`, and `a` have the same canonical form. A non-row type
encountered in a row position is an opaque tail: canonicalization is total and does not attempt to
kind the input.

Type equality is equality of these canonical forms and is independent of `Γ`. Kinding remains
responsible for sharpness. On a sharp row, the set of pairs is the graph of the finite map used by
the existing specification, so accepted programs in a consistent context keep their meaning.

Keep a partial `nfSharp`, or an equivalent checked projection to a finite map, for algorithms that
need unique lookup after kinding. Do not let that partial operation define type equality.

Rules currently written as `F(k) = τ` must account for canonical payloads. They should exhibit a
well-kinded type `τ` whose canonical form is the unique payload at `k`; sharpness makes that witness
unique up to type equality.

### Reference-checker work

- Replace the use of the partial finite-map normal form in
  `Stella.Compiler.TypedCore.Equality` with total canonicalization.
- Keep the finite-map projection in `Stella.Compiler.TypedCore.Row` only for callers that have
  established sharpness, and make that precondition visible in the API.
- Revisit entailment and residual-row code so neither silently treats a normalization failure as
  inequality.
- Keep tail union idempotent. No multiset representation is to be introduced.

### Acceptance criteria

- Canonicalization is defined for `( x : Int ) ⊎ ( x : Int )` and for two entries with the same key
  but different payloads.
- `τ1 ≡ τ2` implies `τ1[σ] ≡ τ2[σ]` without a kinding or consistency premise.
- Row union is idempotent, commutative, and associative under equality.
- Kinding still rejects a repeated key in every consistent context.
- Equality on sharp, well-kinded rows agrees with the current equality.

## S2. Permit inconsistent assumptions and confine ex falso to entailment

### Problem

The current specification and checker require `C` to be satisfiable before forming `Γ, C`.
Type application, however, checks only that its type argument has the quantified kind. It can
therefore substitute a row into a constraint abstraction and make that abstraction's assumption
unsatisfiable.

For example, the outer type application in a value of the following shape is permitted:

```text
( Λ (r : Row Type).
    Λ (_ : name ∉ r). v
) [ ( name : Int ) ]
```

It reduces to a constraint abstraction whose assumption is
`name ∉ ( name : Int )`. The current context-formation rule refuses that assumption, so the
reduct has no type. This is a preservation counterexample, not merely a failure of regularity.

### Required change

Adopt the following division of responsibility.

1. `C => τ` and `Λ (_ : C). v` require `Γ ⊢ C ok`; they do not require `C` to be
   satisfiable.
2. `e [•]` remains the only term rule that requires `Γ ⊨ C`.
3. Keep region-freshness **facts** separate from constraints introduced as **assumptions** by a
   constraint abstraction.
4. If the assumptions are inconsistent, `Γ ⊨ C` holds for every well-formed `C`.
5. Ex falso applies only to entailment. It must not make an unbound variable, an ill-kinded
   application such as `Int Int`, or a kind mismatch well formed. It can make a sharpness premise
   hold because those premises are entailment queries.

The present constraint language is negative: it has only Lacks and Disjoint. Inconsistency can
therefore be decided locally for each assumption after canonicalization:

```text
inconsistent(k ∉ ρ)       iff k ∈ knownKeys(ρ)
inconsistent(ρ1 # ρ2)     iff knownKeys(ρ1) ∩ knownKeys(ρ2) ≠ ∅
```

The empty assignment satisfies every remaining assumption, so no interaction between two
individually consistent negative assumptions creates a new contradiction. This characterization
must be revisited if a positive constraint is ever added.

`r # r` is not inconsistent. It is satisfiable by assigning `()` to `r`, and the existing
intentionally incomplete entailment relation need not derive all of its set-theoretic
consequences.

### Reference-checker work

- Change `Context.assume` so that a well-formed assumption is representable even when its known
  part is contradictory. A context may keep an inconsistency flag and decomposed facts; the exact
  representation is not normative.
- Do not use one `AtomicFacts` value for both region-freshness facts and constraint-abstraction
  assumptions unless the representation still preserves their different origins.
- Make `Entailment.entails` return true immediately for an inconsistent assumption context.
- In `Kinding`, `TConstrained` checks well-formedness, extends assumptions, and kinds its body; it
  no longer turns a contradiction into `EntailmentError`.
- In `Check`, both inference and checking of `ConstraintLam` follow the same rule. The
  `ConstraintApp` rule continues to call entailment.
- The elaborator may continue refusing or avoiding unsatisfiable abstractions. This repair widens
  the accepted Core language and need not widen the programs the elaborator emits.

### Required metatheory

- Entailment is preserved by every type renaming and substitution, without an admissibility
  premise. A substituted contradiction is handled by ex falso.
- Cut holds: if `Γ ⊨ C` and `Γ, C ⊢ J`, then `Γ ⊢ J`.
- If `Γ` is consistent and `Γ ⊨ C`, extending it with `C` remains consistent.
- Weakening preserves entailment.
- A region-name map preserves entailment when it is injective on the keys of the entailed
  constraint. In particular, opening with a name absent from the entailed constraint preserves it.

### Acceptance criteria

- The reduct in the counterexample above has the same type as the redex.
- `Γ, name ∉ (name : Int) ⊨ C` holds for every well-formed `C`.
- The same context still rejects `Int Int` and an unbound type variable.
- The checker still requires entailment at every `[ • ]`.

## S3. Use application chains as the sole representation of global spines

### Problem

The static value-form predicate admits a constructor-headed application chain such as

```text
Λ (a : Type). M.Cons [a] v1 v2
```

The dynamic value grammar instead admits a run-time spine `M.Ctor ς`, reached through
administrative formation steps. Evaluation contexts do not enter a `Λ`. The example is therefore
a legal static value form, but neither a dynamic value nor a reducible term. Progress fails.

The reference Core AST already represents the expression as a chain of `Global`, `TyApp`,
`ConstraintApp`, and `App`. Keeping a second run-time AST form in the specification creates the
mismatch without helping the implementation.

### Required change

Remove the run-time spine as a distinct expression form. A global application is always its source
application chain. A **spine view** may decompose the chain into:

- the global head and its kind arguments; and
- the type, constraint, and value arguments, in written order.

`cursorΣ` walks the declared scheme through that view. Saturation is decided from the unconsumed
**declared** type, before applying the accumulated substitution. An arrow introduced only by an
instantiation is not another argument position.

Classify chains as follows.

- A constructor-headed chain is a value when all its value arguments are values, whether or not
  the constructor is saturated.
- A foreign-headed chain is a value while it is unsaturated.
- A saturated foreign-headed chain whose value arguments are values is a redex.
- Once a declared chain is saturated, any further application is ordinary application of its
  result.

Add a typing rule for a constructor- or foreign-headed chain corresponding to the current
"Typing a spine" rule. Its cursor consumes only pure declared arrows, but its value arguments are
typed at the ambient row of the whole chain. This rule is necessary after eliminating the
run-time form: for example, `openEffC [ρ] (M.Just [Int] 1) → M.Just [Int] 1` must leave a term
typable at the widened ambient row.

Delete the spine-formation reduction steps. Update values, foreign reduction, erasure,
initialization safety, and every use of `values(ς)` to read the chain view instead.

Constructor arrows and every run-time-bearing arrow of a foreign remain pure; S6 makes those
conditions explicit properties of `Σ`.

### Reference-checker work

- Keep the existing `Expr` representation.
- Add a cursor-based chain path to typing rather than relying solely on the ordinary `App` rule,
  whose arrow row must equal the ambient row.
- Ensure global classification is unique as required by S6. A lookup must not choose constructors
  or foreigns by precedence.
- Keep the existing value-form treatment of constructor chains and make its relation to the
  dynamic value predicate explicit.

### Acceptance criteria

- Every static value form is a dynamic value.
- The `Λ` example above is a value and does not need evaluation beneath `Λ`.
- A saturated foreign is a redex; an unsaturated foreign and every constructor chain of values are
  values.
- The `foreign id : forall a. a -> a` example remains saturated after one value argument even when
  `a` is instantiated with a function type.
- `openEffC [ρ] v → v` preserves typing when `v` is a constructor chain.

## S4. Make open region frames closed under type substitution

### Problem

This is the first direct upstream hole found by the specification review.

The typing rule for `region⟨ℓ⟩ θ in e` permits its result type `β` and residual row `ρ` to depend on
the local type context. The escape premise checks that `ℓ` is not currently free in either. Type
substitution can subsequently introduce `ℓ` and invalidate the premise.

A representative shape is:

```text
( Λ (r : Row Effect).
    λ (u : Unit) / r. region⟨ℓ⟩ θ in Prim.Unit
) [ ( region ℓ ) ]
```

Before substitution, `ℓ ∉ frn(r)`. Afterwards the frame's residual row mentions `ℓ`, so the
current frame rule cannot type the reduct.

Operationally, a run-time frame can only be created after the surrounding type and constraint
abstractions have been instantiated: evaluation never enters those abstractions. Its type-level
data should therefore be closed with respect to the local type context.

### Required change

Define `closedCtx(Γ_R)` as the kinding context containing the run-time region names and layouts in
scope, but no local kind variables, type variables, term variables, or constraint assumptions.

For an open frame:

- require `β : Type` and `ρ : Row Effect` under `closedCtx(Γ_R)`;
- require the layout stored in `Γ_R(ℓ)` to be closed in the same sense;
- type each cell value against the corresponding layout type and require it to be a value;
- type the frame body with `Δ` empty;
- retain `ℓ ∉ frn(β) ∪ frn(ρ)`; and
- do not add `RegionKey ℓ ∉ t` facts for local row variables while typing an open frame.

Those facts are needed when checking the body of a **source** `region` under row variables bound
outside it. They are neither needed nor stable in a run-time frame, whose residual row is closed.
The source `region` rule keeps its current freshness facts.

Run-time contexts must preserve the same boundary:

- each `Γ_N` location type is kinded at `Type` with no local kind variable, type variable, or
  constraint in scope;
- a location type may mention names in `Γ_R`, because a `letrec` may be allocated inside an open
  region; and
- extending `Γ_R` or `Γ_N` never changes the layout or type of an existing entry.

### Acceptance criteria

- The open-frame typing rule is preserved by arbitrary well-kinded type substitution.
- Opening a well-typed source region produces a frame satisfying the closed rule.
- The counterexample above is rejected before a bad frame is formed or remains typable after
  substitution; it cannot produce an untypable reduct.
- `force` and `fill` continue to be typable under any local context because their location types are
  closed relative to that context.

## S5. Repair `switchKey` default refinement

### Problem

This is the second direct upstream hole found by the specification review.

Consider a value whose syntax is:

```text
inject y [ ( x : Int ) ] true
```

It has type `Variant ( y : Boolean | x : Int )`. A `switchKey` enumerating `x` enters its default
branch when the injected key is `y`, and the typing rule refines the occurrence to
`Variant ( y : Boolean )`. Reduction, however, places the original value in the branch environment;
its annotation still says that the rest contains `x`. With only the ordinary `inject` rule, that
value does not have the residual type. Preservation fails.

There is a second, mechanization-specific symptom of the same rule: computing a residual by deleting
keys from a canonical list is not stable under substitution when a formerly distinct entry becomes
equal to one being deleted.

### Required change: run-time variant values

Define the carried key and payload of a variant value by looking through `weaken` wrappers to the
underlying `inject`. Add an admissible run-time value typing rule:

```text
Γ;· ⊢ v : Variant r0 ! ()
carrier(v) = (k, w)       Γ;· ⊢ w : τ ! ()
Γ ⊢ r : Row Type          Γ ⊨ k ∉ r
────────────────────────────────────────────
Γ;Δ ⊢ v : Variant ( k : τ | r ) ! ρ
```

The row annotation on `inject` and the wrappers added by `weaken` carry no run-time content. The rule
therefore permits a run-time variant value to be typed at any well-kinded variant row that contains
the key and payload it actually carries. The first premise nevertheless requires the value to have
some ordinary variant typing before its row is changed. This checks every annotation that
`carrier` looks through; without it, an `inject` or `weaken` containing an unbound type variable or
an out-of-scope region could be typed merely from its carried key and payload.

The syntax-directed Core checker may continue to use the ordinary `inject` and `weaken` rules for
source terms. The new rule is required in the declarative run-time typing relation and when proving
that the values in a `match` environment agree with a refined occurrence context. This keeps the
checker's accepted source programs unchanged.

Do not change the reduction rule to rewrite type annotations, and do not remove default-branch
refinement.

### Required change: substitution-stable residuals

State residual computation by row decomposition, not by deletion from a chosen normal-form list.
If the branches enumerate `k_i` with payload types `τ_i`, require a residual `r'` such that

```text
Γ ⊢ r ≡ (( k_1 : τ_1 ) ⊎ ... ⊎ ( k_n : τ_n ) ⊎ r')
```

and use `Variant r'` for the default occurrence. The existing branch premises establish the
payload at each enumerated key, and kinding establishes sharpness. Because total canonical equality
and union commute with substitution, this formulation is stable under substitution.

The no-default rule remains: the row has no unknown tail and the branches exhaust its known keys.

### Acceptance criteria

- Reduction of the counterexample into the default branch preserves the occurrence typing.
- The rule also works when the injected value is underneath one or more `weaken` wrappers.
- An `inject` or `weaken` with an ill-scoped annotation cannot be retyped by the variant-value rule.
- Residual refinement is preserved by type substitution, including in an inconsistent context.
- The operational `switchKey` rules are unchanged.

## S6. Make `Σ wf` an explicit, checked contract

### Problem

Several typing and canonical-forms arguments currently rely on properties that declaration
construction happens to establish. The specification does not collect them into a premise, and a
`Signature` value can be assembled or imported without every consumer re-establishing them.

For example, if `T : Type -> Type` owns a constructor declared as

```text
C : forall (a : Type). a -> T Int
```

then construction and `switchCtor` disagree about which type argument instantiates the field. A
branch may type the field at one type while the value carries another. Preservation fails.

### Required change

Define one predicate `sig_wf(Σ)` and make it a premise of kinding, typing, global conformance, and
the safety statements. Validate imported/interface signatures against it rather than trusting that
they arose through the local declaration builder.

`sig_wf` must include at least the following.

#### Names and lookup

- A global name belongs to at most one of constructors, foreigns, and top-level values.
- Lookup of a global scheme is defined only when exactly one table classifies the name. It must not
  use table precedence to resolve a collision.
- Operation names are unique within an effect.

#### Type constructors and effects

- Every type-constructor kind scheme is well formed, closed under its own kind variables, and
  produces `Type`.
- Every effect parameter has a quantifiable kind.
- Every operation signature is well kinded under the effect parameters and its own type binders.

#### Data constructors

- A constructor's owner is a data type, and a data type's constructor list agrees exactly with the
  constructors whose owner names it.
- The constructor has the same kind variables as its owner.
- If the owner's parameters are `(a_i : κ_i)`, the constructor scheme has exactly the shape

  ```text
  forall k̄. forall (ā : κ̄). τ1 -> ... -> τn -> T [[k̄]] ā
  ```

  with pure arrows.
- The stored field list and arity agree with `τ1 ... τn`.
- Tags are pairwise distinct among constructors of one owner.

The condition formerly called `ctor_params_ok` is part of `sig_wf`, not an optional premise at the
few sites that happened to need it first.

#### Foreigns

- Every foreign scheme is well kinded.
- Every arrow in a run-time-bearing position is pure, as required by D23. This includes arrows
  nested in arguments and row payloads; constraints themselves carry no run-time value and retain
  the existing exception.
- The last declared argument position of a foreign is a value argument: no `forall` and no `=>`
  stands on its spine after its last arrow, nor anywhere on it where it has no arrow. Erasure keeps
  a chain's value arguments alone, so a foreign saturated by a type or constraint argument would be
  called at another point once erased: with `foreign make : forall a. a`, the typed
  `let x : forall a. a = M.make in 0` never calls `δ_make`, while its erasure
  `let x = M.make in 0` does, and faults where `δ_make` faults. A β-step builds such a chain from a
  well-typed term, `(λ g. g v) (M.f [τ])` among them, so no restriction on where a chain is written
  prevents it; the declaration is where it is ruled out, both where a foreign is declared and where
  an imported signature is assembled.

#### `Prim`

Define `prim_wf(Σ)` and use `sig_ok(Σ) = sig_wf(Σ) ∧ prim_wf(Σ)` for the Core metatheory.
It must fix the names, kinds, and canonical-value classes that the rules inspect:

- `Function : Type -> Row Effect -> Type -> Type`, class function;
- `Record, Variant : Row Type -> Type`, their respective classes;
- `Int`, `Number`, `String`, `Char`, and `Boolean : Type`, class literal;
- `IO : Type -> Type`, class opaque; and
- `Unit : Type`, a data type whose only constructor is `Prim.Unit`, with no field and tag 0.

No other type constructor may claim the function, record, or variant canonical class.

### Reference-checker work

Most locally declared constructor-shape, tag, foreign-purity, and namespace checks already exist in
`Stella.Compiler.TypedCore.Declare`. Retain them. The new work is to centralize the invariant,
validate imported `Signature` fragments, remove precedence-based lookup, and add direct regression
tests for malformed signatures.

### Acceptance criteria

- No `sig_ok` signature admits the malformed `C` example above.
- Constructor field types obtained by dispatch are well kinded after instantiation at the
  scrutinee's kind and type arguments.
- A signature collision cannot be hidden by lookup order.
- `cursorΣ` may rely on constructor and foreign arrows being pure.
- No `sig_ok` signature holds a foreign whose type takes a type or a constraint after its last
  value, so a chain is saturated exactly when it holds as many value arguments as its arity.
- A realistic signature containing polymorphic data such as `List` satisfies `sig_ok`.

## S7. Close the remaining run-time and regularity gaps

These items are individually smaller, but omitting one leaves a later theorem undefined or forces a
hidden premise into its proof.

### Type every run-time form

Add a typing rule for `match θ dt`. The derivation carries an occurrence context `Ω`, requires the
value reached by following each occurrence from `θ` to have the type recorded in `Ω`, and types `dt`
under that `Ω`. S5's run-time variant rule is used when a `switchKey` has refined an occurrence.

For the other forms:

- `openEffC [ρ] e` explicitly kinds `ρ` at `Row Effect`, and checks `e` with `Δ` empty: the
  computation it widens is an application of values, `(openEff [ρ] v) w` being the one step that
  makes it, so it needs no outer join point, and a jump out of it would land at a row other than
  its own and find no tail context through the coercion;
- `force ν` and `fill ν e` rely on a well-formed `Γ_N`; `fill` checks `e` with `Δ` empty and out
  of tail position;
- an open region frame follows S4;
- `opaque ω [τ]` remains restricted to a type constructor of canonical class opaque; and
- every cell stored in an open region frame is a value.

### Read payloads through substitution-stable premises

S5 restates the `switchKey` residual by decomposition. The other rules reading a row at a key must
follow, since a rule premised on `nf(ρ)` or `F(k)` holds of a row only as it is written: under
an inconsistent assumption a substitution can bring a second element at a key into a tail, and the
row is then left with no sharp normal form, while equality, entailment, and kinding are preserved by
every substitution.

- `perform k.op [σ̄] e` asks `Γ ⊢ ρ ≡ ( ent | ρ' )` with `key(ent) = k` and
  `payload(ent) = E τ̄`, and `Γ ⊢ ( ent | ρ' ) : Row Effect`, in place of `F(k) = E τ̄` on
  `nf(ρ)`. Under `cache ∉ ( cache : State Int )`, a `perform cache.get` at
  `( cache : State Int | e )` with `( cache : State String )` substituted for `e` has no normal form
  to read, and has the decomposition still.
- A record occurrence `o . k` asks `Γ ⊢ r ≡ ( k : τ | r' )` and
  `Γ ⊢ ( k : τ | r' ) : Row Type`, in place of `F(k) = τ`. The occurrence judgement therefore
  carries `Γ`, written `Γ;Ω ⊢ o : τ`. The kinding premise also keeps `Ω` well formed, kinding the
  `τ` a `bind` puts into `Γ`.
- `readCell ℓ.k` and `writeCell ℓ.k e` ask `RegionKey ℓ ∈ keys(ρ)` in place of
  `RegionKey ℓ ∈ dom(nf(ρ))`. They need no payload, an element keyed `RegionKey ℓ` being
  `region ℓ` alone, but `nf(ρ)` is partial in the whole row: a conflict at another key makes it
  undefined. `keys(ρ)` is defined on every row, and a substitution only adds to it.

A checker may still read these off the sharp normal form; it is then incomplete on rows that only
an inconsistent context kinds, and reports them.

### Make run-time contexts well formed

State and use:

- `rctx_ok(Γ_R)`: each layout is closed except for earlier run-time region names;
- `lctx_ok(Γ_R, Γ_N)`: each location type has kind `Type` with no local kind/type/constraint
  dependency, but may mention `Γ_R`; and
- store typing under those contexts.

Opening a region and allocating a recursive group extend these contexts with fresh keys and preserve
all existing entries.

### Make regularity premises explicit

Every typing derivation must imply that its result type has kind `Type` and its ambient row has kind
`Row Effect`. Add the missing premises rather than relying on an induction hypothesis that an empty
list or empty branch set does not provide. In particular:

- kind the annotation of `let`;
- kind the answer type of `handle`;
- kind annotations introduced by run-time forms;
- require well-formed result types and rows in empty auxiliary-list judgements; and
- require the target type and target row of conversion to be well kinded.

Conversion should permit both components to change by equality:

```text
Γ;Δ ⊢ e : τ1 ! ρ1    Γ ⊢ τ1 ≡ τ2    Γ ⊢ ρ1 ≡ ρ2
Γ ⊢ τ2 : Type        Γ ⊢ ρ2 : Row Effect
───────────────────────────────────────────────────────────────────────────
Γ;Δ ⊢ e : τ2 ! ρ2
```

This is equality conversion, not effect-row subtyping.

### Give `fail` an explicit result type

The decision-tree grammar currently writes `fail` while its expansion needs `τ` in
`Partial.abort [τ]`. Prefer the representation already used by the checker: no `fail` AST node,
and derived notation `fail τ` expanding to

```text
leaf (perform Partial.abort [τ] Prim.Unit)
```

If a node is retained in the prose grammar, it must be `fail τ`, not an unannotated `fail`.

### Define the erased reduction relation

The erasure theorem currently refers to `→ᵤ` without defining it. Define the relation on erased
terms and stores before stating the simulation theorem. State which typed administrative steps map
to zero erased steps and which computational steps map to one.

### Extend initialization safety to run-time forms

Reduction can put `force ν` into an initializer of a nested `letrec`, so the `imm`/`lat` judgement
must be defined on every run-time form:

- `match θ dt` follows the `case` rule, with `θ` as its scrutinees;
- `openEffC [ρ] e` passes `imm` and `lat` through;
- `force ν` and `opaque ω [τ]` read no member of the group currently being judged;
- `fill ν e` uses the default promoting rule, like `writeCell`; and
- `region⟨ℓ⟩ θ in e` counts everything it contains, like a source `region`.

After S3, constructor and foreign chains are classified through the chain view rather than a
run-time spine node. A chain with no more value arguments than its declared arity builds a value;
an application beyond that arity is an ordinary application of the saturated prefix.

### Acceptance criteria

- Every reduct produced by the semantics has a typing rule and an initialization-safety rule.
- Typing regularity is provable without assuming it separately for empty helper judgements.
- Every use of `→ᵤ` refers to a defined relation.
- The initialization judgement remains defined after `letrec` allocation substitutes `force`
  forms into nested initializers.
- No typing rule reads a row through `nf` or `F(k)`: `perform`, record occurrences, and
  `switchKey` read it through a decomposition, and `readCell` and `writeCell` through `keys(ρ)`,
  so each is preserved by every type substitution, an inconsistent assumption included.
- A `perform` and a record occurrence over a row collapsed under an inconsistent assumption are
  typed; one with two payloads at the key is typed by the rules and reported by a checker reading
  the sharp normal form.
- `openEffC [ρ] e` types `e` under no join point, so no jump leaves a widened computation.
- Each typed step is zero or one step of `→ᵤ`, a foreign being called at the same point in both,
  and a step applying a `Λ` or moving or discharging a coercion being the zero-step case.

## S8. Scope join points relative to the nearest non-tail position

### Problem

The rules for `letjoin` and `jump` carry the join point context `Δ` unchanged into every subterm
except at the boundaries of [Terms and Matching](../technical-references/03-Typed-Core/04-Terms-and-Matching.md#join-points):
the bodies of `λ` and `Λ`, `handle`, the body of a `region`, and, after S7, `letrec` initializers,
`fill`, and `openEffC`. Beside that, they impose a separate side condition: a `jump` must be "in
tail position". This has three defects.

1. **Tail position is not defined.** The phrase occurs:
   - in the premise of `jump`;
   - on the definition of a `letjoin` ("the root of e1 is in tail position", wherever the
     `letjoin` stands);
   - on `letrec` initializers and the operand of `fill` ("out of tail position").

   No judgement says which positions are tail positions. The reference checker realizes the notion
   as a flag in its environment:
   - the flag is set at the root of a declaration, at an abstraction, and at the root of a join
     definition;
   - it is cleared at every non-tail child (`notTail`);
   - it is inherited everywhere else.

   Below a non-tail position, the flag is set again only at the root of a join definition. `Δ`,
   meanwhile, is kept.

2. **The tail condition is not preserved by reduction.** Whether a position counts as a tail
   position depends on everything above it, up to the nearest boundary. Reduction, however, moves a
   term checked at a boundary into the position of the redex. β-reduction does exactly this. The
   term

   ```text
   let y : Int = (λ (u : Unit) / (). letjoin j () : Int = 1 in jump j ()) Prim.Unit in y
   ```

   is accepted: the body of the `λ` is in tail position, so are the continuation of the `letjoin`
   and the `jump`. One step gives

   ```text
   let y : Int = (letjoin j () : Int = 1 in jump j ()) in y
   ```

   Here the `letjoin` stands on the bound side of a `let`. Its continuation inherits the non-tail
   position, and the checker reports `JumpNotInTail j`.

   The reduct is a correct program. It takes the join step of
   [Semantics](../technical-references/03-Typed-Core/06-Semantics.md) with `Tl = []`, then
   `letjoin j () : Int = 1 in 1 → 1`. Preservation fails. It fails the same way at every step that
   puts a body checked at a boundary where the redex stood, since the redex may stand in a non-tail
   position: the return clause and the operation clauses of a `handle` are the other instances.

3. **The rules accept jumps that no reduction can perform.** The root of a join definition is a
   tail position wherever the `letjoin` stands, and `Δ` passes through non-tail positions. So the
   definition of a `letjoin` that stands in a non-tail position may jump to a join point bound
   outside that position:

   ```text
   letjoin k () : Int = 0 in f (letjoin j () : Int = jump k () in 1)
   ```

   If `j` were entered, `jump k ()` would stand under `f (…)`, which is no `Tl`, and no join rule
   would apply. The term is not stuck only because nothing can enter `j`. A jump to `j` would have
   to come from its continuation, which inherits the non-tail position, or from the definition of
   `j` itself, which must first be entered. Progress then rests on this unreachability argument
   rather than on the typing of the jump.

The F* mechanization first modelled the specification with an explicit tail flag. It found the
counterexample of item 2 there and then adopted the change below. In the revised development the
contractum of every β-redex is typed at the `Δ` of the redex.

### Required change

Adopt a relative join point discipline inspired by System F_J (Maurer, Downen, Ariola, and Peyton
Jones, “Compiling without Continuations”, PLDI 2017): `Δ` is relative to the nearest non-tail
position or boundary, and `jump` has no positional side condition.

The discipline is a more direct and conservative variant of the one of F_J, not that one as it
stands. F_J is a call-by-name language in which a jump may discard the evaluation context around
it, so it keeps `Δ` in some positions that are not tail positions: the function of an application
keeps `Δ`, and only the argument is checked under an empty `Δ`. In Stella a jump discards no
context and transfers within a `Tl` of its `letjoin`, as the call-by-value semantics has it, so
every non-tail premise is checked under `Δ := ·`.

- **`jump j (ē)` requires only `( j : (τ̄) -> τ ! ρ ) ∈ Δ`.** Its arguments are checked under
  `Δ := ·`.
- **A non-tail position is checked under `Δ := ·`.** The non-tail positions are:
  - both sides of an application, and the value arguments of a chain;
  - the operands of `e [τ]`, `e [•]`, and `openEff [ρ] e`;
  - the bound side of `let`, the scrutinees of `case`, and the values `θ` of `match`;
  - the condition of a guard, and the arguments of `jump`;
  - every subterm of a record or variant operation (`extend`, `select`, `restrict`, `update`,
    `merge`, `inject`, `weaken`, `absurd`);
  - the argument of `perform`, the value of `writeCell`, and the initial values of `region`.
- **`letjoin j (x̄ : τ̄) : τ = e1 in e2` adds `j` to the `Δ` it is given.** It checks `e1` under
  `Γ, x̄ : τ̄; Δ, j` and `e2` under `Γ; Δ, j`.
- **A tail-transparent position inherits `Δ`.** These positions are:
  - the body of `let` and of `letrec`;
  - the continuation of `letjoin`;
  - the tree of `case` and of `match`;
  - the branches and leaves of a decision tree.
- **A boundary keeps `Δ := ·`, as now.** The boundaries are:
  - the bodies of `λ`, `Λ (a : κ)`, and `Λ (_ : C)`;
  - the handled computation and every clause of `handle`;
  - the body of `region`;
  - the body and the cells of an open frame `region⟨ℓ⟩`;
  - `letrec` initializers;
  - the operands of `fill` and `openEffC`.

The two join point rules become:

```text
  Γ ⊢ τ : Type    Γ ⊢ τ̄ : Type    Γ ⊢ ρ : Row Effect
  Γ, x̄ : τ̄; Δ, j : (τ̄) -> τ ! ρ ⊢ e1 : τ ! ρ
  Γ;      Δ, j : (τ̄) -> τ ! ρ ⊢ e2 : τ ! ρ
  ───────────────────────────────────────────────────
  Γ;Δ ⊢ letjoin j (x̄ : τ̄) : τ = e1 in e2 : τ ! ρ

  ( j : (τ̄) -> τ ! ρ ) ∈ Δ    each i: Γ;· ⊢ e_i : τ_i ! ρ
  ─────────────────────────────────────────────────────
  Γ;Δ ⊢ jump j (ē) : τ ! ρ
```

Every other rule writes `·` for the `Δ` of its non-tail premises. For example:

```text
  Γ;· ⊢ e1 : τ1 -{ρ}-> τ2 ! ρ    Γ;· ⊢ e2 : τ1 ! ρ
  ──────────────────────────────────────────────
  Γ;Δ ⊢ e1 e2 : τ2 ! ρ
```

"Tail position" stops being a premise.
- Remove "jump is in tail position" and "the root of e1 is in tail position" from the rules.
- Remove "out of tail position" from the `letrec`, `fill`, and S7 `openEffC` prose. `Δ := ·`
  already says what those phrases meant.
- Where the prose still needs the notion, define it: a position is a tail position of
  `letjoin j` when `j` is in its `Δ`.

The semantics is unchanged: `Tl` and both join rules stay as they are. Under the new rules, the
`jump j` in the hole of an evaluation context stands in a `Tl` under the `letjoin` of `j`, because:
- every position an evaluation context passes through, other than the continuation of a `letjoin`,
  is a non-tail position or a boundary, and both of those empty `Δ`;
- the tail-transparent forms above a `jump` reduce away before the `jump` is in the hole.

This is the argument that the [Semantics](../technical-references/03-Typed-Core/06-Semantics.md)
chapter gives for "the same function activation", and it now follows from the typing rule alone.

### What the change accepts and rejects

- **Newly accepted:** a join point bound in a non-tail position, jumped to from its continuation
  and from the tail-transparent positions below it, as in the reduct of item 2 or in
  `f (letjoin j (n : Int) : Int = n in jump j 1)`. A `case` with shared alternatives in argument
  position takes this shape when its join point is bound around it rather than around the whole
  application.
- **Newly rejected:** a jump that leaves a non-tail position outward, as in item 3. Every such jump
  is unreachable under the current rules. No program that the current rules accept, and that can
  execute a jump, is rejected.
- **Unchanged:** a jump out of `λ`, `Λ`, `handle`, `region`, a `letrec` initializer, `fill`, or
  `openEffC` stays rejected. A join definition that jumps to itself stays accepted wherever its
  `letjoin` stands.

### Reference-checker work

**`Check.purs`.**
- Drop the `tail` field of `Env`.
- Make `notTail` empty `joins`.
- Let `checkJoinBody` extend the `joins` it is given, with no reset of a flag.
- Let a `jump` check membership only.

Keep `JumpNotInTail` as the diagnostic for a jump whose join point is bound but hidden by a
non-tail position. One way is to record the hidden join points beside `joins` in `notTail`.
Every join point boundary then clears both the active and the hidden join points, so that a jump
across a boundary is never reported as `JumpNotInTail`. `UnboundJoin` remains the diagnostic
for a name that no enclosing `letjoin` binds, and for one hidden by a boundary, as now.

**Mid IR translation.** It already lowers a `LetJoin` in argument position through the join point
case of `atomize` (`viaJoin` in `MiddleEnd/Translate.purs`), which delivers both the definition and
the continuation to the bound continuation. It needs no change, but a test should cover a join
point jumped to from its continuation in argument position.

**Kernel builder.** It defers the position of a jump to the Core type checker, and may keep doing
so. Its documentation should no longer say that only an abstraction empties `Δ`.

### Acceptance criteria

- Both terms of item 2 are accepted. More generally, each of these steps preserves typing at the
  `Δ` of the redex: β-reduction, the `handle` steps, the join steps, and every step that moves a
  term out of a tail-transparent form.
- The term of item 3 is rejected with `JumpNotInTail k`.
- `letjoin j () : Int = 1 in f (jump j ())` is still rejected with `JumpNotInTail j`.
- `f (letjoin j (n : Int) : Int = n in jump j 1)` is accepted.
- The existing test "puts the root of a definition in tail position wherever the letjoin stands"
  still passes. Its description becomes "types a join definition under the join points of its own
  `letjoin`".
- Jumps out of every join point boundary of the Required change are still rejected: `λ`,
  `Λ (a : κ)`, `Λ (_ : C)`, `handle`, `region`, an open frame `region⟨ℓ⟩`, `letrec`
  initializers, `fill`, and `openEffC`.
- No typing rule has "tail position" as a premise. Every non-tail position that the Required change
  lists is checked under `Δ := ·`.
- In a well-typed term, every `jump j` in the hole of an evaluation context stands in a `Tl` under
  the `letjoin` of `j`.

### Design decision

Record the discipline as a design decision (D50), as it fixes what a join point is:

> **Join points are scoped relative to the nearest non-tail position.** A non-tail position and a
> join point boundary both start with no join point in scope. The join point boundaries are the
> bodies of `λ` and `Λ`, `handle`, the body of `region`, an open frame `region⟨ℓ⟩`, `letrec`
> initializers, `fill`, and `openEffC`. `letjoin` adds its join point for its
> definition and its continuation, and the other forms pass `Δ` to their tail-transparent
> children. `jump` requires only that its join point is in scope. *Reason:* a positional tail
> condition beside a `Δ` that crosses non-tail positions is not preserved by β-reduction, which
> moves a function body into the position of the call. Relative scoping, inspired by System F_J and
> emptying `Δ` at every non-tail premise, is stable under every reduction, and it makes "the
> `jump` lies in a `Tl` of its `letjoin`" a consequence of typing. *Reversibility:* low. The treatment of `Δ` reaches every typing rule, the
> checker, the structural lemmas, and what lowering assumes of a jump. *Compatibility risk:* low.
> The change newly rejects only jumps that cannot execute, and the forms it newly accepts are
> lowered by `viaJoin` as they stand.

## Specification files to update

The repair should update the following chapters as one coherent change.

- [Kinds and Types](../technical-references/03-Typed-Core/01-Kinds-and-Types.md): total canonical
  equality, constraint formation, and the `Σ wf` premise.
- [Rows](../technical-references/03-Typed-Core/02-Rows.md): total canonical rows, inconsistency, and
  ex-falso entailment.
- [Terms and Matching](../technical-references/03-Typed-Core/04-Terms-and-Matching.md): chain-only
  values, typed `fail` notation, and the relative join point discipline of S8 (the initial
  values of a `region` no longer keep `Δ`).
- [Typing Rules](../technical-references/03-Typed-Core/05-Typing-Rules.md): constraint abstraction,
  chain typing, substitution-stable `switchKey` residuals, conversion, regularity premises, and the
  S8 rules for `letjoin`, `jump`, and the non-tail premises of every rule.
- [Semantics](../technical-references/03-Typed-Core/06-Semantics.md): run-time value typing, closed
  region frames, `match`, chain reduction, run-time contexts, erased reduction, and the S8 typing of
  `openEffC` and `fill` without a tail condition.
- [Core Type Checker](../technical-references/03-Typed-Core/07-Core-Type-Checker.md): item 8 states
  the S8 discipline in place of "`jump` occurs in tail position".
- [Initialization Safety](../technical-references/03-Typed-Core/10-Initialization.md): rules for all
  run-time forms and the chain view.
- [Design Decisions](../technical-references/01-Introduction/03-Design-Decisions.md): retain D4's
  sharp set semantics while separating total equality from sharp finite-map lookup; record the
  chain-only operational representation if it is intended as a lasting design decision; record S8
  as a new decision.
- [Implementation Plan](../technical-references/01-Introduction/04-Implementation-Plan.md): the test
  rows on join points follow S8.

The corresponding reference-checker implementation is concentrated in:

```text
compiler/src/Stella/Compiler/TypedCore/Row.purs
compiler/src/Stella/Compiler/TypedCore/Equality.purs
compiler/src/Stella/Compiler/TypedCore/Entailment.purs
compiler/src/Stella/Compiler/TypedCore/Context.purs
compiler/src/Stella/Compiler/TypedCore/Kinding.purs
compiler/src/Stella/Compiler/TypedCore/Check.purs
compiler/src/Stella/Compiler/TypedCore/Signature.purs
compiler/src/Stella/Compiler/TypedCore/Declare.purs
compiler/src/Stella/Compiler/TypedCore/Prim.purs
compiler/src/Stella/Compiler/TypedCore/Initialization.purs
```

Not every semantic run-time form has a reference-checker AST constructor. Those repairs still
belong in the normative semantics and in the F* model; they must not be omitted merely because the
compiler lowers before representing the form directly.

## Implementation order

1. Implement S1 and S2 together. Entailment, kinding, and equality must agree about rows in an
   inconsistent context.
2. Implement and expose `sig_ok` from S6. Make all subsequent rules and tests use it.
3. Apply S3 to the syntax, typing, value predicate, reduction, erasure, and initialization
   judgement as one change.
4. Apply S4 and S5 to run-time typing and decision-tree typing.
5. Complete the run-time and regularity work in S7.
6. Apply S8 to the join point rules, the non-tail premises of every rule, and the checker.
7. Add the counterexamples above as negative-before/positive-after regression tests, plus malformed
   signature tests.
8. Re-run the F* typing development from an empty cache before beginning renaming, weakening, and
   substitution for the revised typing relation.

## Changes that belong only to the F* development

The following choices are proof representation or proof engineering and are not upstream language
changes:

- de Bruijn indices, locally nameless region binders, and parallel renaming/substitution;
- sorted-list implementations of finite sets;
- the exact cofinite-quantification encoding used for the source `region` rule;
- the split between `.fst` and `.fsti`, solver patterns, fuel, and cache settings; and
- the representation of diagnostic witnesses in the initialization judgement.

Conversely, S1--S7 are not to be hidden as formalization conveniences. They change or complete the
normative Core contract, and the specification, reference checker where applicable, and
mechanization must converge on the same decisions.
