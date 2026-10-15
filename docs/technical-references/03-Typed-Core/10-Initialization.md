# Initialization Safety

**A recursive group is initialized in the order its members are written**, and a member's
right-hand side may read only the members written before it. Which members a right-hand side
reads is judged statically, as an abstract interpretation of Core, so that a program the checker
accepts never reads a member that is not yet initialized, and no run-time check is relied on for
it. The judgement is D14, for a top-level `rec` group ([Modules](../06-Modules/01-Modules.md))
and a local `letrec` ([Typing Rules](05-Typing-Rules.md)) alike; a local group's members that are
no function values are by-need cells, filled in the order written ([Semantics](06-Semantics.md)).

A function value reads nothing when it is initialized, so every group of function values is
initialization-safe. What the judgement admits beside them is a member that is no function and
reads the group only where nothing runs it during initialization: a recursive function stored in
data, a record of closures referring to one another, a dictionary holding another.

## What an initializer reads

The judgement is an abstract interpretation of each right-hand side. For an expression `e` it
gives two maps from members to non-empty sets of **witnesses**:

- **`imm(e)`**, what evaluating `e` reads before it has a value;
- **`lat(e)`**, what the value of `e` may read later: what a closure it holds reads when applied,
  and what that closure's own value may read in turn.

**A witness `⟨r, p⟩` is where a read is seen**: `r` is the occurrence of the member's name that
is read, and `p` is **the form that made the read immediate** — an application, a `perform`, a
`writeCell`, a handling expression, or a region, the forms that promote below — or nothing where
the occurrence is read as it stands. Maps are combined pointwise by union, `∅` holding nothing;
`promote_p(m)` is `m` with the second part of every witness replaced by `p`, so a read is located
at the outermost form that brought it into the initializer's evaluation.

**The judgement is taken for one group `R`**, and its maps hold the members of `R` alone. Every
other variable is a local: a member of a group nested in `R`'s right-hand sides, and one of a
group `R` itself stands in, among them. A variable bound outside `R`'s right-hand sides is at
`ρ = ∅`, its value having been built where no member of `R` is in scope. Each recursive group is
judged by its own `R`, in its own order, the nested ones included. The judgement for `R` is taken
under:

- **`lat*(x)`** for each member `x` of `R`, `lat` of its right-hand side;
- **`ρ(y)`** for each local `y`, what the value bound to `y` may read later;
- for each join point `j`, **`arg_j`**, its parameters' `ρ`, the union over every `jump` to `j` of
  what each argument may read later, and **`imm_j`** and **`lat_j`**, those of its body under
  `arg_j`.

Witnesses are drawn from the occurrences and the promoting forms of the module, which are finite,
and every rule below is monotone in the maps. The summaries are **the least fixed point** of the
rules, taken together over a group; being a fixed point of sets, it is the same whatever order it
is computed in.

**The default rule** is that of the three forms the tables below leave out: an application that
is no constructor's or foreign's spine, a `perform`, and a `writeCell`. Each of their immediate
subexpressions `s̄` is evaluated, and the form may apply anything one of them holds, or, for a
`writeCell`, store it where it is read back and applied:

```text
imm = ⋃ₖ ( imm(sₖ) ∪ promote_this(lat(sₖ)) )        lat = ⋃ₖ lat(sₖ)
```

`this` is the form itself. That is the rule for an application `e₁ e₂`, a `perform`, and a
`writeCell`: **an application promotes** — what the callee and the argument may read later becomes
read now, since the callee may apply any closure it reaches. One rule covers `(\_ -> x) ()`, a
closure passed to a function that applies it, a member function called during initialization
whose body reads another member, and a closure taken out of a member's value and applied —
`b = (select next a) Prim.Unit`, which no syntactic condition sees.

The forms with a rule of their own are the variables, the binders, the forms that build or take
apart a value without running what it holds, and the control forms:

| Form | `imm` | `lat` |
| --- | --- | --- |
| `x`, a member | `{ x ↦ ⟨x, –⟩ }` | `lat*(x)` |
| `y`, a local | `∅` | `ρ(y)` |
| `M.x [[κ̄]]`, `c`, `recordEmpty`, `readCell ℓ.k` | `∅` | `∅` |
| `λ(y : τ) / r. e` | `∅` | `imm(e) ∪ lat(e)`, with `ρ(y) = ∅` |
| `Λ (a : κ). e`, `e [σ]`, `Λ (_ : C). e`, `e [•]`, `openEff [ρ] e` | `imm(e)` | `lat(e)` |
| `M.c ē`, a spine whose head is a data constructor or a foreign, through type and constraint applications, with no more arguments than its arity | `⋃ imm(eₖ)` | `⋃ lat(eₖ)` |
| `extend k e₁ e₂`, `update k e₁ e₂`, `merge e₁ e₂`, `inject k [ρ] e` | `⋃ imm(eₖ)` | `⋃ lat(eₖ)` |
| `select k e`, `restrict k e`, `weaken k [τ] e`, `absurd [τ] e` | `imm(e)` | `lat(e)` |
| `let y : τ = e₁ in e₂` | `imm(e₁) ∪ imm(e₂)`, with `ρ(y) = lat(e₁)` | `lat(e₂)` |
| `letrec { ȳ : σ̄ = ē' } in e`, a group nested in `R` | `⋃ imm(e'ₖ) ∪ imm(e)`, each `yₖ` a local at `ρ(yₖ) = lat(e'ₖ)`, the least fixed point over the nested group | `lat(e)` |
| `case (ē) of dt` | `⋃ imm(eₖ) ∪ imm(dt)` | `lat(dt)` |
| `letjoin j (ȳ : τ̄) : τ = e₁ in e₂` | `imm(e₂)` | `lat(e₂)` |
| `jump j (ē)` | `⋃ imm(eₖ) ∪ imm_j` | `lat_j` |
| `handle e with h`, `region [ℓ] (k̄ : σ̄) @ (ē) in e` | `⋃ₖ imm(partₖ) ∪ promote_this(⋃ₛ ( imm(s) ∪ lat(s) ))` | `⋃ₛ lat(s)` |

A decision tree is judged under the scrutinees, each occurrence reading what the scrutinee it
starts from may read later:

| Tree | `imm` | `lat` |
| --- | --- | --- |
| `leaf e` | `imm(e)` | `lat(e)` |
| `bind y o dt` | `imm(dt)`, with `ρ(y)` the `lat` of the scrutinee `o` starts from | `lat(dt)` |
| `switchCtor o`, `switchLit o`, `switchKey o`, their branches and default | `⋃ imm(dtₖ)` | `⋃ lat(dtₖ)` |
| `guard e dt₁ dt₂` | `imm(e) ∪ imm(dt₁) ∪ imm(dt₂)` | `lat(dt₁) ∪ lat(dt₂)` |

**A constructor, a record, a variant, and a saturated `foreign` do not promote.** A constructor
builds a value without running anything it is given, and a selection, a restriction, or a match
takes one apart: a variable a pattern binds may hold any part of the scrutinee, so it may read
later what the scrutinee may, and a closure extracted and applied is then an application of it,
which promotes. A `δ_f` may carry a function value but may not apply one ([Semantics](06-Semantics.md)),
so `Base.IO.bind` storing `a -> IO b` in the value it builds reads nothing; what applies it is the
runtime executing that value, which an initializer, at row `()`, never does.

**A join point is read where it is jumped to**, not where it is defined: its body runs at each
`jump`, under what that jump and every other hands its parameters, and a join point jumping to
itself is part of the same fixed point.

**A handling expression and a region count everything they hold as read through them**, every
subexpression `s` at any depth, each binder of a clause or a cell at `∅`: what is performed,
handled, resumed, stored in a cell, or read back from one flows through them without a rule to
follow it, and what any part may read later is read now. What a part — the handled computation,
a clause, the region's body or an initial value — reads as it stands is kept as it is, so a read
the source makes directly is located at its reference alone, and every other read inside is
promoted by the form itself: `region … in x` reads `x` where `x` stands, and a closure reading
`x` applied inside the region reads it through the region. An initializer runs at row `()`, so an
operation it performs is handled inside it, by a handling expression that is counted whole.

## The rule

A group `{ x₁ = e₁; …; xₙ = eₙ }`, its members in the order written, is **initialization-safe**
where, for each `i`,

```text
dom(imm(eᵢ)) ⊆ { x₁, …, xᵢ₋₁ }
```

that is, an initializer reads only members written before it.

**What it refuses is reported deterministically.** For each initializer in the order written, and
for each member it reads that is not written before it, in the order written, one error is given,
at the least witness `⟨r, p⟩` of that member in `imm(eᵢ)` — occurrences and promoting forms
ordered by their position in the group, its right-hand sides in the order written and each read
left to right, which needs no source position and so orders what a guest builds as well; a
witness with no promoting form comes before one with a form at the same occurrence. It is located
where `r`, the reference, stands, and where `p`, the form that promoted it, stands, if there is
one.

Initialization order is the order the members are written, **within the group**. Groups stay in
the stable dependency order Core requires ([Modules](../06-Modules/01-Modules.md)): a group is
initialized after every group it refers to, which are complete before it begins, so no order
across groups needs judging.

A function member, a `FunVal`, reads nothing when it is initialized, `imm` of a λ being `∅`, so
**every group of function values is initialization-safe**. The rule is a condition on the order
of what is read, not on the shape of a right-hand side: `g x = f x; f = g` is admitted, `f`
reading `g` written before it, and `f = g; g x = f x` is not, `g` being written after `f` —
whether or not `g` is a function, as at top level a later global is installed later.

| Group | Judgement |
| --- | --- |
| `fibAnd = Tuple "fib" (\n -> … snd fibAnd …)` | Admitted: `fibAnd` is read only under the λ |
| `functorIO`, `applicativeIO`, `monadIO` as records of closures and of earlier dictionaries | Admitted in any order where each field is a closure; a dictionary held as a field is read, so it is written before |
| `a = { next: \_ -> b }; b = { next: \_ -> a }` | Admitted |
| `x = Tuple 1 x`, `x = x` | Refused at `x`: it reads itself |
| `xs = Cons 1 ys; ys = Cons 2 xs` | Refused at `ys` in `xs`: written after `xs`. A cycle of data is no initialization order |
| `x = (\_ -> x) ()` | Refused at `x` inside the λ, and at the application |
| `a = { next: \_ -> b }; b = (select next a) Prim.Unit` | Refused at `b` inside `a`'s closure, and at the application in `b` |
| `a = g 1; g x = c x; c y = a + y` | Refused in `a`: it calls `g`, which reads `c`, written after `a`, and through it `a` itself |

## Where it is judged

**The judgement is defined on Core**, and the Core checker enforces it on every top-level `rec`
group and every local `letrec`, whoever built it, refusing the first read it finds where the
reference stands ([Core Type Checker](07-Core-Type-Checker.md)). That is the condition the
language guarantees. A `letrec` a guest builds through the kernel is judged as any Core is.

**The surface elaborator judges the source form** of a top-level group, and of every local group
a declaration holds, and reports what it refuses
as an error of the program, located where the reference stands and where the form that promoted it does
([Elaboration](../02-Surface-Language/01-Elaboration.md)). It applies the same judgement to each
member's right-hand side made Core with **every η-expansion it inserted taken as the expression it
expands**, whatever became of the expansion: the initialization dependencies of an expression are
judged before it is expanded and kept after it. `f :: forall a. a -> a; f = f` reads `f` at once
whatever the expansion makes of it, so the elaborator refuses it, where Core, seeing the λ the
expansion made, would not. Every other form is judged alike, so what the elaborator admits Core
admits.
