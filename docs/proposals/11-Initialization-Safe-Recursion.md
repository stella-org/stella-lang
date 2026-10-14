# Initialization-Safe Recursion

Status: Approved

## What is This?

### Background

A recursive binding group admits function values alone (D14). Each right-hand side must be
syntactically a `FunVal` — a `λ`, or a type or constraint abstraction of one — so installing the
group reads nothing, and Core rejects `letrec x = f x` where it is checked instead of leaving an
uninitialized reference to be read at run time.

The rule is safe but blunt. It refuses groups in which nothing is read before it is initialized:

```stella
fibAnd = Tuple "fib" (\n -> if n < 2 then n else snd fibAnd (n - 1) + snd fibAnd (n - 2))

functorIO     = { map: \f m -> bind monadIO m (\x -> pure applicativeIO (f x)) }
applicativeIO = { functor: functorIO, pure: pureIO, apply: \mf mx -> bind monadIO mf (\f -> map functorIO f mx) }
monadIO       = { applicative: applicativeIO, bind: bindIO }
```

`fibAnd` stores a recursive function in data, as a recursive dictionary does, and the second
group is the shape every instance dictionary of a class hierarchy takes — records of closures
referring to one another, some of them holding another dictionary as a field. Neither is a
`FunVal`, and both are refused today: the surface elaborator reports a member of a recursive
group that is no `FunVal` as a form it does not elaborate ([Open Questions](../technical-references/99-Open-Questions/01-Open-Questions.md),
*Recursive bindings that are no functions* and *Mutually dependent instance dictionaries*).

What a member may not do is **read** a member that is not yet initialized. `x = Tuple 1 x` reads
`x` while building it; `x = (\_ -> x) ()` does too, a λ applied at once running its body during
initialization; so does `x = twice (\_ -> x) 0` for a `twice` that applies what it is given. A
syntactic condition sees none of the difference between these and `fibAnd`. A judgement of what
an initializer reads, conservative and decidable, does.

The lowering is the second half. Mid IR's `letrec` allocates every closure of a group and then
fills the capture lists, which is right for closures and wrong for anything else: `fibAnd`'s inner
λ is created while `fibAnd`'s own initializer runs, and captures a value that does not exist yet.
A thunk recomputed at each reference would close the cycle at the price of a call at every use,
and of recomputing what the source evaluates once. This proposal gives the group a dedicated
initialization instead.

### Requirements

1. **No read of an uninitialized member** in a program the compiler accepts: the condition is
   judged statically, in Core, and no run-time check is relied on for it.
2. **Initialization stays strict and ordered.** A group's members are evaluated in the order they
   are written, each once, before anything after the group runs; a member nothing refers to is
   evaluated all the same, and its divergence or fault is observed where the group is
   initialized. Nothing becomes lazy.
3. **No cost where none is needed.** A group of functions alone is lowered as it is today. A
   top-level group uses the global slots the runtime already has. Only a local group with a member
   that is no function value pays for a cell, and a reference to such a member costs a state test
   and a load, not a call.
4. **Core enforces the condition, and the surface adds to it.** The Core checker judges every
   recursive group, whoever built it, and that is the condition the language guarantees. The
   surface elaborator judges the source form, with the immediacy the source gives it: an
   η-expansion it inserts does not make a read it delays later. It therefore refuses what Core
   would refuse and, for such an expansion, more — `f = f` among them — and never admits what Core
   refuses.
5. **Representation is untouched** (D31). How a recursive member is stored and initialized is a
   matter of the binding, not of the `Rep` of the value it holds.

## The judgement

### What an initializer reads

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
`b = (select next a) Prim.Unit`, which [Open Questions](../technical-references/99-Open-Questions/01-Open-Questions.md)
records as what no syntactic condition sees.

The forms with a rule of their own are the variables, the binders, the forms that build or take
apart a value without running what it holds, and the control forms:

| Form | `imm` | `lat` |
| --- | --- | --- |
| `x`, a member | `{ x ↦ ⟨x, –⟩ }` | `lat*(x)` |
| `y`, a local | `∅` | `ρ(y)` |
| `M.x [[κ̄]]`, `c`, `recordEmpty`, `readCell ℓ.k` | `∅` | `∅` |
| `λ(y : τ). e` | `∅` | `imm(e) ∪ lat(e)`, with `ρ(y) = ∅` |
| `Λ (a : κ). e`, `e [σ]`, `Λ (_ : C). e`, `e [•]`, `openEff [ρ] e` | `imm(e)` | `lat(e)` |
| `M.c ē`, a spine whose head is a data constructor or a foreign, through type and constraint applications, with no more arguments than its arity | `⋃ imm(eₖ)` | `⋃ lat(eₖ)` |
| `extend k e₁ e₂`, `update k e₁ e₂`, `merge e₁ e₂`, `inject k e` | `⋃ imm(eₖ)` | `⋃ lat(eₖ)` |
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
which promotes. A `δ_f` may carry a function value but may not apply one ([Semantics](../technical-references/03-Typed-Core/06-Semantics.md)),
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

### The rule

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
the stable dependency order Core requires today ([Modules](../technical-references/06-Modules/01-Modules.md)):
a group is initialized after every group it refers to, which are complete before it begins, so no
order across groups needs judging.

A function member, a `FunVal`, reads nothing when it is initialized, `imm` of a λ being `∅`, so
**every group D14 admits is initialization-safe**, and is lowered as it is today. The rule is a
condition on the order of what is read, not on the shape of a right-hand side: `g x = f x; f = g`
is admitted, `f` reading `g` written before it, and `f = g; g x = f x` is not, `g` being written
after `f` — whether or not `g` is a function, as at top level a later global is installed later.

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

### Where it is judged

**The judgement is defined on Core**, and the Core checker enforces it in place of guardedness,
for a top-level `rec` group and a local `letrec` alike. A `letrec` a guest builds through the
kernel is judged by the checker as any Core is.

**The surface elaborator judges the source form** and reports what it refuses as an error of the
program, not as a form this version does not elaborate. It applies the same rules to Core⁺, with
one difference: an η-expansion it inserts, `EEta`, is judged as the expression it expands, its
initialization dependencies judged before the expansion and kept after it ([Elaboration](../technical-references/02-Surface-Language/01-Elaboration.md)).
`f :: forall a. a -> a; f = f` reads `f` at once whatever the expansion makes of it, so the
elaborator refuses it, where Core, seeing the λ the expansion made, would not. Every other form is
judged alike, so what the elaborator admits Core admits.

## Typed Core

### Syntax and typing

The syntax is unchanged, and a recursive group's right-hand sides become expressions:

```text
letrec { x̄ : σ̄ = ē } in e
rec { x₁ : σκ₁ = e₁ ; … }
```

```text
  Γ' = Γ, x₁ : σ₁, …, xₙ : σₙ
  each i:  Γ'; · ⊢ eᵢ : σᵢ ! ()
  { x̄ = ē } is initialization-safe
  Γ'; Δ ⊢ e : τ ! ρ
  ──────────────────────────────────────────────
  Γ;Δ ⊢ letrec { xᵢ : σᵢ = eᵢ } in e : τ ! ρ
```

**An initializer is checked under no join point**, `Δ = ·`. A `FunVal` discarded `Δ` at its λ, so
the rule could pass it on; a general initializer could otherwise jump to a join point outside the
group and leave it half initialized. The row stays `()`: an initializer performs nothing, so
initialization has no effect to order beside reading.

A top-level `rec` group is checked as today, every scheme registered first, with
initialization safety in place of `FunVal` ([Modules](../technical-references/06-Modules/01-Modules.md)).

### Semantics

**A by-need cell** holds one member of a recursive group while the group is initialized and
after. It is in one of three states:

```text
Suspended e      its initializer, not yet run
Evaluating       its initializer running
Ready v          its value
```

A configuration carries a store `N` of by-need cells. **A location `ℓ` naming a cell is no value**:
it stands only as the operand of the run-time forms `force ℓ` and `fill ℓ e`, and **evaluating a
member's name is forcing its cell**. `letrec` allocates a cell for each member, every initializer
suspended with each member's name replaced by the force of its cell, then forces the cells in the
order written, and only then evaluates its body:

```text
  letrec { x̄ : σ̄ = ē } in e
    →  force ℓ₁ ; … ; force ℓₙ ; e[ x̄ := force ℓ̄ ]
       with ℓ̄ fresh,  N(ℓᵢ) := Suspended (eᵢ[ x̄ := force ℓ̄ ])

  force ℓ     →  v                      where N(ℓ) = Ready v
  force ℓ     →  fill ℓ e               where N(ℓ) = Suspended e,  and N(ℓ) := Evaluating
  fill ℓ v    →  v                      and N(ℓ) := Ready v
  force ℓ     →  initialization fault   where N(ℓ) = Evaluating
```

`e₁ ; e₂` is `let _ = e₁ in e₂`, and `fill ℓ □` is an evaluation context. A member's name given to
a constructor, put in a record, or returned by the body is evaluated there, as any variable is,
and so forces its cell: `Cons 1 ys` forces `ys`'s cell before the constructor is built, and a body
returning `x` returns the value `x`'s cell holds. **A cell is held raw only under a λ**, where the
force of it stands unevaluated in the body until the closure is applied — which is what an
implementation's closure capturing the cell is.

**Initialization safety makes the cells strict.** The judgement is designed so that evaluating an
initializer forces only the cells of the members in `dom(imm(eᵢ))`; for a safe group those are
written before it, and the group's own sequence has already filled them. So every `force` the
sequence performs finds its cell `Suspended`, every other `force` during initialization finds its
cell `Ready`, every `force` after the group finds every cell `Ready`, and no initialization fault
is reached. The cells are therefore no lazy evaluation — each initializer runs once, at its place
in the order — and a program the checker accepts never observes the state of one. A divergence or
a fault of an initializer is observed where the group is initialized, as today a `nonrec`'s is.
That the judgement does bound the forces so is the property the Typed Core text proves of it,
by induction on evaluation, the abstract maps standing for the forces a value's closures perform
when applied.

**A top-level `rec` group** is the same model over global names: the fold installs every member
as a suspended entry of `G`, its name being the force of its entry, and forces the entries in the
order written. This replaces the installation of every right-hand side at once, which only a
group of values could have.

`rec_i(x̄ : σ̄. v̄)` is no longer needed: the force of a cell takes its place, and a group of
function values is the case in which every cell is filled at once with the closure its λ is.
Run-time terms are typed under a context of locations `ℓ : σ`, as they are under `Γ_R`, `force ℓ`
at `σ` and `fill ℓ e` where `e : σ ! ()`; erasure keeps a cell as it keeps a recursive closure.

## Core⁺ and the elaborator

- `ELetRec` and `DeclRec` carry expressions, judged by the same rule.
- `isFunVal` is no longer a condition on a recursive group; `CorePlus.Term.isFunVal`'s refusal of
  an η-expansion not yet contracted, and the top-level check of `isFunVal` beside the immediate
  references, are replaced by the judgement over the source form.
- `immediateReferences` is retired: it computes `imm` without the promotion rule, and returns
  nothing for a match, a record, or a selection, so it is no judgement of safety.
- The diagnostic is an error of the program, one for each initializer and member [the rule](#the-rule)
  refuses, located at its least witness — the reference and, where a form promoted the read, that
  form: *`x` is read here while its recursive group is being initialized, before
  `x` is*, saying whether `x` is the member being initialized or one written after it.
  `OutsideSubset "a recursive value that is no function"` disappears.

## Lowering and the run-time

### Top level

**Nothing new.** A top-level member already lives in a global slot, the slots are installed in
the order of `GLOBALS`, and a member refers to another by global name, read by `LOADG` when the
reference is reached. A member that is a λ is a `func` and one that is not is a `run` — the shape
of the right-hand side decides, as it does for a `nonrec` — and the `run`s are evaluated in the
order written.

**This erases the top-level cells, and initialization safety is why.** Installing a `func` or
running a `run` at a member's place in the order is forcing its cell there, the slot being the
cell's `Ready` state. A safe group's initializer reaches a member written before it, which is
installed, and reaches one written after it only from a part of a closure not yet run, which runs
after the group; so no `LOADG` of a member ever meets an empty slot — the `Suspended` state, which
nothing observes outside the sequence — and none meets one being initialized — the `Evaluating`
state, which a safe group never forces. A backend therefore keeps no state beside the slot.

`IO`'s instance dictionaries pay nothing: each is a global, each method a closure whose references
are `LOADG`s.

### Local groups

A local group of function values is lowered as today, `CLOSN` and `SETCAP`. Its cells are erased
for the same reason: a function member's force fills its cell with the closure at once, an
initializer reads nothing, and a closure allocated before its place in the order is reached, by a
safe group, only from code that runs after the group. In a group mixing the two, the function
members are closures and only the others have cells.

**A local group with a member that is no function value** gives each such member a by-need cell.
In Mid IR the binding records how the member is stored, and the class of the value the cell holds
apart from the class of the binder (D31):

```text
letrec { x_i : Rep = closure f_i [ā_i] ;  y_j : Val = need Rep_j g_j [b̄_j] } in expr

comp ::= … | force y                       the value the by-need cell y holds
```

**A cell's binder is `Val`.** What its local holds — and the register it is lowered to, and a
capture slot that captures it — is the cell, a heap object no class of value describes, never the
member's value. `Rep_j` is the class of the value the cell holds once it is `Ready`, and a `force`
gives that class: in `let z : Rep_j = force y_j` the destination is at the `Rep` the forced
binding records. A backend keeping one uniform representation ignores both, as it ignores every
`Rep`.

`need g_j [b̄_j]` is a cell suspended over a closure of `g_j`, a function of no parameter whose
body is the member's initializer, capturing `b̄_j`. A backend:

1. allocates every closure of the group and every cell with its initializer's closure, their
   capture lists unfilled;
2. fills every capture list — a capture of a by-need member capturing its cell;
3. forces the cells in the order written;
4. evaluates `expr`.

A reference to a by-need member is `force y`; a function member is referred to as today. Inside a
closure that captured a cell, the capture is the cell, at `Val`, and each reference forces it. The
verifier checks that a `need` binding names a function of no parameter, whose result is at the
`Rep_j` the binding records; that the binder of a `need` binding, and every capture of one, is
`Val`; that a by-need local stands only as the operand of `force` or in a capture list; that the
destination of a `force` is at the `Rep_j` of the binding it forces; and that a cell is forced by
the group's sequence in the order written.

### Bytecode, Steam, and JavaScript

Two instructions:

| Instruction | Effect |
| --- | --- |
| `NEED d, s` | A by-need cell in `d`, `Suspended` over the closure in `s` |
| `FORCE d, s` | The value of the cell in `s`, into `d`: `Ready v` gives `v`; `Suspended` marks it `Evaluating`, enters its initializer, and stores what it returns as `Ready`; `Evaluating` is an initialization fault |

`CLOSN` allocates the initializer closures and `SETCAP` fills them, so a cell's initializer is an
ordinary closure. A `FORCE` of a `Ready` cell is a state test and a load. An initialization fault
ends the run as a fault does; a module the compiler accepted never reaches one. Steam and the
JavaScript runtime each implement the cell as a value of its own, with its state.

**The registers carry the classes Mid IR gave them.** `NEED`'s destination and `FORCE`'s source
hold a cell and are `Val`, as is a capture slot holding one; `FORCE`'s destination is at the
class of the value, the `Rep_j` of the binding it was lowered from. Validation checks the first
two against the function's table of register and capture `Rep`s — a check of what the file
carries, not a derivation of it; that a `FORCE`'s destination matches the cell's `Rep_j` is the
Mid IR verifier's to establish, the cell's class not being in the file.

Neither format version changes. Versioning has not started, and both formats stay at version 0.
The `.dmi` is untouched: a recursive group is recorded nowhere in it, and a member that is a `run`
has no arity, as a `nonrec`'s does not.

## Documents to revise

- **Design Decisions**: D14 is rewritten — recursive groups are initialization-safe, judged in
  Core, initialized in the order written. D31 is untouched.
- **Typed Core**: Terms and Matching (the `FunVal` restriction on recursion), Typing Rules
  (`letrec`, `Δ = ·`), Semantics (by-need cells, the module fold, `rec_i` removed, erasure), Core
  Type Checker (guardedness), Examples (`fibAnd`), PureScript CoreFn (`Rec`'s condition).
- **Modules**: the `rec` rule and the fold.
- **Surface Language**: Elaboration (recursive groups, local blocks, η's initialization
  dependencies), Name Resolution (the judgement it defers to), Elaborator API (`letrec`'s
  admissibility).
- **Middle end and backend**: Mid IR (`letrec`, `need` and the `Rep` it holds beside its `Val`
  binder, `force`, the verifier, a top-level member being a `run`), Translation, Bytecode (`NEED`,
  `FORCE`, initialization, and validation checking their registers' `Rep`, where it otherwise
  checks none), Encoding (the opcodes), Abstract Machine, JavaScript.
- **Open Questions**: *Recursive bindings that are no functions* is closed. *Mutually dependent
  instance dictionaries* is restated: a group of dictionaries referring to one another is
  admitted, and what remains is a forward reference across groups, which this proposal does not
  change.
- **Implementation Plan**: the regression tables for recursive groups.

## Implementation

Two slices, each of units reviewed before the next begins.

**c3b-4a, top-level groups.** Local `letrec` keeps `FunVal` until 4b, so nothing a guest builds
reaches a lowering that cannot take it.

1. **The judgement in Typed Core**, and the `rec` rule of the module declaration checker.
2. **The elaborator's top-level groups**: the judgement over the source form, η counted
   unexpanded, the diagnostic.
3. **Mid IR and translation** of a top-level member that is no function as a `run`, through to
   Steam and the JavaScript backend.

**c3b-4b, local groups and the run-time.**

4. **Typed Core's `letrec`**, `Δ = ·`, the run-time semantics, and Core⁺ and the kernel.
5. **Mid IR**: `need`, `force`, translation, and the verifier.
6. **Bytecode**: lowering, `NEED` and `FORCE`, the `.dmo` format, and validation.
7. **Steam**.
8. **The JavaScript backend and runtime**.
9. **The elaborator's local blocks.**

The technical references are revised as each slice is accepted.

Tests that pin the semantics down, run on both Steam and the JavaScript backend from shared
fixtures:

- `fibAnd`, at top level and in a `let` block, computing a value through the stored function.
- Three dictionaries referring to one another, one holding another as a field, at top level and
  locally.
- A member nothing refers to whose initializer faults: the fault is observed where the group is
  initialized, before the body or anything after the group.
- Initializers with observable order — a `nonrec` after the group reading each member — showing
  each ran once, in the order written.
- A function member and a by-need member capturing each other.
- Rejections, at the reference and, where promoted, at the promoting form:
  - `x = x` and `x = Tuple 1 x`;
  - `xs = Cons 1 ys; ys = Cons 2 xs`;
  - `x = (\_ -> x) ()`;
  - a closure passed to a function and the function's result bound;
  - a closure taken out of an earlier member's value and applied;
  - an earlier member function called whose body reads a later member;
  - `f :: forall a. a -> a; f = f`, refused as before the expansion.
- Steam and JavaScript each running hand-written bytecode that forces an `Evaluating` cell,
  ending with an initialization fault.

## Open points

- **Whether a `FORCE` that finds its cell `Suspended` outside the group's own sequence should be a
  fault.** Under the judgement it never happens; forcing early is what the model says, and
  refusing it would need a fourth state.
- **Whether `force` deserves a form that only reads a `Ready` cell**, for a backend that would
  rather not keep the code to enter an initializer at every reference. Nothing needs it yet.
- **Precision across modules.** An application promotes whatever the callee is; a summary of what
  an imported function applies would admit more, at the price of carrying it in the `.dmi`.
- **A program whose group could be reordered.** The rule refuses `f = g; g x = f x`; the
  diagnostic could say that writing `g` first admits it.
