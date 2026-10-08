# Prompt-Local Cells

Status: Proposed

## What is This?

### Background

A **cell** is a mutable binding a handler's operation clauses read and write without building a
continuation (D36). Today a cell belongs to **one handler**: the `var` declarations of a group
written in a handling expression are visible in that group's clauses alone, and in Typed Core the
region of cells is owned by the one `handle` that handles one effect element.

```stella
main = handle e with
  State
    var c := 0
    fast | get _ -> c!
         | set s -> c := s
  Emit
    fast | emit _ -> c!        -- rejected today: `c` belongs to the State group
```

The intended model, recorded in Open Questions, is wider: **a cell is local to the prompt a
handling expression installs, and every group of that expression reaches it.**

```stella
main = handle e with
  var c := 0
  State
    fast | get _ -> c!
         | set s -> c := s
  Emit
    fast | emit _ -> c!        -- the same cell
```

Today's model also fixes the region key as a single constant, `RegionKey`, so that a row holds
at most one region. That forbids opening a region where another is open, and a handler
polymorphic in its residual row must assume `RegionKey ∉ e`. Under the intended model, prompts
owning cells nest freely, an inner cell hides an outer one of its name, and an open residual
row is never a reason to refuse a handler.

The reference semantics is **Hoop's prompt-local cells** (the `purescript-hoop-verify`
repository), whose runtime semantics is mechanised in F*. This proposal keeps Hoop's observable
behaviour — which cells a resumption shares and which it copies — and replaces Hoop's
label-and-placement lookup with static identity.

### Requirements

1. `var c` introduces a cell owned by **the handling expression** it is written in. Every
   operation clause of every group in that expression reaches it.
2. Prompts owning cells **nest without restriction**. An inner cell of a name hides an outer
   one; leaving the inner prompt makes the outer one visible again.
3. A cell reference is **resolved statically**, at elaboration, to the cell of one specific
   handling expression. A reference that the enclosing expressions do not declare is an error at
   once; nothing fills it in later from an outer handler.
4. An unknown region in an open ambient row is **never** a reason to reject an application.
5. Sharing and copying follow Hoop: **only the cells inside the stack segment a continuation
   captures are copied, by value, into each resumption.** The cells of the prompt that captured
   it are not in the segment and are shared by every resumption.
6. The handled computation, the `return` clauses, and the initial values do not reach the
   expression's own cells.

## Semantics, informally

**Where a region stands.** A handling expression with cells opens one region, standing directly
below the outermost prompt the expression installs. Each group installs a prompt of its own, as
today; the inner groups' clauses reach the region by identity rather than by adjacency.

```text
  ┌────────────────────────────┐
  │ handled computation  e     │
  ├────────────────────────────┤
  │ prompt of the Emit group   │   items are installed top-down, outermost first
  ├────────────────────────────┤
  │ prompt of the State group  │
  ├────────────────────────────┤
  │ region { c }               │   opened before the first item is installed
  └────────────────────────────┘
```

**What a resumption sees.**

| The continuation is captured by | Is the region in the captured segment | What resumptions see |
| --- | --- | --- |
| a group of the expression owning the region | no, the region stands below every group | **one live region, shared**: a write before `resume` is seen by the resumed computation, and a write during one resumption by the next |
| a handler outside the expression | yes | **a copy per resumption**: each begins from the values held at the capture |

Composition order is therefore observable, as in Hoop and Koka: `state(choice(...))` threads one
counter through both branches, `choice(state(...))` gives each branch its own. A copy is a copy
of the cell slots; the values the slots hold are shared, being immutable.

**`return` clauses and initial values.** Initial values are evaluated in declaration order before
any item of the expression is installed, outside the region; they reach no cell of the
expression. The surface does not let a `return` clause read the expression's cells, so an
ordinary return hands back no state, as `ST` and unlike a state monad. Typed Core is more
general here (below).

## Typed Core

### Region names

A **region name** `ℓ` is a new syntactic class. It is not a type and has no kind. It is bound by
the `region` binder, never by `forall` or `Λ`, and no term or type abstracts over one, so **a
region name is never the target of an instantiation**: no `forall`, `Λ`, or metavariable stands
for one. The only operations that replace a region name are binder-aware α-renaming and the
replacement of a binder by a fresh run-time name when the region opens (below). Region names are
what make a region's identity static.

```text
Γ ::= …
    | Γ, region ℓ : ι          ι = ( k1 : σ1, …, kn : σn ), a closed layout
```

### Syntax

```text
e  ::= …
     | region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e      open a region and evaluate e in it
     | readCell ℓ.k                           read the cell k of region ℓ
     | writeCell ℓ.k e                        write it
     | handle e with h                        no cells, no initial values

h  ::= { handles ent ; return (x : τ) -> e_r ; cl̄ }

ent ::= …
      | region ℓ                              a region element of a `Row Effect`

RowKey ::= …
         | RegionKey ℓ                        the key of `region ℓ`
```

`handle e with h @ ( ē )`, the `cells [r]` part of a handler, the single constant `RegionKey`,
and the element `region r ι` are removed. The run-time forms `handleO` and `handleI` disappear:
no handler owns a region, so no handler tells an owner from a reinstatement.

`region ℓ` is its own payload: `key( region ℓ ) = RegionKey ℓ`, `payload( region ℓ ) = region ℓ`.
The layout is read from `Γ`, not from the row.

### Free region names, α-equivalence, and substitution

`frn(τ)` is the set of region names occurring in `τ` — in a `RegionKey ℓ` key, in a `region ℓ`
element, and in the key of a `Lacks` constraint. Types bind no region name, so `frn` of a type is
plain occurrence. In a term, `region [ℓ] … in e` binds `ℓ` in `e` and in nothing else: not in
the layout types `σ̄`, and not in the initial values `ē`.

- **α-equivalence** renames a region binder together with every occurrence it binds, in terms
  and in the types those terms annotate.
- **Key equality**: `RegionKey ℓ1 = RegionKey ℓ2` exactly when `ℓ1 = ℓ2`, after α-renaming.
  No instantiation replaces a region name, and α-renaming and opening replace a binder with all
  its occurrences at once, so a key is rigid and row equality stays decidable (D13, D16).
- **Type substitution in a term is capture-avoiding for region binders as well.** Substituting
  `σ` for `a` under `region [ℓ]` renames the binder first where `ℓ ∈ frn(σ)`. This arises when a
  global's body is instantiated at a type mentioning a region of the caller, two binders of one
  name being possible across globals.

### Kinding

```text
  ( region ℓ : ι ) ∈ Γ                       ( region ℓ : ι ) ∈ Γ
  ──────────────────────────────             ──────────────────────────
  Γ ⊢ region ℓ : Effect entry                Γ ⊢ RegionKey ℓ key Effect
```

A region name out of scope makes a type ill-kinded. This is the scope check for region names.

### Entailment: what freshness gives

A row variable bound outside `ℓ` cannot be instantiated with a row mentioning `ℓ`: wherever its
instantiation is formed, `ℓ` is not in scope, and capture-avoiding substitution keeps it so. The
`region` rule therefore records, for its body, **`RegionKey ℓ ∉ t` for every row variable
`t : Row Effect` bound in `Γ` before `ℓ`**. A row variable bound later, inside the body, gets no
such fact. A function that abstracts over a row inside a region and needs the key absent says so
in its type, as for any other key.

This is what lets a handler with cells take an open residual row without any constraint:

```text
counter : forall (e : Row Effect). forall (a : Type).
          Counter ∉ e => ( Unit -{ ( Counter | e ) }-> a ) -{ e }-> a
        = Λ e. Λ a. Λ _. λ (thunk : Unit -{ ( Counter | e ) }-> a).
            region [ℓ] ( n : Int ) @ ( 0 ) in
              handle ( ( openEff [( region ℓ )] thunk ) Prim.Unit ) with { handles Counter ; … }
```

`openEff [( region ℓ )] thunk` needs `( Counter | e ) # ( region ℓ )`, that is
`RegionKey ℓ ∉ e`, which the binder supplies. `counter` can then be applied anywhere, inside
another region included: the two regions carry different keys and sit side by side in one sharp
row.

**In elaboration** the same holds of a metavariable only by its scope. Ψ records, for each
metavariable, the region names in scope where it was created, as it records type and kind
variables. `RegionKey ℓ ∉ ?m` is discharged by `ℓ ∉ scope(?m)` and is otherwise an ordinary
obligation. Assigning a metavariable a solution mentioning a region name outside its scope is the
same scope failure as for a type variable.

### Typing rules

```text
  the k̄ are distinct      |ē| = |k̄|      ι = ( k̄ : σ̄ )      Γ ⊢ σ_j : Type
  each j:  Γ;Δ ⊢ e_j : σ_j ! ρ                    ← outside the region
  ℓ ∉ dom(Γ)                                      ← the binder is fresh
  Γ' = Γ, region ℓ : ι, { RegionKey ℓ ∉ t | t : Row Effect ∈ Γ }
  Γ';· ⊢ e : β ! ( region ℓ | ρ )
  ℓ ∉ frn(β) ∪ frn(ρ)                             ← nothing of the region outlives it
  ─────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e : β ! ρ

  ( region ℓ : ι ) ∈ Γ      ι(k) = σ      RegionKey ℓ ∈ dom(nf(ρ))
  ─────────────────────────────────────────────────────────────
  Γ;Δ ⊢ readCell ℓ.k : σ ! ρ

  ( region ℓ : ι ) ∈ Γ      ι(k) = σ      RegionKey ℓ ∈ dom(nf(ρ))      Γ;Δ ⊢ e : σ ! ρ
  ──────────────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ writeCell ℓ.k e : Unit ! ρ
```

- `( region ℓ | ρ )` is sharp because the binder is fresh: `ℓ ∉ frn(ρ)` already implies
  `RegionKey ℓ ∉ ρ` for the known part of `ρ`, and the recorded facts cover its row variables.
- `Δ` is discarded at the region body. A join point does not cross into it, as it does not
  cross into a `handle`.
- **`handle` has one rule again**, the present rule without cells. A group's clauses, its handled
  computation, and its return clause all stand at rows the context gives, so a region opened
  outside the `handle` is visible to all three. The surface decides which of them may name it.
- **A `return` clause reading a cell is admitted by Core on purpose.** Region and `handle` are
  separate binders, so nothing in Core can tell a return clause inside a region from any other
  term inside one. The surface does not produce such a read. A backend and an optimizer must not
  assume that a return clause reads no cell.
- The escape condition `ℓ ∉ frn(β) ∪ frn(ρ)` plays the role `r ∉ ftv(β) ∪ ftv(ρ)` plays today.
  Every way to reach a cell mentions `ℓ` — a closure over a `readCell ℓ.k` carries `region ℓ`
  in its arrow — so no such value can be the answer or reach the residual row.

**Binder freshness is a well-formedness condition on the checker's input, not a rule of the
language.** Core is a language of terms up to α-equivalence, and in it a term written with a
shadowing binder is the same term as its renamed form. What the checker receives is a
**representation**, and it requires that representation to follow the unique-binder
convention for the binders of terms: no region binder, `Λ`, or clause type binder binds a name
already bound where it stands. The rule's `ℓ ∉ dom(Γ)` is that condition for region binders.

Types are not held to the convention. A type reaches the checker from `Σ` and from substitution
as well as from the term, and is compared up to α-equivalence. So a `forall` met while kinding is
scoped lexically: it hides an outer variable of its name, together with every assumption made
about that outer variable.

The condition is checked rather than assumed. A representation that breaks it is rejected as
malformed, not renamed: elaboration generates fresh names, so such an input is an elaborator
defect. This closes the present hole by which a type binder shadowing an outer variable is
accepted with the wrong meaning. Reduction keeps the convention: the opening step introduces a
globally fresh name, and type substitution renames a binder it would capture.

### Reduction

Opening a region allocates a name, which is the region's run-time identity.

```text
  region [ℓ] ( k̄ : σ̄ ) @ ( v̄ ) in e   →   region⟨ℓ'⟩ ( k̄ ↦ v̄ ) in e[ℓ := ℓ']      ℓ' globally fresh

  region⟨ℓ⟩ θ in v                     →   v

  region⟨ℓ⟩ θ in Ev_ℓ[ readCell ℓ.k ]        →   region⟨ℓ⟩ θ in Ev_ℓ[ θ(k) ]
  region⟨ℓ⟩ θ in Ev_ℓ[ writeCell ℓ.k v ]     →   region⟨ℓ⟩ θ[k ↦ v] in Ev_ℓ[ Prim.Unit ]

  Ev_ℓ ::= an evaluation context with no region⟨ℓ⟩ on the path to the hole
```

- The allocated names form a global context `Γ_R` of `region ℓ : ι` entries. Run-time terms are
  typed under it. The run-time form `region⟨ℓ⟩ θ in e` binds nothing; its rule is the source
  rule with `ℓ ∈ Γ_R` in place of the binder, and `θ` typed against `Γ_R(ℓ)`.
- **A continuation copies its segment as it stands, names included.** Applying
  `k = λy. H Ev_k[y] with h` twice yields two terms holding `region⟨ℓ⟩` under the same `ℓ`. No
  rule renames them, so one name may label several frames on one path, and `Ev_ℓ` picks the
  innermost.
- The rule for a value reaching a handler is the present one without cells. A value reaching a
  `region⟨ℓ⟩` frame passes through it and closes it.
- **A `fast` clause body runs outside `Ev_k`** as today, so the regions inside `Ev_k` are not on
  its path.

### Why the innermost frame of a name is the right one

The central proposition:

> When a well-typed term executes `readCell ℓ.k` or `writeCell ℓ.k`, the innermost `region⟨ℓ⟩`
> on the path is the region instance `ℓ` denotes, or the continuation copy of it that is running.

It splits into a type-safety part and a coherence part.

**Type safety does not depend on which copy is chosen.** Every frame named `ℓ` descends from one
opening, so every frame named `ℓ` carries a `θ` typed against the one layout `Γ_R(ℓ)`. Reading
or writing any of them preserves the type.

For progress, a frame must exist. The only evaluation-context frame that puts `region ℓ` into
the ambient row at the hole is `region⟨ℓ⟩` itself:

- `handle` adds only its handled element.
- `openEffC` runs its inner computation at a smaller row.
- Application requires the arrow's row to equal the ambient row, so a β-step adds nothing.

So a hole at whose row `region ℓ` stands — which `readCell ℓ.k` requires — has a `region⟨ℓ⟩`
on its path.

**Coherence.** The argument rests on three facts and one definition.

1. **Distinct openings carry distinct names.** A name is allocated fresh at each opening, so two
   dynamic instances — two applications of one handler, recursive ones included — never share
   one.
2. **Frames sharing a name are copies of one opening.** A name is introduced by an opening and
   duplicated only by applying a continuation, which copies its segment as it stands. Every frame
   named `ℓ` therefore has the layout `Γ_R(ℓ)`.
3. **A computation needing `ℓ` runs only beneath a frame named `ℓ`.** An eliminator of `ℓ` — a
   `readCell ℓ.k`, a `writeCell ℓ.k`, or the application of a function whose arrow carries
   `region ℓ` — is typed only where `region ℓ` is ambient. By the progress argument above, such a
   place has a `region⟨ℓ⟩` frame on its path. Preservation keeps this true across every step,
   continuation application included, since a copy carries its frames along with the code that
   needs them.
4. **Definition.** Where several frames named `ℓ` stand on the path, the Core semantics selects
   the innermost: the copy currently running.

None of this asks where a value referring to `ℓ` has been in the meantime. A value may be held
for any length of time — in a closure, in a polymorphic data structure, behind an operation's
type parameter, inside a `reifiable` continuation — and it reaches a cell only when it is
eliminated. By fact 3 that happens beneath a frame named `ℓ`, and by the definition it reaches the
innermost one.

**Agreement with Hoop.** Hoop resolves a cell by its label to the innermost frame carrying that
label, and relies on its placement invariant to keep that frame the clause's own. Stella resolves
by name to the innermost frame of that name, which needs no placement invariant: frames of other
openings carry other names and are passed over whatever their labels. Both machines copy a frame
exactly when it lies inside a captured segment. Which cells a resumption shares and which it
copies therefore depends on the same thing in both — whether the frame is inside the segment —
and the table in "Semantics, informally" is Hoop's.

A semantics that renamed each copy would differ observably. A value created before a capture,
handed out through a type parameter and back, would point at the original instance. That
instance is no longer on the stack once its segment is captured, so such a value would get stuck.

The cases the review asked to be addressed, each read through the facts above:

| Case | What happens |
| --- | --- |
| A continuation resumed again while a copy of it is running | The second copy is pushed above the first under the same name (fact 2). Anything needing `ℓ` that runs while the second copy is on top reaches the second (definition). This is Hoop's innermost-by-label choice as well. |
| A `reifiable full` continuation stored and resumed later | Its segment, region frames included, travels with it and is copied at each application, names kept (fact 2). Its type admits an application only where its row is ambient, after widening, and the frames it needs come with it. |
| Values as arguments or results of polymorphic operations | They may be held anywhere their type allows, for any length of time. They reach a cell only when eliminated, which is beneath a frame named `ℓ` (fact 3), and reach the innermost (definition). |
| A closure whose type mentions `RegionKey ℓ` | It cannot be the answer or reach the residual row of its region (`ℓ ∉ frn(β) ∪ frn(ρ)`), and can be applied only where `region ℓ` is ambient (fact 3). |
| Future scoped and higher-order effects carrying a computation | In the present first-order Core, a computation payload is run only where its row is ambient, so running one outside its region is rejected by typing. That says nothing yet of a construct that moves or duplicates frames, as Hoop's scoped weave does by running a computation beneath borrowed frames. **Such a construct carries a preservation obligation of its own**: that every frame it moves or copies keeps its name, and that fact 3 holds after its steps. |

This part is the one the proposal asks to be reviewed most closely. Test cases are listed under
Implementation.

### Erasure

```text
⌊region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e⌋  =  region ℓ ( k̄ ) @ ( ⌊ē⌋ ) in ⌊e⌋
⌊readCell ℓ.k⌋                       =  readCell ℓ.i         i the position of k in the layout
⌊writeCell ℓ.k e⌋                    =  writeCell ℓ.i ⌊e⌋
⌊{ handles ent ; return … ; cl̄ }⌋    =  { key key(ent) ; return … ; ⌊cl̄⌋ }
```

The region name survives erasure as a **term-level** binder: it stands for the run-time identity
the opening step allocates. A cell is named by its position, the key becoming debug information.

## Core⁺ and the elaborator kernel

- Core⁺ mirrors Core: `ERegion`, and `EReadCell` and `EWriteCell` naming a region binder. A
  handler loses its layout.
- **The kernel API.**
  - A region is opened and closed as a binder. `openRegion` takes the layout and answers with
    the binder, the fresh region name it binds, and the scope the body is built in. That scope
    binds the name with the layout and jumps to no join point outside, Core discarding `Δ` at a
    region's body.
  - `closeRegion` takes the body and the initial values, built outside the region. It refuses a
    body jumping to a join point, and a body claimed at a type mentioning the region (the escape
    condition).
  - `readCell` and `writeCell` take the region's binder handle and a key, and are built in a
    scope the region stands around.
  - **A region's name is how a type mentions it.** `extendRow` admits the element
    `region ℓ` under `RegionKey ℓ`, and a constraint admits the key `RegionKey ℓ`, where `ℓ` is
    a region name in scope. A region not in scope makes the type ill-kinded, as an unbound type
    variable does. A clause reading a cell needs this: its row is given by whoever opens the
    handler, and must hold the region. A `perform` and a handler name an effect, and refuse a
    region element.
  - Handlers are opened without cells.
  - The present rules on "a term that depends on its region", and on regions carried by goals and
    term metavariables, become ordinary binder scoping: a term mentioning `ℓ` stands where `ℓ`
    is in scope, and a metavariable's scope lists the region names it may mention.
- **The guest bundle** `Stella.Elab` follows:
  - its `RowKey` and `RowPayload` views lose the region constant and gain the region name;
  - its handler requests lose cells;
  - region requests are added.

## The surface

### Grammar

```text
handlingExpr ::= "handle" expr "with" block(handlingItem)
               | "using" block(handlingItem) "handle" expr
handlingItem ::= "var" ident ":=" expr
               | (qualProperName | ident) marker? clause+       a group
               | expr                                           a handler applied
handlerDecl  ::= "handler" ident binderAtom* "::" type "where" block(handlerItem)
handlerItem  ::= "var" ident ":=" expr
               | marker? clause+
```

- **A `var` of a handling expression is an item of the expression**, and every `var` stands
  before its first group or handler. One after a group or a handler is rejected.
- The form `State var n := 0 | …`, a cell after a group's head, is removed.
- A handler declaration keeps its `var`s before its clauses (see Handler declarations below).

### The Surface AST

The cells move from the group to the expression that owns them.

```text
ExprHandle Origin (Array CellDeclaration) (Array HandlerItem) Expr
Group       = { origin, label, effect, body :: HandlerBody }
HandlerBody = { operations, return }                      no cells
DeclHandler … { cells :: Array CellDeclaration, body :: HandlerBody }
```

A `CellVar` keeps its binding identity. Elaboration maps the binding to the region binder of
its expression and to the cell's position, which is how a reference is resolved to one slot of
one region.

### Scope

- **The cells of a handling expression are in scope in the operation clauses of its groups**,
  every group alike. They are not in scope in:
  - its `return` clauses;
  - its initial values;
  - its handled expression;
  - the expressions of its handler items, a handler applied as an item being a function value
    written elsewhere or inline.
- **A handling expression written inside an operation clause** sees the cells of the expression
  owning that clause, besides its own. Its own cells hide outer ones of the same name throughout
  the expression. In its initial values and `return` clauses, where its own are closed, such a
  name reaches neither cell, as today.
- A `c!` or `c := e` no enclosing handling expression declares is an error where it is written.
- The rule rejecting a handler with cells applied inside a clause of another handler with cells
  is removed, together with the generated `RegionKey ∉ e`. Nesting is unrestricted.

### Desugaring

```text
handle e with var c̄ := ē ; i1 ; … ; in

  ⟹  region [ℓ] ( c̄ : σ̄ ) @ ( ē ) in  i1 (\_ -> … in (\_ -> e))
```

- `ℓ` is fresh.
- `c!` and `c := e` in a group's clause become `readCell ℓ.c` and `writeCell ℓ.c e`.
- A thunk handed to an item stands at a row holding `region ℓ`, so the groups inside it reach
  the region, and a handler applied as an item instantiates its residual row with that row.
- A handling expression with no `var` opens no region.
- A handler declaration desugars to a function whose body is the `region` around its `handle`,
  as in the `counter` example above.

### Handler declarations

A handler declaration writes its cells in its block, ahead of its clauses.

```stella
handler h :: E ~> e where
  var n := 0

  fast | op x ->
    let f = \_ -> n!
    in f ()
```

**The cells belong to the prompt an application of `h` installs, not to the effect `E`.** A
handler declaration is a handling expression holding one group, whose head is the one element its
signature handles. Its cells are that expression's prompt-local cells, as in any other handling
expression. They are not cells local to an effect. The Surface AST holds them in
`DeclHandler.cells`, beside the body, not in the `HandlerBody` of the group.

```text
h = λ thunk.
      region [ℓ] ( n : Int ) @ ( 0 ) in
        handle ( ( openEff [( region ℓ )] thunk ) Prim.Unit ) with
          { handles E
          ; return (x : a) -> x
          ; fast op x -> let f = λ _. readCell ℓ.n in f Prim.Unit
          }
```

- **The initial values are evaluated once per application of `h`, and each application opens a
  region of its own.** Two computations run under `h` count separately, a recursive application
  included.
- **`n` is in scope in the operation clauses and in the local functions written in them.** It is
  not in scope in the `return` clause, in the initial values, or in the computation `h` handles.
- **`f` may be called inside the region.** A clause handing `f` out — returning it as the answer,
  or as part of it — is rejected by the escape condition, `f`'s type carrying `region ℓ`.

**Applying a declared handler inside another handling expression joins no layouts.**

```stella
handle program with
  var c := 0
  h
  Emit
    fast | emit _ -> c!
```

- `h`'s clauses reach `h`'s own `n` and nothing else.
- The `Emit` group reaches the outer expression's `c`.
- `h` cannot take up the `c` of the expression it is applied in, and the `Emit` group cannot reach
  `h`'s `n`.

Effects that are to share one cell are written as groups of one handling expression:

```stella
handle program with
  var n := 0
  E
    fast | op x -> n!
  Emit
    fast | emit _ -> n!
```

### Diagnostics

- A cell problem names the cell and says that a cell is reached from the operation clauses of
  the handling expression declaring it.
- The nesting diagnostic is removed.

## Lowering and the run-time

**Mid IR.**

- `handle h f [ā]` takes no initial values; a handler entry has no cells.
- A new computation, `region k̄ f [ā] @ [v̄]`, opens a region of `|k̄|` cells with initial values
  `v̄` and calls `f`, a function of one parameter, with the region's identity. `k̄` is the
  layout's keys in the order it writes them: a cell's position is its key's, the keys are
  distinct, and `v̄` holds one value per key. They are what a region entry's cell count and debug
  keys come from.
- `readCell x i` and `writeCell x i a` name the local holding a region's identity and a cell
  position.
- The identity is an ordinary local of `Rep` `Val`. A closure over a cell captures it as it
  captures any local.

**Bytecode and `.dmo`.**

- `HNDL` and `TAILHNDL` lose their cell operands.
- `RGN d, region, r_body, m, c…` and its tail form open a region, its entry giving the cell
  count and, as debug information, the keys.
- `CGET d, r_region, i` and `CSET d, r_region, i, s` reach a cell by identity and position.
- `HANDLERS` loses its cell vector, and region entries take a section of their own.
- The `.dmi` encoding of keys and row entries drops the region tag. No published scheme mentions
  a region name, top-level declarations being checked with no region in scope.
- Neither format version changes. Versioning has not started, and both formats stay at version 0.

**Steam and the JavaScript runtime.**

- `RGN` allocates a fresh identity, pushes a region frame holding the identity and the cell
  slots, and enters the body with the identity as its argument. An identity is fresh across
  every run of the host, not within one machine: a continuation stored by one run may be
  applied by another, and its frames keep the identities they were opened with. Steam
  allocates a host object per opening and compares by reference.
- `CGET` and `CSET` walk to the innermost **visible** region frame of that identity — the walk
  that skips a `fast` clause's boundary, as today.
- A value reaching a region frame pops it.
- Handler markers lose `ownsRegion` and the owner/reinstatement distinction.
- Applying a continuation copies the region frames of its segment slot by slot **and keeps their
  identities**, which is the copy rule above.
- A region identity is a run-time value that crosses no foreign boundary. Typing keeps it inside
  Stella code, and a manifest kind for it does not exist.

## Documents to revise

- **Design Decisions**: D36 is rewritten; D16 for `RegionKey ℓ`; D33 for the copy rule.
- **Typed Core**: Kinds and Types, Rows, Effects (cells), Terms, Typing Rules, Semantics (handlers,
  cells, erasure, the proposition above), Core Type Checker.
- **Surface Language**: Effect Handlers (cells), Syntax, Name Resolution, Surface AST, Elaboration,
  Elaborator API (cells, regions, the kernel requests).
- **Middle end and backend**: Mid IR, Translation, Bytecode, Encoding, Interface, Abstract Machine,
  JavaScript.
- **Open Questions**: the question of whose cells they are is closed. The question of how a helper
  could be written against a handler's cells is restated: a helper still cannot name a region,
  region names being unquantifiable.
- **Implementation Plan**: the regression tables for cells.

## Implementation

Each unit is reviewed before the next begins.

1. **Typed Core and the checker**, together with binder freshness for every type binder.
   Includes Core⁺, the kernel builders, the guest bundle, and the hand-written Core fixtures.
2. **Mid IR** and translation.
3. **Bytecode**: lowering, the `.dmo` format, and the `.dmi` key encoding.
4. **Steam**.
5. **The JavaScript backend and runtime**.
6. **The surface**: grammar, CST checks, Surface AST, resolver.
7. **Technical references.**

The surface's ownership boundary is fixed by this proposal (the Surface AST shape and the scope
rules above), so the surface-language track can build on it before unit 6 lands.

Tests that pin the semantics down, run on both Steam and the JavaScript backend from shared
fixtures:

- Two groups of one expression sharing a cell, each writing and reading the other's write.
- `state(choice(…))` against `choice(state(…))`: shared against per-branch, Hoop's fixtures
  26–29 and Koka's figures.
- A `full` clause of the owning expression resuming twice, each resumption seeing the other's
  writes.
- A handler declaration whose clause builds a local function over its cell and calls it, and the
  same function returned from the clause, the second rejected by the escape condition.
- A declared handler with a cell applied as an item of a handling expression with a cell of its
  own: neither reaches the other's.
- **The same handler applied inside its own clause**, both with a cell `c`, and a closure over
  the outer `c` called inside the inner handler's clause. It must reach the outer cell.
- A continuation resumed while a copy of it is running: the inner copy's code reaches the inner
  copy.
- A closure created before a capture and run in two copies: each run reaches its own copy.
- A value carried out through an operation's type parameter and handed back: it reaches the copy
  that runs it.
- Rejections:
  - a region name escaping through the answer type;
  - escaping through the residual row;
  - a shadowing type binder;
  - a shadowing region binder.
- `RegionKey ℓ ∉ t` for a row variable `t` bound inside the region, as a pair:
  - rejected where nothing supplies it, freshness giving no fact for `t`;
  - accepted where the function binding `t` assumes it, a `RegionKey ℓ ∉ t =>` in its type
    discharged at each application.

## Open points

- Whether a region identity should be a distinct `Rep` rather than `Val`. Nothing depends on it.
- Whether the checker should accept any representation and rename it into the unique-binder
  convention itself, instead of rejecting one that breaks it. This proposal rejects, since such
  a representation means elaboration produced one.
