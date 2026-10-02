# Elaboration

## Core⁺

The representation elaborators work with is Core⁺: Core with unresolved holes added.

```text
κ⁺ ::= … | ?k                          kind metavariable
τ⁺ ::= … | ?α                          type metavariable
e⁺ ::= … | ?m                          term metavariable
         | ⟨ τ by f ⟩                  synthesis goal
         | hole τ                      typed hole, for diagnostics
```

**`⟨ τ by f ⟩` is a form elaboration is handed, not one a Core⁺ term holds.** Where it is met it is taken apart into `?m` in the term and the constraint `Synth ?m τ f` beside it ([Synthesis goals](#synthesis-goals)), so the term keeps the goal's metavariable alone and the goal itself is the constraint. Holding both would give one goal two representations.

**Invariant: a term handed to the Core type checker belongs to Core⁺ minus `{?k, ?α, ?m, ⟨…⟩, hole}`.** If any remain after zonking — after applying the accumulated substitution — the goal is unresolved and compilation fails.

```text
Ψ ::= ·
    | Ψ, ?k [Γκ] R          unresolved kind; Γκ the kind variables it may mention,
                            R the requirements it carries
    | Ψ, ?k := κ            solved
    | Ψ, ?α : κ [Γτ; Γκ]    unresolved; the variables of either class it may mention
    | Ψ, ?α := τ            solved
    | Ψ, ?m : τ [Γx; Γτ; Γκ] unresolved; the values, types, and kinds it may mention
    | Ψ, ?m := e            solved
```

Recording the variables a metavariable was created under allows the scope check that decides whether a solution mentioning local variables may be assigned to it. A type metavariable records **both classes**, since a kind variable of an inner declaration escapes as readily as a type variable does — `?α`'s kind and the kinds inside its solution are where a kind variable reaches it. A kind metavariable records the kind variables alone: kinds and types are separate classes and no kind mentions a type variable (D2). A term metavariable records all three, value variables among them, since a solution such as a dictionary a resolver found may be a local of the site the goal stood at.

**A substitution narrows what the metavariables inside it may mention.** A metavariable standing in a solution mentions none of the variables it was created under until it is solved, so assigning `?α := τ` restricts every metavariable of `τ` to `?α`'s own scope — and refuses the assignment where the kind such a metavariable stands at lies outside it. Without that, `?α` created outside a binder and solved to a type mentioning `?β` would admit whatever `?β` was later solved to, binder and all.

**A term metavariable records no join point.** A join point does not cross a function boundary, and a solution supplied from elsewhere is in the same position: it may jump only to a join point it binds itself. What a synthesizer is shown of its site, `localContext`, holds none either.

**The narrowing reaches term metavariables too.** Assigning `?m := e` restricts every term metavariable of `e` to the intersection of its own scope and `?m`'s, and refuses the assignment where that metavariable's own type mentions what the intersection excludes; the type and kind metavariables of `e` are restricted to `?m`'s as a type's are. **A solution is not type checked where it is assigned** — an elaborator may construct an ill-typed term, and the Core type checker is what rejects one — so scope is the whole of what an assignment decides.

**A solution is held without its annotations**, and zonking puts it where `?m` stood, every node of it taking the annotation that `?m` carried: the place the goal was written.

`R` is settled with [kind unification](#kind-unification) below.

## Constraints

```text
Constraint ::= κ1 ≡ κ2                 kind equality
             | τ1 ≡ τ2                 type equality
             | ρ1 ≡ ρ2                 row equality
             | k ∉ ρ                   Lacks, as in Core
             | ρ1 # ρ2                 Disjoint, as in Core
             | Synth ?m τ f            synthesis goal
```

A `HasField k τ r` predicate is not a separate constraint. It is the row equality

```text
r ≡ ( k : τ | ?r )
```

for a fresh `?r`. Likewise `t = Union r s` is `t ≡ r ⊎ s`. Keeping the number of constraint forms small is what keeps the solver small.

## Kind unification

Solving `κ1 ≡ κ2` is **first-order unification with an occurs check**. Kind equality is syntactic and there is no computation at the kind level (D2), so every outcome is decided where the equation is met: a kind metavariable is assigned, or the two kinds differ. **There is no third outcome to wait for**, and this is the one place the solver's three-way split does not appear.

### A requirement is carried, not decided by equality

`Γ ⊢ κ qkind` is not a condition on kind equality. `?k ≡ Effect` is an equation that solves, and it is wrong only where `?k` stands somewhere a quantifiable kind is called for (D24) — under a `forall`, in a `[[κ̄]]`, or at a declaration's type parameter. Where `?k` stands for the result kind of an effect constructor, `Effect` is what belongs there.

A **requirement** is therefore recorded against the metavariable and re-applied at every assignment.

```text
R ⊆ { Quantifiable, ProducesType }

Quantifiable      Γ ⊢ κ qkind
ProducesType      result(κ) = Type
```

Each decides where the kind is known and attaches itself where it is not.

| | `Quantifiable` | `ProducesType` |
| --- | --- | --- |
| `Type` | holds | holds |
| `Row ε` | holds | fails |
| `Effect` | fails | fails |
| a kind variable | holds | fails — a scheme says nothing about what instantiates it |
| `?k` | attaches to `?k` | attaches to `?k` |
| `κ1 -> κ2` | both sides `Quantifiable`, and `κ2` `ProducesType` | `κ2` `ProducesType` |

Assigning `?k := κ` re-applies every requirement `?k` carries to `κ`, which is what makes assigning one metavariable to another **merge the two sets**: a requirement reaching an unsolved kind attaches itself there. So `?k` required quantifiable and solved to `?k1 -> ?k2` leaves `?k2` owing `ProducesType`, and a later `?k2 := Row Type` is where that is decided.

**A requirement is not work the scheduler holds.** It is a condition on the assignments a metavariable admits rather than something waiting on information, so it never becomes a `Pending` ([Elaborator API](03-Elaborator-API.md)).

### What the caller establishes

That a kind variable is **bound** is not checked here. Every kind variable of a well-formed kind is bound by the scheme of the declaration being checked (D3), so `k ∈ Γ` belongs where the kind is built; unification takes a rigid kind variable as it finds it.

## Type unification

Solving `τ1 ≡ τ2` is structural, and it is **directed by the kind both sides stand at**.

```text
Γ ; κ ⊢ τ1 ≡ τ2
```

**The kind is carried rather than synthesized.** Two sides of an equation stand at one kind by the premise of whoever wrote it, so unification never has to compute one and needs neither `Σ` nor a kinding judgement over Core⁺. What the kind is for is the one thing unification cannot read off a type: the kind a **metavariable** stands at is recorded in `Ψ`, and the carried kind is what it is held to. **Both sides are held to it**, not only the one being assigned, since a metavariable at the root of a solution stands at that kind too.

Where nothing in hand determines a kind — the argument of an application, an effect's argument, the row a `SymbolKey` Lacks constrains — a kind metavariable stands for it. Such a metavariable is a **local existential**: it belongs to the equation rather than to the solver's state, and one left unsolved and unreferenced when the equation succeeds is discarded.

### The rules

| Sides | |
| --- | --- |
| `?α` against anything | held to the carried kind, then assigned under the conditions every substitution meets (below) |
| `a` against `b` | equal where the correspondence below pairs them, and where neither is bound by a `forall` being descended and the two are one variable |
| `T [[κ̄]]` against `T [[κ̄']]` | the same constructor, and `κ̄ ≡ κ̄'` pairwise |
| `τ1 τ2` against `σ1 σ2` | a kind metavariable stands for the argument's kind, and the head is read at an arrow into the carried kind |
| `C => τ` against `C' => τ'` | `C ≡ C'`, then the bodies at `Type` |
| a row against anything | row unification, whose payload equations are discharged here |
| anything else | a mismatch |

A row's payload equations are type equations, so discharging them is this judgement's work rather than the row solver's. What they stand at follows the row element kind: a `Row Type` element carries a type, and what an effect's argument stands at is `Σ`'s to say, so a metavariable stands for each — **one per equation**, two arguments of one effect having no reason to share a kind.

**A constraint is compared by its own form.** A Lacks holds where the two keys are one and the two rows are equal, and its row element kind is what the key settles where the key settles it: an `EffectKey` or a `RegionKey` is a `Row Effect` and a `TagKey` or a `PositionKey` a `Row Type`, while a `SymbolKey` keys a field and a labelled effect instance alike and so settles nothing ([Kinds and Types](../03-Typed-Core/01-Kinds-and-Types.md)). A Disjoint holds where its two rows are equal pairwise, and **one kind serves them both**, the two sides of `#` sharing one row element kind ([Rows](../03-Typed-Core/02-Rows.md)).

### `forall` is compared through a correspondence

```text
forall (a : κ1). τ1  ≡  forall (b : κ2). τ2
```

holds when `κ1 ≡ κ2` and the bodies are equal under the correspondence `a ↔ b`. **Neither side is renamed.** Nested binders push onto a stack and a variable is read through the innermost entry mentioning it, so one bound on one side and free on the other is a mismatch however the two are spelled.

**A metavariable whose solution would mention a binder of the correspondence is refused**, on either side. Solving it needs the two binders identified rather than corresponded, and identifying them is α-conversion, which would have to rename either the scope a metavariable records or a binder inside the solution.

The refusal is a **mismatch of its own**, not a fourth outcome beside solved, stuck and mismatched. The equation fails and the caller reads a failure, as it does for two constructors that differ; what the distinct mismatch carries is why, since saying the two types disagree would misdescribe an equation that this judgement declines to solve rather than one that has no solution.

```text
forall a. Pair a a  ≡  forall b. Pair b b      accepted, the correspondence deciding it
forall a. ?m        ≡  forall b. Int           accepted, the solution needing no binder
forall a. ?m        ≡  forall b. b             refused
```

**Rank-1 inference is unaffected.** A scheme is instantiated at its use site before any monotype is unified, so two `forall`s meet only where an annotation wrote one. What is refused is confined to higher-rank types, and what to do about those is a question of its own ([Open Questions](../99-Open-Questions/01-Open-Questions.md)) rather than a gap in what Hindley–Milner needs.

**Rows under a correspondence are not an exception**, and the correspondence is a parameter of [row unification](#row-unification) for that reason. A rigid tail cancels the tail it corresponds to rather than the one it shares a name with, so `forall r. Record ( a : A | r )` and `forall s. Record ( a : A | s )` are the one type they are.

## Row unification

Solving `ρ1 ≡ ρ2` operates on the normal form. The procedure is **identical for record rows and effect rows**: effect row keys are rigid (D16), so `dom(F)` does not depend on how metavariables are solved and the case analysis does not depend on the order in which inference proceeds.

### Rigid and flexible

Row variables appearing in a normal form's tail are of two kinds, and the case analysis requires the distinction.

| | Origin | Assignable |
| --- | --- | --- |
| **rigid** `r` | a type variable of `Γ`, bound by `forall (r : Row ε)` | no |
| **flexible** `?r` | a metavariable of `Ψ` | yes |

A rigid row variable can equal only itself, or the variable a correspondence pairs it with where the equation stands under one. It can, however, **be absorbed by a flexible tail on the other side**: `?s := ( a : A | r )` is correct.

### The procedure

The correspondence `B` the equation stands under is a parameter. It is the one the enclosing comparison of two `forall`s built, and it is **empty for an equation under no such comparison**, which is every equation rank-1 inference produces.

```text
solve(ρ1 ≡ ρ2  under B):
  ⟨F1;T1⟩ = nf(ρ1)
  ⟨F2;T2⟩ = nf(ρ2)

  1. match the payloads of shared keys
     L = dom(F1) ∩ dom(F2)
     emit F1(k) ≡ F2(k) for each k ∈ L        discharged by type unification, under B
     D1 = F1 ∖ L,  D2 = F2 ∖ L        (thereafter dom(D1) ∩ dom(D2) = ∅)

  2. cancel shared tails, each class by its own notion of being the same variable
     a rigid tail cancels the rigid tail B pairs it with
     a flexible tail cancels the same metavariable on the other side
     T1' = T1 ∖B T2,  T2' = T2 ∖B T1   (thereafter nothing of T1' cancels anything of T2')

  3. split into rigid and flexible
     T1' = R1 ⊎ M1,  T2' = R2 ⊎ M2

  4. case analysis on |M|, the number of flexible tails

     (a) |M1| = 0, |M2| = 0
           success if D1 = D2 = ∅ and R1 = R2 = ∅
           otherwise failure, with a row diagnostic

     (b) |M1| = 0, |M2| = 1  (M2 = {?s})
           the left side is determined, so the right side's remainder must be empty
           failure if D2 ≠ ∅ or R2 ≠ ∅
           otherwise  ?s := D1 ⊎ R1
           the case |M1| = 1, |M2| = 0 is symmetric

     (c) |M1| = 1, |M2| = 1  (M1 = {?r}, M2 = {?s}; step 2 gives ?r ≠ ?s)
           introduce a fresh ?t and **substitute on both sides**
             ?r := D2 ⊎ R2 ⊎ ?t
             ?s := D1 ⊎ R1 ⊎ ?t

     (d) |M1| ≥ 2 or |M2| ≥ 2
           Stuck: no unique solution, so wait until one of them is instantiated

  every substitution performs an occurs check and the scope narrowing it owes,
  and the conditions below are re-decided against it
```

**An empty `B` makes `∖B` the difference by name.** Two rigid tails then cancel exactly when they are one variable, which is the ordinary reading, and the flexible tails cancel by identity in either case, a metavariable belonging to `Ψ` rather than to the side it appears on and so being the same metavariable whatever binders stand around it.

**What a flexible tail may absorb narrows under a non-empty `B`.** A solution mentioning a variable `B` pairs is refused for a row tail as for any other metavariable, so `?s := ( a : A | r )` is correct where `r` is a variable of `Γ` and refused where `r` is a binder the enclosing `forall` comparison put into `B`.

### Case (c) is the substance

`{ a : A | ?r } ≡ { b : B | ?s }` falls here.

```text
D1 = {a ↦ A},  D2 = {b ↦ B},  M1 = {?r},  M2 = {?s}

fresh ?t
?r := ( b : B | ?t )
?s := ( a : A | ?t )

check: left  = ( a : A | ?r ) = ( a : A, b : B | ?t )
       right = ( b : B | ?s ) = ( b : B, a : A | ?t )     equal under nf
```

**A substitution on one side alone cannot solve this.** Setting `?s := ( a : A | ?r )` makes the right side `( b : B, a : A | ?r )`, which does not match `( a : A | ?r )` on the left; substituting symmetrically into `?r` as well fails the occurs check and rejects a solvable constraint. Introducing a fresh `?t` and **refining both unknown tails at once** is the essence of row unification in this style.

### Failure and diagnostics

Failures in (a) and (b) are where a row problem is reported as a row problem: "`r` has no `name`", or "`r` is universally quantified and so cannot have `name`". It is not an instance resolution failure.

A leftover rigid tail fails the same way. `forall (r : Row Type). Record r ≡ Record ( name : String )` fails at "R1 ≠ ∅" in (b), because `r` is rigid.

Stuck in (d) is not failure; the scheduler resumes it.

### Preserving sharpness

Every substitution constructs a `⊎` and must satisfy its well-formedness conditions.

- For `?s := D1 ⊎ R1`, check that every `k ∉ ?s` assumed of `?s` holds of `D1` and `R1`.
- For the fresh `?t` of case (c), impose

```text
Lacks(?t) ⊇ dom(D1) ∪ dom(D2) ∪ Lacks(?r) ∪ Lacks(?s)
?t # R1,  ?t # R2
```

Neglecting this produces Core that is not well-kinded. The Core type checker re-validates the side conditions, so an omission is caught.

**What the fresh tail owes is inherited rather than copied.** A constraint that named `?r` names whatever `?r` was solved to once it is zonked, so one that reached `?r` reaches `?t` with nothing written onto the metavariable; the containment above is a consequence of the substitution and not a set anything maintains.

**And it is re-decided rather than decided here.** Each of these constraints holds on the assumptions of the site it came from, which the equation making the substitution need not stand at, so what decides them is the obligations and not this procedure ([Elaborator API](03-Elaborator-API.md)). A unification reports the metavariables it assigned, and its caller re-decides what those were watched by.

## Synthesis goals

```text
⟨ τ by f ⟩        f is an ordinary function of type Goal -> Elab Expr
```

The elaborator turns this into the constraint `Synth ?m τ f` and places `?m` in term position. Running `f` later assigns the result to `?m`.

**`f` is not a compiler builtin.** The type class resolver is an ordinary value in the standard library, and `f` is carried as a **`SynthRef`** — a resolved qualified global name — rather than as a host function (D39).

The compiler holds no algorithm specific to type classes. That is a statement about what it knows and not about how little it records: the scheduler keeps a goal record, because re-running a goal has to put it back in the context it was created in, and every field of that record is a fact about a goal rather than about a class, an instance, or a dictionary ([Elaborator API](03-Elaborator-API.md)).

## Scheduling synthesis

```text
data SynthesisResult
  = Solved   Expr
  | Stuck    (Set Meta)
  | Failed   Diagnostic
```

The scheduler is not specific to type classes. A `Stuck` goal is registered in a queue for each metavariable it awaits, under an identifier rather than as the job itself, since one goal waits on several metavariables at once.

```text
blocked : Meta ⇀ Set PendingId

assign(?α := τ):
  record the substitution in the current transactional Ψ
  re-decide the obligations ?α is watched by, each against its own site
  for each id in blocked[?α]:
    remove id from every dependency it is registered under
    push id onto the ready queue
```

**`assign` enqueues and runs nothing**, the scheduler loop being the only thing that attempts a job.

**An attempt is a transaction, and a `Stuck` goal is re-run from its beginning rather than resumed** (D40). A goal that postpones therefore leaves behind neither the metavariables it created nor the constraints it emitted, and what the blocked table holds is a description of work rather than a machine state. [Elaborator API](03-Elaborator-API.md) fixes what a rollback restores, what it deliberately does not, and why a synthesizer must be a function of its goal record.

Termination:

- every goal is `Solved`: zonk and hand the term to the Core type checker
- no progress and `Stuck` goals remain: report insufficient information, naming the metavariables awaited
- any goal is `Failed`: report that diagnostic

Distinguishing "unsolvable" from "not enough information yet" is exactly this three-way split. `Show (Array ?a)` is `Stuck {?a}`, not `Failed`.

Case (d) of row unification joins the same queue, and so does the search for an implicit effect handler ([Effect Handlers](02-Effect-Handlers.md)). The row solver, the handler search, and the synthesis scheduler share one resumption mechanism.

**A postponed equality carries the site it was written at**, as a synthesis goal does. What it takes from that site is the kind variables in scope there — a kind metavariable created while solving it may mention those and no others — and the place a failure is reported.

**What a substitution must preserve is decided elsewhere.** The row constraints naming a metavariable are obligations, and each is discharged from the atomic facts of the site **it** came from, which need not be the site of the equation making the substitution ([Elaborator API](03-Elaborator-API.md)). What a unification reports is the metavariables it assigned, and re-deciding what those were watched by belongs to the operation that installs the substitution rather than to whoever asked for the equation.

## Operations available to metaprograms

`Elab` is a monad running under compile-time effects.

```text
-- observation
goalType        : Goal -> Elab Type
viewType        : Type -> Elab TypeView
whnf            : Type -> Elab Type
normalizeRow    : Type -> Elab RowNormalForm
kindOf          : Type -> Elab Kind
typeOf          : Expr -> Elab Type
localContext    : Elab (Array (Ident, Type))
localConstraints: Elab (Array Constraint)
lookupGlobal    : QIdent -> Elab (Maybe Decl)
declsWithAttr   : QIdent -> Elab (Array QIdent)          -- the attribute, by its qualified name

-- metavariables
freshMetaType   : Scope -> KindView -> Elab Type
subgoal         : Scope -> Type -> SynthRef -> Elab Expr
isAssigned      : Meta -> Elab Boolean

-- constraints
unify           : Scope -> Type -> Type -> Elab Unit
entails         : Scope -> ConstraintView -> Elab Boolean
require         : Scope -> ConstraintView -> Elab Unit

-- construction
check           : Syntax -> Type -> Elab Expr
infer           : Syntax -> Elab (Tuple Expr Type)
localVariable   : Scope -> Ident -> Elab Expr
globalRef       : Scope -> QIdent -> [KindView] -> Elab Expr
literal         : Scope -> Literal -> Elab Expr
                  -- and the binders and applications the Elaborator API lists

-- control
transact        : Elab a -> Elab (Either Diagnostic a)
postpone        : Set Meta -> Elab a
throw           : Message -> Elab a
warn            : Message -> Elab Unit
```

**Quotation and antiquotation are syntactic forms producing a `Syntax`, not operations of this table.** They belong with the Surface AST, as `check` and `infer` do.

**The table divides by what it depends on.** Observation, the metavariable operations, the constraints, and control are the **kernel**, which a synthesizer needs and a parser is not required for. `check`, `infer`, quotation, and hygiene require a Surface AST and are separate, which is what lets the first guest synthesizer run before a parser exists ([Elaborator API](03-Elaborator-API.md)).

**A `Type`, an `Expr`, and a `Goal` reach a metaprogram as opaque handles**, and what it does with one it does through a view rather than by matching on a representation. Publishing Core⁺'s own representation would make an internal one part of an interface the compiler could no longer change. A `Type` holds the kind it stands at and an `Expr` the type it is claimed to have, which is what `kindOf` and `typeOf` read; what a goal, an operation that depends on where it stands, and a message are is fixed with the kernel ([Elaborator API](03-Elaborator-API.md)).

`transact` supports trying candidates transactionally. A rollback restores `Ψ`, the constraint set, the queues, and any terms constructed. Running one goal is the outermost such transaction and is not written anywhere (D40).

**What `transact` catches is a diagnostic and not a postponement.** A `postpone` inside one rolls that checkpoint back and propagates to the attempt root, so a candidate search never reads "not enough information yet" as "this candidate failed" ([Elaborator API](03-Elaborator-API.md)).

**`postpone` names metavariables that outlive the attempt.** The set is non-empty, and each of its metavariables existed before the attempt began and is still unsolved. One the attempt itself created is deleted by the rollback, so a job registered under it would wait on an assignment nothing can make.

`declsWithAttr` supports finding declarations that carry an attribute. It must work across modules, which is why attributes are persisted in a compiled interface ([Modules](../06-Modules/01-Modules.md)).

**What these two read is fixed before any goal exists.** The module's own declarations — their names, their attributes, and their schemes, provisional where one is still being inferred — are assembled once, before the first right-hand side is elaborated, and the set does not grow as the binding groups are folded. Otherwise the candidates a synthesizer finds would depend on when its goal was attempted ([Elaborator API](03-Elaborator-API.md)).

`localConstraints` exposes row constraints to elaborators, so that a derive mechanism working over rows can consult which Lacks constraints are already assumed.

Residual computation over an unknown tail takes this shape: `normalizeRow` extracts the known elements and the unknown tail, an encoder is assembled recursively over the known part, and where the tail `T` is non-empty the corresponding evidence is requested as a `subgoal`, to be decided by whatever the site it stands at can supply. **Closing the row is never required.**

## Names only elaboration writes

**The desugaring of a `reifiable full` clause refers to an elaboration-only entry**, the constructor `Base.Continuation.$Continuation` ([Modules](../06-Modules/01-Modules.md)). It wraps the clause's Core continuation in it, so that the clause holds an abstract `Continuation` where Core holds a function ([Effect Handlers](02-Effect-Handlers.md)):

```text
| reifiable full op x k -> e
  ⟹  full op (x, k0) -> let k = Base.Continuation.$Continuation k0 in e
```

**Outside `Base.Continuation`, that desugaring is the one place the constructor is written**, the module's own source writing it under its ordinary name. Name resolution does not resolve it, a macro cannot spell it, and the catalog a synthesizer reads omits it ([Elaborator API](03-Elaborator-API.md)). The module the clause stands in imports `Base.Continuation`, which the desugaring makes a dependency; a clause in a module without the import is reported where it stands.

**The Core type checker checks the reference as it checks any other**, as the application of a newtype constructor, and does not ask who wrote it. That no other term builds a `Continuation` is a guarantee of surface elaboration, and of nothing beneath it.

## What an elaborator may and may not do

An elaborator may:

- construct any Core⁺ term, including ill-typed ones
- fail, diverge, or exhaust resources
- produce unhelpful diagnostics

An elaborator may not:

- bypass the Core type checker
- pass a term that has not been type checked to Mid IR
- fabricate a derivation of `Γ ⊨ C` — there is nothing to fabricate, since no proof term is carried
- change the behaviour of type checking through attributes
- carry state from one attempt of a goal into the next

The last is the one the host cannot check. A goal is re-run from its beginning, so a synthesizer reading a mutable global of its own, or caching a candidate between attempts, gives two runs of one goal two results — and the second run is the one whose term reaches Core (D40).
