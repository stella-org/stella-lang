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
    | Ψ, ?k [Γκ] R                 unresolved kind; Γκ the kind variables it may
                                   mention, R the requirements it carries
    | Ψ, ?k := κ                   solved
    | Ψ, ?α : κ [Γτ; Γκ; Γℓ]       unresolved; the type and kind variables and the
                                   region names it may mention
    | Ψ, ?α := τ                   solved
    | Ψ, ?m : τ [Γx; Γτ; Γκ; Γℓ]   unresolved; the values, types, kinds, and region
                                   names it may mention
    | Ψ, ?m := e                   solved
```

Recording the variables a metavariable was created under allows the scope check that decides whether a solution mentioning local variables may be assigned to it. A type metavariable records **both classes**, since a kind variable of an inner declaration escapes as readily as a type variable does — `?α`'s kind and the kinds inside its solution are where a kind variable reaches it. A kind metavariable records the kind variables alone: kinds and types are separate classes and no kind mentions a type variable (D2). A term metavariable records all three, value variables among them, since a solution such as a dictionary a resolver found may be a local of the site the goal stood at. **A type and a term metavariable record the region names in scope as well** (D36): a region name is bound by its `region` and nowhere else, so a type mentioning `region ℓ` or a solution reading a cell of `ℓ` escapes its region exactly as a type mentioning a variable escapes its binder.

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

**A constraint is compared by its own form.** A Lacks holds where the two keys are one and the two rows are equal, and its row element kind is what the key settles where the key settles it: an `EffectKey` or a `RegionKey ℓ` is a `Row Effect` and a `TagKey` or a `PositionKey` a `Row Type`, while a `SymbolKey` keys a field and a labelled effect instance alike and so settles nothing ([Kinds and Types](../03-Typed-Core/01-Kinds-and-Types.md)). A Disjoint holds where its two rows are equal pairwise, and **one kind serves them both**, the two sides of `#` sharing one row element kind ([Rows](../03-Typed-Core/02-Rows.md)).

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

**What these two read is fixed before any goal exists.** The module's own declarations with a signature — their names, their attributes, and their written schemes — are assembled once, before the first right-hand side is elaborated, and the set does not grow as the binding groups are folded. Otherwise the candidates a synthesizer finds would depend on when its goal was attempted ([Elaborator API](03-Elaborator-API.md)).

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

## Inference

The surface elaborator infers what a signature does not write. This section fixes the judgement it uses, how an effect row is fitted where it is used, when and over what a declaration is generalized, and how a written signature is checked. The mechanism it runs on — jobs, attempts, the transaction — is the subject of [Elaborator API](03-Elaborator-API.md).

### The judgement and the ambient row

```text
Γ ; ρ ⊢ e ⇐ τ ⇝ e'        check e against τ
Γ ; ρ ⊢ e ⇒ τ ⇝ e'        infer the type of e
```

**`ρ` is the ambient row**, the row the evaluation of `e` may perform, which every application in `e` is fitted into. It is a `Row Effect` of Core⁺ and may be a metavariable.

| Where | Ambient row |
| --- | --- |
| a top-level value's right-hand side | `()` |
| a computation declaration's body | the row its signature writes |
| the body of a `Λ` | `()`, as Core requires of a value form |
| the body of a λ with no expected type | a fresh row metavariable |
| the body of a λ checked against `A -{r}-> B` | decided at the checking boundary ([below](#explicit-checking-boundaries)) |
| an operation clause | the row its handler gives the clause |

**An application `e1 e2` under `ρ`** infers `e1`, reads an arrow `A -{r}-> B` off its type — equating the type with an arrow of fresh metavariables where its shape is not yet known — checks `e2` against `A`, and places a fit of `r` into `ρ` on the function side.

### Fitting an effect row

**A fit is the containment `source ⊆ target`** between the row a function performs and the row ambient where it is applied (D8). It is decided on the difference of the two rows after normalization, not on their equality.

```text
fit(source, target):
  normalize both; cancel the keys they share, equating their payloads, and the tails they share
  what remains: (Ds, Rs, Ms) of the source, (Dt, Rt, Mt) of the target
                 — known keys, rigid tails, flexible tails

  the source's remainder is empty:
      the target's is empty too             Equal
      otherwise                             Widen w, where w = Dt ⊎ Rt ⊎ Mt, requiring source # w
  Ds or Rs not empty, and Mt empty          a row mismatch
  otherwise                                 undecided; it waits on Ms ∪ Mt
```

**A known key or a rigid tail of the source that the target cannot absorb is a mismatch whatever the source's own tail is.** Assigning a source tail only adds to the source, so with no flexible tail left in the target nothing can contain what the source has left. `( Console | ?t )` against `( LiftIO | e )` is a mismatch, not a wait; at a checking boundary it is where a plan is sought ([Explicit checking boundaries](#explicit-checking-boundaries)). The fit waits only where the source's remainder is flexible tails alone, or the target keeps a flexible tail that can still absorb it.

**Widening is the target's remainder entire**: with the source's remainder empty, whatever `Mt` is later solved to belongs to the difference. The requirement `source # w` is what Core's `openEff` rule asks of the term the widening becomes.

```stella
use :: forall e. (Unit -> Unit / {| Console, ...e |}) -> Unit / {| Console, Clock, ...e |}
use k = k ()
```

```text
fit(( Console | e ), ( Console, Clock | e ))   Console and e cancel, the source's remainder is empty
                                              → Widen ( Clock )
Core:  ( openEff [( Clock )] k ) Prim.Unit
```

**A fit wraps a term or demands containment alone.** A fit placed on the function side of an application, or at the outermost arrow of a checking position, wraps that expression, and its `Widen` becomes `openEff [w]` around it. A cell read or write places a fit that wraps nothing ([Cells](#cells)): its outcome records that the containment holds and produces no term. The two share the decision and the resolution below.

#### Resolving fits by direction

A fit still undecided when the loop reaches quiescence is resolved by the direction of the containment it states. Fits are taken in connected components — the fits, jobs, and obligations of one owner, the declaration body or the binding group they belong to, sharing an unsolved metavariable, a job joined by every metavariable an attempt of it could assign — and each component is resolved inside a transaction of its own, to a fixpoint, reading and changing nothing of another.

1. **A target whose remainder is one flexible tail `?m`** is solved to the compatible union of the source remainders of every undecided fit whose target's remainder is `?m`. The ambient row takes the least row its sources need.
2. **A source whose remainder is one flexible tail `?t` created by instantiation** is solved to the target's remainder. The tail of an instantiated effect-polymorphic function takes the ambient row.

**Each round computes its assignments from the state as it stands and installs them simultaneously**, rule 1 before rule 2. Assignments that depend on one another — a metavariable rule 1 and rule 2 both reach, or one standing in another's union — are not made, and the component is ambiguous. The outcome therefore depends on no order of the fits. Every assignment goes through the ordinary assignment of [Elaborator API](03-Elaborator-API.md): occurs check, scope, level, the obligations it is watched by, and the jobs it wakes. **A round that assigns nothing is a fixpoint only where nothing has moved**: a union not formed is waited on while the component's other assignments, the equations of the keys a union shares, and the jobs they wake still decide something, and the component is ambiguous only once none does. **A checking boundary's fits are not taken**; the boundary's own fits against its expected row stand in for them, and only their assignments are kept ([below](#explicit-checking-boundaries)).

**The compatible union** of rows is the least one formed without a new decision:

| Rows hold | Union |
| --- | --- |
| one key in several | one element, the payloads equated before the tails are counted |
| distinct known keys | joined |
| a key and a tail | joined, `k ∉ tail` required |
| distinct tails, at most one of them flexible | joined, the tails required apart |
| the same tail in several | one tail |
| two distinct flexible tails | not formed: their disjointness would be a new decision, so the fit waits |

**What a union needs to be a row is required at the site of each row it joins**, the union being the row ambient at each, so the order the rows come in decides nothing.

**A row metavariable records whether instantiation made it.** One created for a scheme's row quantifier where the scheme is instantiated is an **instantiation row**; every other — the row of a λ with no expected type, the row of an arrow whose shape was not known — is an **inference row**. Where two are identified, the result is an instantiation row only if both were, so the direction of a unification decides nothing. Rule 2 maximizes an instantiation tail only: an inference tail is a function's own least row, and filling it with the ambient one would lose that.

**What is left undecided is reported by its cause.** The transaction is rolled back either way, and the diagnostic says which.

| Cause | Reported as |
| --- | --- |
| no unique compatible union; two distinct flexible tails | an ambiguous effect row, an annotation asked for |
| assignments depending on one another | the same |
| a fit undecided at the fixpoint | the same |
| a key's payloads differ | a type mismatch |
| a rigid tail or a known key of the source not contained by the target | a row mismatch |
| an occurs or a scope check failing | that failure |
| the least solution breaking a Lacks or a Disjoint | the obligation broken |

```stella
greet = \_ -> let _ = say "a" in tock ()     -- say : String -> Unit / {| Console |}, tock : Unit -> Unit / {| Clock |}
```

```text
fit(( Console ), ?e) and fit(( Clock ), ?e) wait; ?e is the λ's row
rule 1: ?e := ( Console, Clock ); the fits become Widen ( Clock ) and Widen ( Console )
greet : ∀u. u -{( Console, Clock )}-> Unit
```

Taking the first fit as an equation would have fixed `?e := ( Console )` and refused the second.

### Cells

Cells are prompt-local (D36): a cell belongs to the handling expression that declares it, and every group of that expression reaches it ([Effect Handlers](02-Effect-Handlers.md)).

- **A cell is found by lexical scope, never by inference.** Name resolution binds `x!` and `x := e` to the region binder of the handling expression declaring `x` and to the cell's position; a reference no enclosing expression declares is an error there, whatever the ambient row.
- **An open row is no evidence that a cell exists.** Reading or writing a cell needs its resolved binding and the element `region ℓ` in the ambient row. The elaborator places `fit(( region ℓ ), ρ)`, wrapping nothing: the containment is what Core's rule for `readCell` and `writeCell` asks, and an equation `ρ ≡ ( region ℓ | ?rest )` would leave the tail of a local function's row with nothing to decide it.
- **A region enters the ambient row only by the region binder**, which a handling expression with cells produces, and inside it by the `openEff [( region ℓ )]` its desugaring places around each thunk. A fit adapts a function to a region already ambient; it creates no region and no cell binding, and neither a fit nor closing removes a region element.
- **A region name is never generalized.** A type or term carrying `region ℓ` out of its region is an escape: the metavariable it would be assigned to was created outside the region and has no `ℓ` in its scope, so the assignment fails. The failure is reported where the cell is referenced, with the escaping function or the answer boundary as a secondary location.
- **A term metavariable and a synthesis goal keep the region scope of the place they were created**, so no solution reading a cell is assigned to one created outside that cell's region.

```stella
handler h :: E ~> e where
  var n := 0
  fast | op x -> let f = \_ -> n! in f ()
```

```text
the clause's ambient row is ( region ℓ | e )
f's row ?e; n! gives fit(( region ℓ ), ?e); f () gives fit(?e, ( region ℓ | e ))
rule 1: ?e := ( region ℓ ); the second fit is Widen e
Core:  let f : Unit -{( region ℓ )}-> Int = λ _. readCell ℓ.n in ( openEff [e] f ) Prim.Unit
```

### Closing

**A row a function needs nothing of is closed to `()` before it is generalized**, once, after the fits of its group are resolved by direction and immediately before the quantifiers are chosen — for a declaration with a signature, before its body is made Core. A fit the resolution leaves undecided is not reported yet: closing may decide it. **Candidates are found from the group's zonked terms, its undecided fits, and its residual atoms**: each unsolved metavariable at `Row Effect` there that no checking boundary owns. **A candidate is closed where it stands at most once across the types the group's zonked terms and members write, and nothing requires anything of it**: no undecided fit has it in its target, no waiting equation or goal could assign it — by either of its sides or by what it waits on — and no residual atom but a Lacks names it. A fit and an atom find a candidate and are no occurrence of it: how many fits name a row says nothing of how it stands in a type. A Disjoint keeps a candidate open, and the Lacks are dropped, `()` satisfying every one. Occurrences are counted over the whole group, so a metavariable two members share is never closed by the order they are visited in. **The candidates are closed together, and the jobs and the resolution of the fits run again**; where either fails, the closing is undone, and what failed is what the declaration is reported by — the rows decided again without the closing need not fail the same way — a checking boundary its body cannot meet being outside the subset as it is wherever it is decided. A fit still undecided after is reported as an ambiguous effect row.

A closed row costs nothing: a fit adapts a pure function to any ambient row. `id = \x -> x` is `∀a. a -> a` rather than `∀a e. a -{e}-> a`, and the scheme agrees with the signature an author would write. Closing never removes a known element, a region included.

### Generalization

**Only top-level value declarations are generalized implicitly** (D48). A local `let` or `where` binding is monomorphic unless it carries a signature; a binding with a signature is checked against it and never generalized; the kinds of data declarations are generalized by [their own rule](#kinds).

**Declarations are inferred in the strongly connected components of the references their bodies write**, read off the Surface AST before elaboration; a reference to a declaration with a signature is no edge, its scheme being known. Inside a group, a member without a signature is referenced at a monomorphic type of its own, from an environment local to the group rather than from the catalog. The order the Core module is emitted in is computed afterwards, from the committed terms.

**A metavariable records the level of the binding group it was created in**, and an assignment lowers every metavariable of its solution to the level of the one assigned. The candidates of a group are the unsolved metavariables of its level.

#### The value restriction

A member whose right-hand side, zonked and after any η-expansion, is no value form — by the predicate the Core checker uses for the body of a `Λ` — is not generalized. The metavariables reachable from its type and its body are lowered at once and recorded as **restricted**. They may still be solved by what the rest of the group's elaboration decides; **one still unsolved when the group is generalized asks for a signature.** A variable is never left monomorphic for a later declaration to fix.

A restricted metavariable is unsolved where its zonked representative still holds an unsolved metavariable, whatever its own entry in `Ψ` says.

#### Quantifiers

**The quantifiers of a member, `Qᵢ`, are the generalizable type metavariables its inferred type holds, with what their kinds depend on**, in one deterministic order: members in the order they are declared, each type read left to right, a metavariable placed where it first appears. Constraints do not extend `Qᵢ`. A candidate reached only through the body, or only through a constraint, is one no caller could determine, and asks for an annotation:

```stella
f _ = let _ = g Nil in 0
g xs = f ()
```

```text
g : ∀a. List a -> Int, since ?a is in g's type
f's body uses g at ?a, which f's type Unit -> Int does not reach
→ an ambiguous type in f, an annotation asked for
```

#### Obligations in atoms

**A required Lacks or Disjoint is kept as the atomic requirements its normal form decomposes into**, and a part proved where it arises is not kept. A site's facts are its context's assumptions decomposed into `Γ*`, together with the scope of the metavariables.

```text
Lacks k ρ, ρ = ⟨F;T⟩:
  k ∈ dom(F)                     refused
  a rigid tail t                 k ∉ t proved from Γ*, or refused
  a flexible tail ?t             proved by scope (k = RegionKey ℓ, ℓ ∉ scope(?t)), or the atom Lacks k ?t

Disjoint ρ1 ρ2:
  a key shared by the known parts             refused
  a known key of one against a tail of the other   as Lacks above
  two rigid tails t1, t2                      t1 # t2 proved from Γ*, or refused
  a flexible tail and a rigid one             the atom Disjoint ?t r
  two flexible tails                          the atom Disjoint ?t1 ?t2
```

An atom carries the basis, context, and origin of the obligation it came from. An assignment to an atom's tail decomposes it again at its site, which may add atoms, remove it, or refuse. Every atom holds a flexible tail, so an atom is proved at a site only by scope or by an atomic fact of that site's `Γ*`; otherwise it stays as it is. Core rederives the original Disjoint an `openEff` asks for from the atoms.

`?e # ( region ℓ, Console )`, with `?e` created outside the region, keeps the atom `Console ∉ ?e` alone: `RegionKey ℓ ∉ ?e` holds by scope.

#### Constraints

**The constraints of a member are found before its quantifiers are bound, over the group's shared metavariables, call site by call site:**

```text
Cᵢ = Ownᵢ ∪ ⋃ { residualizeAt(s, Cⱼ) | s a reference in i's body to a member j of the group }
```

- `Ownᵢ` are the required atoms left at quiescence whose origin is `i`'s body. Assumptions are no part of it.
- `residualizeAt(s, Cⱼ)` is the requirement a recursive reference raises at `s`, decomposed at `s`'s site: an atom an assumption around the reference proves is gone there, and `i` is not constrained by it.
- A propagated atom is identified by its call site in `i` and the atom of `Own` it began as, so the identifiers are finitely many, and the union is a monotone least fixpoint: finite and unique. Adding `[•]` to a recursive reference raises no new requirement.
- **Every atom of `Cᵢ` must mention no metavariable outside `Qᵢ`**; one that does is ambiguous, reported at the reference it came from.
- At the fixpoint, each `Cᵢ` is rewritten in the member's rigid variables, normalized, deduplicated, and ordered deterministically.

**A recursive reference** to a member `g` gains the type arguments of `g`'s final scheme and a `[•]` for each of its constraints, in their final order. A type argument outside the referring member's `Qᵢ` is a candidate of its body alone, and is ambiguous as above.

#### Kinds

**Kind metavariables are generalized into the kind variables of the declaration's scheme, before its type quantifiers are made** (D3), so that no type quantifier is left at an unsolved kind. A kind candidate is an unsolved kind metavariable of the group's level reached from the kind of a type quantifier or from a constructor's kind argument in the type. One carrying `ProducesType` cannot become a kind variable and is reported. A local binding generalizes no kind.

**A data declaration group** generalizes the kind metavariables its heads leave unsolved into each declaration's kind variables, and a reference inside the group to a member gains its kind arguments, `[[k̄]]`.

```text
data App f a = App (f a)
  f : ?k1, a : ?k2; the field gives ?k1 := ?k2 -> Type; ?k2 is unsolved at the end of the group
  → App : ∀k. (k -> Type) -> k -> Type
```

#### What does not cross a generalization

A generalization introduces rigid variables and `Λ`s, so nothing that would need its scope rebound beneath them crosses it.

- A synthesis goal whose type touches `Qᵢ` asks for a signature. One that does not is attempted again first, and one still waiting after that is reported as undecided synthesis; a goal that fails is a failure.
- A metavariable an equality job still touches is restricted (above).
- No term metavariable, no undecided fit, and no pending boundary job crosses — a boundary whose plan is still being sought among them.

#### The procedure

For each top-level group, in the dependency order above:

1. Elaborate every member's body, each as an attempt.
2. Run the loop to quiescence and resolve the fits.
3. η-expand where [Signatures](#signatures) allows, rebuilding the wrapping fits of the expanded body against its new ambient row.
4. Run the loop and resolve the fits again.
5. Apply the value restriction: lower and record the restricted metavariables.
6. Compute a provisional `Qᵢ` for every member.
7. Ask for a signature where a synthesis goal touches a provisional `Qᵢ`; attempt every other goal again.
8. Run the loop to quiescence; report a goal still waiting as undecided synthesis.
9. Snapshot the candidates for closing.
10. Close.
11. Run the loop to quiescence and resolve the fits again; where either fails, undo the closing and report the failure by its cause.
12. Confirm that no synthesis goal, term metavariable, undecided fit, or pending boundary job remains; restrict what an equality job still touches; ask for a signature where a restricted metavariable is unsolved.
13. Compute the final `Qᵢ`; report candidates of a body alone as ambiguous.
14. Compute `Cᵢ` and check it against `Qᵢ`.
15. Generalize the kinds.
16. Assign the members' `Qᵢ` to fresh rigid variables, all at once, and build `TForall` and `ETyLam`.
17. Rewrite `Cᵢ` in those variables and wrap each body in `EConstraintLam`, removing the atoms from the store.
18. Complete the recursive references.
19. Make each member's scheme final in the catalog.

**The assignment of step 16 is the mechanism's own**, made outside every attempt, and takes no scope check: the rigid variables are bound at the root of each declaration and nowhere else, so nothing escapes. Each is bound outside every region a scope check has used to discharge `RegionKey ℓ ∉ ?m`, which is why no such discharge is undone by it; generalizing only the metavariables of a group's own level keeps that true.

### Signatures

| Operation | Rule |
| --- | --- |
| instantiate | at each occurrence of a variable or a global: a `∀` becomes an `ETyApp` at a fresh metavariable, a kind variable a fresh kind metavariable carrying `Quantifiable`, a `C =>` an `EConstraintApp` and a requirement |
| skolemize | checking against a `∀` adds a rigid variable to `Γ` and an `ETyLam`; a constraint is assumed and wrapped in `EConstraintLam`; the body must be a value form, or be η-expanded as below |
| subsumption | the fit of the outermost arrow's row alone; no deep skolemization, no contravariant position, no containment between polymorphic types, which are compared by correspondence |
| escape | the scope check of an assignment: a metavariable created outside a skolem's binder cannot be assigned a type mentioning it |

Higher-rank types follow from these rules where they are written; inference itself introduces a `∀` only by generalizing.

**A local binding with a signature inside a prompt** is skolemized where it stands: its `Λ` is inside the region, and what its body creates has both the skolem and `ℓ` in scope. A signature has no spelling for a region, so a local function reading a cell is left without one and inferred.

#### η-expansion

The body of a `Λ` must be a value form, and a reference to a global that is no constructor is none: `f :: forall a. a -> a; f = id` is `Λ a. id [a]`, which Core refuses. **A body whose evaluation can move under a λ without any observable difference, and whose type is a function, is η-expanded once**:

```text
Λ ā. e   ⟹   Λ ā. λ (x : A). e x
```

- The forms that may move are value forms, variables, globals, their type and constraint applications, constructor spines whose arguments all may move, and such a form under a wrapping fit. None performs, faults, diverges, or reads a cell.
- Only the wrapping fits of `e` are rebuilt, against the ambient row of the new λ. A cell reference is no form that may move, so no demanding fit is moved.
- **The initialization dependencies of `e` are judged before it is expanded and kept after it.** A reference that `e` makes immediately to a member of the group being initialized stays immediate after the expansion, and is judged by the rule for recursive bindings: `f :: forall a. a -> a; f = f` is not made a recursive function by being expanded.
- A body that is no such form is not expanded; a parameter is asked for, since moving an application under a λ would change when it faults or diverges.
- A top-level declaration without a signature is expanded by the same rule, so that `g = id` is generalized.

### Computation declarations

| | Value declaration | Computation declaration `x :: ∀ā. C => τ / ρ` |
| --- | --- | --- |
| Signature | optional | required |
| Core scheme | the written or inferred type | `∀ā. C => Unit -{ρ}-> τ` |
| Body | checked at `()` | wrapped in `λ (_ : Unit)` and checked at `ρ` |
| Generalized | as above | never |
| A reference | instantiated | instantiated, applied to `Prim.Unit`, and fitted on its function side |

**Forcing a computation at a top-level value's right-hand side**, where `()` is ambient, succeeds where its row is `()`. A computation with a row that is not empty is a row mismatch where the value has no signature, the right-hand side then being an inference position; where it has one, the right-hand side is a [checking boundary](#explicit-checking-boundaries) at `()`, and a unique plan of implicit handlers taking the row to `()` forces it.

### Explicit checking boundaries

**A position whose expected row an annotation or a signature fixes is a boundary**:

| Boundary | Expected row `ρ` |
| --- | --- |
| a λ checked against an arrow an annotation or a signature writes | the arrow's row |
| a computation declaration's body | the row its signature writes |
| the right-hand side of a top-level value declaration with a signature | `()`, the ambient row of every top-level value |

**Opening the boundary creates a fresh ambient row `?σ`**, which every fit inside the body takes as its target. The body is built under it, and **closing the boundary, once the body is built, makes it a job** ([Elaborator API](03-Elaborator-API.md#checking-boundaries-and-implicit-handlers)), owned by the attempt that built the body. The compatible union of what the fits inside need, shared tails kept as one, is the body's complete source row `U`; the job waits before deciding only where that union cannot be formed uniquely. It then decides `fit(U, ρ)`, which cancels the keys and tails `U` and `ρ` share first: `( Console | ?e )` against `( LiftIO | ?e )` is decided at once.

| `fit(U, ρ)` | The boundary's job |
| --- | --- |
| Equal or Widen | solved with no handler: `?σ := ρ`, and every fit inside is decided again against `ρ`; nothing is placed at the boundary |
| a definite row mismatch | `?σ := U`, and the body is fixed at `U`; a plan is sought over the complete difference, and the job is solved recording it, applied as [Effect Handlers](02-Effect-Handlers.md) lowers it, or fails where there is none or several |
| undecided after the shared tails cancel | postponed on the flexible tails left, `?σ` unassigned |

**The resolution of fits takes the boundary's fits against `ρ` in place of the fits inside.** Neither rule solves `?σ` or takes a fit targeting it. A waiting boundary contributes `fit(U, ρ)` where `U` is formed and `fit(Sᵢ, ρ)` for each source `Sᵢ` where it is not; only the assignments they make are kept, and `U` is then decided against `ρ` once. A body calling instantiated `( Console | ?t1 )` and `( Clock | ?t2 )` under a signature at `( Console, Clock | e )` is decided by rule 2, `?t1 := ( Clock | e )` and `?t2 := ( Console | e )`, and then by the first branch. Distinct flexible tails rule 2 does not reach are left an ambiguous effect row.

A boundary job still pending when its declaration is generalized keeps the declaration from being committed. A position whose row nothing fixes — a λ with no expected type, the right-hand side of a top-level value without a signature — is no boundary, and inserts nothing.

## The surface elaborator

**The surface elaborator is the host's**, and builds Core⁺ from the Surface AST on the mechanism above directly, without the handles and requests a guest uses ([Elaborator API](03-Elaborator-API.md)). What it builds carries the Surface AST's origins as its annotations, through to the Core it becomes, and every site it creates carries the node it stands for, so a failure is reported where it was written.

### A signature's type

**A kind left unwritten is a kind metavariable**, and the type is read with an equation for every kind it stands at: a type constructor at an instance of its kind scheme, each kind variable of the scheme a fresh metavariable; an application at the arrow its head must be, the result a fresh metavariable; and an arrow's two sides and a `forall`'s body at `Type`. A kind equation is decided where it is met ([Kind unification](#kind-unification)), so reading a signature leaves nothing waiting on a kind.

**A type variable is introduced only at a quantifiable kind.** A kind written on a binder is checked to be one, and refused at the binder otherwise. A kind left unwritten — an implicitly quantified variable's, a binder's, a kind argument of a constructor's scheme — is a metavariable carrying `Quantifiable`, so a solution that is no quantifiable kind is refused where it would be assigned.

**Every kind left unwritten is asked after once the elaboration it belongs to is done**, and each place still holding an undetermined one is reported once: a binder where it stands, an implicitly quantified variable where it is first mentioned, and a type constructor whose kind arguments nothing decided where it is written — `T` at `forall k. Type`, its `k` mentioned nowhere else, decides nothing of `k`. A metavariable none of these accounts for is reported where the signature's type stands, so a signature that is not made a scheme is always reported somewhere. Only then is the signature a Core scheme.

**A row is read in the bracket it is written in.** A record's row and a variant's are read at `Row Type`, each element's payload at `Type` under its key — a label's `SymbolKey`, a tag's `TagKey` — and the type is `Prim.Record` or `Prim.Variant` of the row. A tuple of `n` components is the record of `PositionKey 0` to `PositionKey (n - 1)`, the components at those positions. An effect row is read at `Row Effect`: an element is its effect applied to its arguments, keyed by the effect, and an instance `s :: E τ̄` is the same application keyed by `SymbolKey s`. **An effect applied to its arguments is kinded as an application** of something at the arrow of its parameters' kinds into `Effect`, so each argument is read at the kind its parameter is declared at, and an effect applied to more or to fewer arguments than it has parameters is a kind equation that fails where the argument, or the application, stands. An arrow carries the row `/` writes on it, read at `Row Effect`, and is pure where none is written.

**A spread joins the row it names to the row written around it.** `...τ` is read at the row kind of its bracket, and a row is its elements over the union of the rows it spreads, so `{ name :: String, ...r }` is `( name : String | r )` and `{ ...r, ...s }` is `r ⊎ s` ([Rows](../03-Typed-Core/02-Rows.md)). A row holding one key twice through what it spreads, and one spreading a row variable twice, are refused where the row stands.

**`...` alone is a variable the signature quantifies implicitly**, one per row kind, so every `...` of one kind in a signature is the same row. It is named apart from every name source can write, and is quantified with the signature's other implicit variables, all of them in the order they are first mentioned. Nothing but a signature quantifies one: `...` alone in an annotation, in a field, or in a synonym's body is refused where it stands.

**What a row's sharpness needs is carried by the binder of its variables.** A row is sharp only where each key it holds is absent from each row variable it spreads, and the row variables it spreads are apart, which is what `⊎` asks of what it joins. Each such condition is an **atom**, `k ∉ r` or `r # s`; the atoms of a type are normalized, each once and in one order, and the author writes none of them. **An atom stands directly under the innermost binder that binds a variable it is about**, a `forall` written in the type or one of the signature's implicit quantifiers:

```text
forall r a. { x :: Int, ...r } -> a          forall r. x ∉ r => forall a. Record ( x : Int | r ) -> a
(forall s. { a :: Int, ...s } -> Int) -> Int    (forall s. a ∉ s => Record ( a : Int | s ) -> Int) -> Int
```

**An atom about no variable the type binds is about one bound around it.** An annotation requires it where the annotation stands, from what the context assumes, once every part of the annotation is read, so a form outside what this version reads is reported before anything is required of the row around it. A data type's field refuses it ([A module's type declarations](#a-modules-type-declarations)).

**A type operator is what it names, applied to its two operands.** One naming a type constructor is that constructor applied to them. One naming a type synonym is the synonym applied to them, its operands its first two arguments. Where an element of an effect row stands, one naming an effect is held by resolution as that effect applied to its operands ([Surface AST](08-Surface-AST.md)); anywhere else it stands where a type does, and an effect is no type, so it is reported where the operator is written.

**A type synonym is expanded where it is used, its whole spine of applications read at once.** Applications are not judged one at a time: the whole spine is collected first, and the use is refused, where the application stands, only when that spine supplies fewer arguments than the synonym has parameters, so `S a b` under a synonym `S` of two parameters is one use of it, and `S a` is not refused on the way. Its parameters are replaced by as many arguments, each read at its parameter's kind, the synonym's kind variables instantiated afresh at each use as a type constructor's are; the arguments beyond its parameters are applied to what it stands for. A `forall` of what it stands for binding a name an argument mentions free is renamed, so no argument is captured. **The synonyms read are those the modules the header reaches declare**, as their interfaces hold them: a synonym's body there has every synonym in it expanded already, so expanding a use reaches no other synonym ([Modules](../06-Modules/01-Modules.md)). What a synonym stands for is read like any other type, a row it stands for spread into another as a row written there would be.

**A synonym whose body spreads a parameter into a row beside a key or another row needs a condition of the row it is given**, and a synonym carries none ([Open Questions](../99-Open-Questions/01-Open-Questions.md)); a use of one is outside what this version reads. A name the body binds again in a `forall` is that `forall`'s, and so is what its row needs: `forall e. Unit -> Unit / {| Console, ...e |}` under a parameter `e` extends no parameter.

**A synthesized argument on a signature's spine is read as the type of its dictionary**, behind the pure arrow it stands behind, and marked where it stands; a computation declaration's signature, `forall ā. C => {{ … }} -> τ / ρ`, is read as the Core type it is, its spine and then `Unit -{ρ}-> τ`, and marked as a computation. **The scheme an interface publishes is read off the Core scheme and those marks**: each quantifier and constraint as it stands, each marked arrow a synthesized parameter holding its dictionary's type, its name, and its synthesizer, and a computation's thunk the computation it is ([Modules](../06-Modules/01-Modules.md)). A value without either publishes its Core scheme as it is.

**This version reads a subset of types**: type variables, type constructors, applications, arrows with the row they carry, `forall`, kind annotations, tuples, rows and the rows they spread, the type synonyms the imports and the module declare, and type operators naming a type constructor or such a synonym. A spread row is taken apart as it is read, into the empty row, elements over a row, unions, and row variables. A spread whose row cannot be taken apart that way (a type variable applied to arguments, for example), a constraint, a synthesized argument anywhere but the spine, a wildcard, and a typed hole are reported as outside it where they stand, and each stands meanwhile as a fresh metavariable, so what surrounds it is still read; a form resolution already reported is not reported again.

### A value declaration's body

**A body is checked against its declaration's scheme, opened along its spine.** Each quantifier is opened by a type abstraction and each constraint by a constraint abstraction, the constraint assumed in what it encloses, and each parameter the definition writes is bound by a `λ` at the argument type of the next arrow. Quantifiers and constraints are opened in front of the first parameter and wherever parameters remain, so a `forall` after a parameter is opened where it stands; one left once every parameter is bound is the body's to meet. **A synthesized argument is a parameter like any other here**, the dictionary bound by the next parameter the definition writes, `{{ d :: …}}` binding nothing ([Modules](../06-Modules/01-Modules.md)):

```text
f :: {{ d :: D by make }} -> (forall a. a -> a)
f d x = x                                         λ d. Λ a. λ (x : a). x
```

**Checking is bidirectional, under an ambient row** ([The judgement and the ambient row](#the-judgement-and-the-ambient-row)): the right-hand side of a declaration with a signature is a checking boundary at `()` ([Explicit checking boundaries](#explicit-checking-boundaries)). An application infers its function and checks its argument at the arrow the function's type must be — a type that is no arrow yet is equated with an arrow of fresh metavariables, its row an inference row — and fits the row the function performs into the ambient row, a wrapping fit around the function. A local has the type its binder gave it. A global or a constructor is instantiated: each kind variable of its scheme becomes a fresh kind metavariable carrying `Quantifiable`, each `forall` a type application to a fresh type metavariable — an instantiation row for a quantifier at `Row Effect` — and each constraint a constraint application, the constraint required where the global stands. A literal has its literal type. An annotation is read at `Type` under the type variables of the signature around it, and its expression checked against it. A `λ` is checked against the type expected of it opened along its spine as a definition's is: quantifiers and constraints opened in front of its first parameter and wherever parameters remain, so `\x y -> y` checked against `A -> (forall b. b -> b)` is `λ x. Λ b. λ y. y`. **Where the expected type comes from decides the row its body is under**: an arrow a signature or an annotation writes, and every arrow reached by opening its quantifiers, constraints, and parameters, is a checking boundary at the arrow's row; one instantiation or inference gives is ambient as it is. A `λ` whose type is not known where it stands is inferred, each parameter at a fresh type and its body under a fresh inference row. **A form that is only inferred is subsumed by what is expected**: where both are arrows once zonked, their arguments and their results are equated and the inferred row is fitted into the expected one, a wrapping fit around the form; anything else is an equation of the two types.

**Every equation is stated where the node it is about stands**, and is decided at once where it can be. One that cannot be decided yet becomes an equality job and the body goes on ([Elaborator API](03-Elaborator-API.md#an-equation-the-surface-elaborator-cannot-decide-yet-becomes-a-job)).

**This version elaborates a subset**: locals, globals, constructors, literals, application, `λ` over variables, and annotations. A checking boundary whose body performs what the row expected of it cannot hold asks for an implicit handler, which this version does not seek: it is reported as outside the subset where the boundary stands, rather than as a mismatch the language may resolve. A reference to a value whose scheme takes a synthesized argument, from the module or from an import, is outside it, a goal being what supplies the argument. A parameter that is no variable, and every other form, are reported as outside it where they stand, and the declaration holding one is not elaborated further.

### A module's type declarations

**A module's type declarations are elaborated before any of its values** — its data types, newtypes, type synonyms, foreign types, and effects — **and every head before anything a head names.** Each head is read first: a data type's or a newtype's parameters, each at the kind written or at a kind metavariable, and the kind the declaration writes for itself, where it writes one, equated with the kind they give it — the parameters' kinds to `Type`; a synonym's parameters and the kind of what it stands for; a foreign type's kind; an effect's parameters. Then each synonym's body, at the kind its head gives what it stands for — `Type`, a row kind, or any other, `type Effects = {| Console |}` among them — and then each constructor's fields and each operation's types, at `Type`, each under its declaration's parameters. Each is read with every head of the module in scope, so a declaration may name one written after it, and declarations referring to one another — `data A = MkA B` and `data B = MkB A` — are read together, their kinds decided by the same equations. A newtype is read as the data type of one constructor of one field it is, marked as a newtype.

**A head is read at the kind its declaration is being given.** A kind variable the declaration writes, wherever in it it is written — on a parameter, `k` in `data Proxy (a :: k) = Proxy`, on the declaration, or in a field, `data Poly = Poly (forall (f :: k -> Type) (a :: k). f a -> f a)` — is the declaration's own, and each use of the type instantiates it afresh, so `Proxy Int` and `Proxy List` may stand in one module. A metavariable standing for a kind left unwritten is one kind, shared by the head and every use of it while the declarations are read.

**A synonym's body is read after the bodies of the synonyms it is written in terms of.** The module's synonyms are taken in the strongly connected components of the references their bodies make to one another, directly or through a type operator. A synonym defined in terms of itself, directly or through others, is reported where it is declared, each member of a cycle once, and none of them is read; a use of one, or of a synonym whose body did not read, is reported where the use stands, once, and a synonym only depending on a cycle is not reported as a member of it. A body that spreads a parameter into a row beside something else needs a condition of the row it is given ([Open Questions](../99-Open-Questions/01-Open-Questions.md)), and the synonym is refused where it is declared. A synonym read is expanded where it is used as an imported one is ([A signature's type](#a-signatures-type)), and the module's values are read through it.

**A field's rows need no condition of a parameter.** A row in a field spreading a parameter needs it to lack the keys the row holds beside it, and to be apart from the other row variables it spreads; a constructor's type, `forall k̄. forall ā. τ̄ -> T ā`, carries no constraint, so the field is refused where the row stands — `data R r = R { name :: Int, ...r }` among them. A row variable a `forall` of the field binds carries its atoms there, so `data P = P (forall s. { name :: Int, ...s } -> Int)` is admitted.

**A foreign type stands at the kind it writes**, over the kind variables it writes, held where it is declared to what a type constructor's kind is: its domains are kinds a type variable may stand at, and it produces `Type`. `foreign type E :: Effect` and `foreign type F :: Effect -> Type` are refused there ([Foreign Types](../../proposals/06-Foreign-Types.md)).

**An effect's head is its parameters**, read with the other heads, so a row of the module's declarations may name an effect it declares, wherever declared; its operations are read with the fields, under the effect's parameters and each operation's own type variables, their arguments and the type each resumes with at `Type`. **An effect has no kind scheme** (D3, D24): its parameters and an operation's own type variables stand at kinds that mention no kind variable, and one whose kind nothing decides must be written — unlike the present limit on data declarations, this is no limit of the version: an effect has nothing to generalize a kind into, now or later. A kind variable an operation writes, on a variable of its own or inside its types, refuses the operation where it is declared, before anything is read of it, so no equation of the kind variable stands in the way of saying so; an effect whose head is refused is refused whole, its operations not read, and a use of it is judged against no parameter, so nothing a use asks of a parameter is reported beside it. **An operation's types need no condition of the effect's parameters or of its own variables**, neither carrying one: a row in them needing one is refused where the row stands, and `...` alone, there being no implicit quantifier to stand for it, is refused likewise; a `forall` inside one of the types carries its own atoms. An operation written with other than one argument takes its arguments as Core's one: none is `Prim.Unit`, and several are a record of them, each under its position ([Effects](../03-Typed-Core/03-Effects.md)).

**A kind nothing decided is outside what this version elaborates.** `data App f a = App (f a)` says that `a` is at some `k` and `f` at `k -> Type`, and nothing of what `k` is: the language reads it as `App : forall k. (k -> Type) -> k -> Type`, generalizing the kind, and this version, which generalizes nothing, reports each parameter whose kind is left undetermined where it stands, its kind to be written — `data App f (a :: Type) = App (f a)`, which decides `f : Type -> Type` as well. A synonym's parameter, and the kind of what a synonym stands for, are held to the same: `type K f = f` asks for the kind of `f`. This is a limit of the version and no rule of the language.

**What the type declarations declare is the module's own.** The data types, the foreign types, and the effects with their operations are added to the signature the module's values are elaborated against, the constructors to that signature and to the catalog, and the synonyms to those the values' types are read through; nowhere else: the Core checker is given the signature of the imports, as for any module, with the module's foreign types besides, which no Core declaration produces, and the build environment never holds the module ([Modules](../06-Modules/01-Modules.md)). A constructor's tag is its position among its declaration's constructors. A type declaration whose head, kind, body, or fields do not elaborate leaves the module's values unread, a value naming its type having nothing to be read against. **An attribute on a synonym or on a foreign type is checked afterwards**, neither having a Core declaration to carry it, against the signature with every value and every foreign of the module at its scheme and every attribute declaration of the module ([A module's foreigns and attribute declarations](#a-modules-foreigns-and-attribute-declarations)), so a constant may name a value declared after it; one that does not check is reported beside what the values give, and the values are read all the same.

### A module's foreigns and attribute declarations

**A foreign's signature is read as a value's is**, with the values' signatures and settled with them ([A signature's type](#a-signatures-type)), and a foreign has no body. It enters the catalog as a foreign at its scheme, with the attributes written on it, so a body may apply one the module declares, wherever it is declared.

**What a foreign takes and gives must cross to the host** (D44), and its type decides how, where the foreign is declared ([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md#how-a-value-crosses)). Its quantifiers are looked through, and each argument of its spine and its result are classified: `Int`, `Number`, `Char`, `String`, and `Boolean` cross as the host's own, `Unit` as `unit`, a type headed by an intrinsic of the class opaque — a foreign type among them — as `opaque`, and a result `IO τ` as an action producing what `τ` crosses as. A data type, a record, a variant, a function, a type variable, a type under a constraint, an `IO` anywhere but the result, and `IO (IO τ)` are refused at the first part that is one — an argument, counted from one, or the result — and the foreign is reported where its name is declared. The classification reads the type and the signature it is declared against and nothing else, and what it gives is the signature a foreign manifest holds for the foreign (`Stella.Compiler.ForeignBoundary`).

**Every arrow of a foreign's type is pure** (D23), by the rule the Core checker holds a foreign to: an arrow of the spine whose row's normal form holds an element or a tail is refused at the argument it takes, and so is one anywhere a value passes through an argument or the result — an opaque type's arguments and a row element's payload among them, a constraint's own types aside — so the Core checker never later refuses a foreign the elaborator admitted on the ground of its purity. `Int -> Int / {| ...{||} |}` is pure, its row empty by its normal form; `Box (Int -> Int / {| Console |}) -> Int` under `foreign type Box :: Type -> Type` is refused at its argument.

**An attribute declaration's parameters are closed types at `Type`**, read with every type the module declares in scope and no free type variable, under an initially empty type-variable context — a `forall` the type writes binds its own, so `forall a. a -> a` is one — and each keyword parameter's default is the constant Core holds. A type holding a kind nothing decided — `T` at `forall k. Type` — is reported where the type stands, nothing being able to generalize it. That a default, and an attribute's arguments, are of their parameters' types is checked by the Core checker ([The Core module](#the-core-module)).

### A module's values

**Every signature is read before any body.** A declaration's scheme is what every other declaration refers to it at, so each signature is read as an attempt of its own and its kinds settled ([A signature's type](#a-signatures-type)); the schemes are then entered into the catalog beside what the imports publish, each value and each foreign with the attributes written on it. A body may refer to any value or foreign of the module, itself and those declared after it among them. **A value declaration needs a signature in this version**, a fixity gives Core nothing, and a computation declaration and a handler are reported as outside what it elaborates.

**Each body is elaborated as an attempt of its own.** A body that fails, or holds a form this version does not read, leaves nothing behind. What the bodies leave undecided stands as jobs, which the loop runs once every body has been elaborated, so an equation one body states may be decided by what another does. **Once the loop is quiescent, the fits left undecided are resolved by direction**, each declaration's apart ([Resolving fits by direction](#resolving-fits-by-direction)): a declaration whose effect rows nothing decides is reported where its undecided fits stand, an annotation asked for, and one the resolution refuses by its cause — a checking boundary its body cannot meet as outside the subset, as the boundary is wherever it is decided ([A value declaration's body](#a-value-declarations-body)). Then each body is zonked and made a Core term, and each place a type nothing decided stands is reported once.

**A body is a value only once everything stated for it holds.** The loop stops at the first failure ([Elaborator API](03-Elaborator-API.md#the-loop)), so where it stops is read per declaration, through the site of each job:

| Where the loop stops | Reported | Not a value |
| --- | --- | --- |
| a job refused | the diagnostic, which names the declaration of each site it holds — an assignment that broke an obligation may name two | each declaration it names |
| jobs left waiting on what nothing assigned | each of them, as undecided where it was stated | each declaration such a job belongs to |
| fuel run out | the job next to be retried, as undecided where it was stated | the declaration it belongs to |
| a refusal, or fuel run out, and another declaration with a job still waiting | that declaration, as left unchecked | that declaration |
| a defect | the defect | every declaration |

### The Core module

**The values are grouped by what they refer to.** The edges are the references each Core term makes to the module's own values, and each strongly connected component is a group: a recursive one — more than one member, or one referring to itself — becomes a `DeclRec`, any other a `DeclNonRec`. **The groups stand in a stable topological order**: each after every group it refers to, and among the groups that may stand next, the one holding the declaration written first. A declaration is placed by its ordinal in the module's list of declarations rather than by its range, since declarations a macro produces may share one. A group lists its members in that order too.

**A recursive group binds function values alone.** Core's `letrec` admits only `FunVal`s (D14), and the surface admits more: `fibAnd = Tuple "fib" \n -> … snd fibAnd …` initializes without reading what it is initializing ([Name Resolution](06-Name-Resolution.md)). How such a binding is judged and lowered is open ([Open Questions](../99-Open-Questions/01-Open-Questions.md)), so **this version reports a member of a recursive group that is no `FunVal` as a form it does not elaborate**, where that member is declared. This is no statement about the program: `fibAnd` and `n = n` are reported alike, and which of them the language admits is decided where the lowering is.

**A Core module is made only of a module with no error.** A module missing a declaration would refer to what it does not bind. The Core module imports what the module imports, in the order written, a module imported twice once, and exports each value it declares that is reached from outside — by its name, as a macro, or through an operator it exports — which is the rule its interface's arities are checked by ([Interface](../05-Backend/03-Interface.md#which-values-have-one)); a re-export reaches what another module declares and is no export of its Core. It declares the module's data types, its effects, its attribute declarations, and its foreigns before its values — a foreign at its scheme with its attributes, in no group of values — and exports each foreign reached from outside as a value is, each data type the module exports, with the constructors exported of it — `List` exports the type alone, and `List(..)` its constructors besides — and each effect it exports. A synonym and a foreign type have no Core declaration: their elaborated form is recorded in the Core part of the interface rather than in a Core declaration. The Core part holds a foreign's scheme as it holds a value's, and an attribute declaration at its parameters' types, their labels and defaults being the surface part's. Each binding carries the attributes written on its declaration. What the Core module is annotated with is where the module stands, a `DeclNonRec` where its declaration does, and a `DeclRec` where its first member does.

**The Core checker refusing the module is the elaborator's fault**, and reported as such, with one exception: an attribute's arguments are checked against its declaration by the Core checker alone ([Core Type Checker](../03-Typed-Core/07-Core-Type-Checker.md#what-it-verifies)), so an attribute whose arguments do not check is the author's, reported where its declaration stands — for a recursive group, where the group's first member does.

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
