# Typing Rules

## Contexts

```text
Σ ::= global signature                         (kind schemes: §3.1 Kinds and Types)
        type constructors   T : forall k̄. κ
        data constructors   Ctor : forall k̄. σ   (with owning type, tag, arity, field types)
        effect declarations E (ā : κ̄) { op : σ }
        foreign             f : forall k̄. σ
        top-level values    M.x : forall k̄. σ

Γ ::= ·                 local context
    | Γ, k              kind variable; introduced only while checking a declaration
    | Γ, a : κ          type variable
    | Γ, x : τ          value variable
    | Γ, C              row constraint assumption

Δ ::= · | Δ, j : (τ̄) -> τ ! ρ              join point context
Ω ::= occurrence ⇀ τ                        occurrence context
```

There are four contexts because their **scoping rules differ in four ways**. Merging them would erase the differences.

| | Σ | Γ | Δ | Ω |
| --- | --- | --- | --- | --- |
| Contains | declarations | local bindings | join points | occurrence types |
| Populated by | a module's declarations and its imports | `λ`, `Λ`, `let`, `letrec`, `bind`; kind variables while checking a declaration | `letjoin` | `case` and `switch*` |
| Lifetime | fixed throughout checking of a module | grows at a binder, shrinks on leaving it | **discarded at a lambda** | within a decision tree only |
| Structure | an unordered table | ordered; later entries may refer to earlier ones | ordered | a map from occurrences |
| Names | fully qualified `M.x`, `T`, `M.Ctor` | local names `x`, `a` | join names `j` | not names but paths |
| Kind schemes | yes | no | no | no |
| On lookup | instantiates the kind scheme | taken as is | taken as is | taken as is |
| In judgements | implicit, omitted below | explicit | explicit | decision tree judgements only |

The distinction between `Σ` and `Γ` is the most basic.

`Σ` is a table of declarations, built from a module's top-level declarations and from the signatures of imported modules, and fixed throughout the checking of that module. The typing rules neither extend nor shrink it; they only look things up in it. That is why the judgements below omit it.

`Γ` is a sequence of local bindings. It grows on entering `λ`, `Λ`, or `let` and shrinks on leaving. It is ordered, and later entries may refer to earlier ones: `Γ, a : Type, x : a` is meaningful while the reverse order is not.

**`Γ, C` requires `C` to be satisfiable.** Writing it is a check and not only an extension: a constraint that contradicts itself, such as `k ∉ ( k : τ )`, forms no context, and no rule may assume one. Entailment reads `Γ` as a set of atomic facts about row variables and has no rule for an inconsistent context ([Rows](02-Rows.md)), so a context admitting one would let a term be typed from a premise nothing discharges.

The distinction is also the unit of **separate compilation**. `Σ` is what a module's interface publishes for other modules; `Γ` never crosses a module boundary. That only `Σ` carries kind schemes follows from instantiation occurring only when a declaration is referenced.

`Ω` is separate because an occurrence is not a variable. It is a path from a scrutinee, derived structurally as the tree is descended rather than introduced by a binder. It becomes a variable only by passing through `bind x = o`, at which point it enters `Γ`.

## Judgement forms

```text
Γ ⊢ κ kind                  kind well-formedness
Γ ⊢ κ qkind                 κ is a quantifiable kind
Γ ⊢ k key ε                 key well-formedness
Γ ⊢ τ : κ                   kinding
Γ ⊢ C ok                    constraint well-formedness
Γ ⊨ C                       constraint entailment
Γ ⊢ τ1 ≡ τ2                 type equality
Γ; Δ ⊢ e : τ ! ρ            term typing; ρ is the ambient effect row
Γ; Δ; Ω ⊢ dt : τ ! ρ        decision tree typing
Ω ⊢ o : τ                   occurrence typing
```

`ρ` is the range of effects a term's evaluation may produce. Pure constructs are typeable under any `ρ`. Constructs that produce effects require agreement with `ρ`. Containment on an arrow's effect row is never inserted automatically (D8).

## Basic rules

```text
  ──────────────────────────
  Γ;Δ ⊢ c : litType(c) ! ρ

  (x : τ) ∈ Γ       (M.x : forall k̄. σ) ∈ Σ   Γ ⊢ κ̄' qkind   |κ̄'| = |k̄|
  ─────────────────  ─────────────────────────────────────────────────────
  Γ;Δ ⊢ x : τ ! ρ    Γ;Δ ⊢ M.x [[κ̄']] : σ[k̄ := κ̄'] ! ρ

  Γ, x : τ1; · ⊢ e : τ2 ! ρ'
  ────────────────────────────────────────────   ← the body's effects go on the arrow
  Γ;Δ ⊢ λ(x : τ1). e : τ1 -{ρ'}-> τ2 ! ρ         ← Δ is discarded

  Γ;Δ ⊢ e1 : τ1 -{ρ}-> τ2 ! ρ    Γ;Δ ⊢ e2 : τ1 ! ρ
  ────────────────────────────────────────────────   ← the arrow's row equals the ambient row
  Γ;Δ ⊢ e1 e2 : τ2 ! ρ

  Γ ⊢ κ qkind    Γ, a : κ; · ⊢ v : τ ! ()    v is a value form
  ────────────────────────────────────────────────────────────
  Γ;Δ ⊢ Λ(a : κ). v : forall (a : κ). τ ! ρ

  Γ;Δ ⊢ e : forall (a : κ). τ ! ρ    Γ ⊢ σ : κ
  ─────────────────────────────────────────────
  Γ;Δ ⊢ e [σ] : τ[a := σ] ! ρ

  Γ ⊢ C ok    Γ, C; · ⊢ v : τ ! ()    v is a value form
  ─────────────────────────────────────────────────────
  Γ;Δ ⊢ Λ(_ : C). v : C => τ ! ρ

  Γ;Δ ⊢ e : C => τ ! ρ    Γ ⊨ C
  ───────────────────────────────   ← no proof term; the checker re-derives
  Γ;Δ ⊢ e [•] : τ ! ρ

  Γ;Δ ⊢ e1 : τ1 ! ρ    Γ, x : τ1; Δ ⊢ e2 : τ2 ! ρ
  ───────────────────────────────────────────────
  Γ;Δ ⊢ let x : τ1 = e1 in e2 : τ2 ! ρ

  Γ' = Γ, x1 : σ1, …, xn : σn
  each i:  vi is a FunVal   and   Γ'; Δ ⊢ vi : σi ! ()
  Γ'; Δ ⊢ e : τ ! ρ
  ──────────────────────────────────────────────────
  Γ;Δ ⊢ letrec { xi : σi = vi } in e : τ ! ρ

  Γ;Δ ⊢ e : τ1 ! ρ    Γ ⊢ τ1 ≡ τ2
  ────────────────────────────────   ← conversion is by equality; there is no subtyping
  Γ;Δ ⊢ e : τ2 ! ρ
```

`litType` assigns each literal its primitive type: an integer literal has type `Int`, a floating-point literal `Number`, a string literal `String`, a character literal `Char`, and `true` and `false` have type `Boolean`. A literal produces no effect, so it is typeable under any ambient row.

**`Unit` is not a literal.** `Prim` declares `data Unit = Unit`, so `Prim.Unit` is an ordinary data constructor of arity 0 and one `switchCtor` branch exhausts it. As a literal it would fall under `switchLit`, where a default is mandatory because literals cannot be exhausted. Surface syntax writes the value `()`; Core writes `Prim.Unit`.

**Substituting a type for a type variable is capture-avoiding and simultaneous**, as `τ[a := σ]` is meant: a `forall` binding `a` again leaves it alone beneath it, a `forall` binding a variable free in `σ` is renamed first, and `τ[ā := τ̄]` replaces every variable at once rather than one after another. Core gives no binder a name unique across a module — a scheme is instantiated at the variables of whatever term uses it — so neither condition can be left to the names chosen.

The rules for global names instantiate a kind scheme with `κ̄'`, which is **pure substitution**: `κ̄'` is written in the term, so the checker neither guesses nor searches for it. It verifies only that the arity matches and that each `κ'` is a quantifiable kind. Where a global name has an empty scheme, `[[]]` is omitted and the rule reads as `(M.x : σ) ∈ Σ`, which is the case for most of Core.

## Records and variants

```text
  ───────────────────────────
  Γ;Δ ⊢ {} : Record () ! ρ

  Γ;Δ ⊢ e1 : τ ! ρ    Γ;Δ ⊢ e2 : Record r ! ρ    Γ ⊢ k key Type    Γ ⊨ k ∉ r
  ─────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ extend k e1 e2 : Record ( k : τ | r ) ! ρ

  Γ;Δ ⊢ e : Record ( k : τ | r ) ! ρ    Γ ⊢ k key Type
  ──────────────────────────────────────────────────────
  Γ;Δ ⊢ select k e : τ ! ρ

  Γ;Δ ⊢ e : Record ( k : τ | r ) ! ρ    Γ ⊢ k key Type
  ──────────────────────────────────────────────────────
  Γ;Δ ⊢ restrict k e : Record r ! ρ

  Γ;Δ ⊢ e1 : Record ( k : τ | r ) ! ρ    Γ;Δ ⊢ e2 : τ' ! ρ    Γ ⊢ k key Type
  ──────────────────────────────────────────────────────────────────────────   ← the type may change
  Γ;Δ ⊢ update k e1 e2 : Record ( k : τ' | r ) ! ρ

  Γ;Δ ⊢ e1 : Record r1 ! ρ    Γ;Δ ⊢ e2 : Record r2 ! ρ    Γ ⊨ r1 # r2
  ───────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ merge e1 e2 : Record (r1 ⊎ r2) ! ρ

  Γ;Δ ⊢ e : τ ! ρ    Γ ⊢ k key Type    Γ ⊨ k ∉ r    Γ ⊢ r : Row Type
  ─────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ inject k e : Variant ( k : τ | r ) ! ρ

  Γ;Δ ⊢ e : Variant r ! ρ    Γ ⊢ k key Type    Γ ⊨ k ∉ r    Γ ⊢ τ : Type
  ─────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ weaken k [τ] e : Variant ( k : τ | r ) ! ρ

  Γ;Δ ⊢ e : Variant () ! ρ    Γ ⊢ τ : Type
  ────────────────────────────────────────
  Γ;Δ ⊢ absurd [τ] e : τ ! ρ
```

The rule above is what a row-polymorphic record merge amounts to. Written as a type, it reads:

```text
merge : forall (r : Row Type). forall (s : Row Type).
        r # s => Record r -> Record s -> Record ( r ⊎ s )
```

`merge` is a term constructor and not a global name, so that type describes the rule rather than declaring anything ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

`r # s` is a `C => τ`, not a dictionary argument, and disappears at run time.

## Effects

```text
  nf(ρ) = ⟨ F ; T ⟩      F(k) = E τ̄                ← the key selects the element
  ( op : forall (b̄ : κ̄'). σ ->* τ ) ∈ Σ(E)         ← the payload selects the protocol
  E's type parameters are ā
  Γ ⊢ σ̄ : κ̄'      Γ;Δ ⊢ e : σ[ā := τ̄][b̄ := σ̄] ! ρ
  ────────────────────────────────────────────────────
  Γ;Δ ⊢ perform k.op [σ̄] e : τ[ā := τ̄][b̄ := σ̄] ! ρ

  h = { handles ent ; return (x : α) -> e_r ; cl_i }     ← no region
  Γ ⊢ ( ent | ρ ) : Row Effect                      ← the element the handle removes
  Γ;· ⊢ e : α ! ( ent | ρ )                         ← inside handle the row grows
  payload(ent) = E τ̄                                ← the key selects it, the payload names E
  Γ, x : α; · ⊢ e_r : β ! ρ
  each i:  Σ(E).op_i = forall (b̄_i : κ̄_i). σ_i ->* τ_i
           σ_i' = σ_i[ā := τ̄]    τ_i' = τ_i[ā := τ̄]
           (b̄_i is bound by the clause; a handler must respect an operation's polymorphism)
           if cl_i = full op_i [b̄_i] (x_i : σ_i', k_i : τ_i' -{ρ}-> β) -> e_i
              Γ, b̄_i : κ̄_i, x_i : σ_i', k_i : τ_i' -{ρ}-> β; · ⊢ e_i : β    ! ρ
           if cl_i = fast op_i [b̄_i] (x_i : σ_i') -> e_i
              Γ, b̄_i : κ̄_i, x_i : σ_i'                    ; · ⊢ e_i : τ_i' ! ρ
  { op_i } = dom(Σ(E))    and the op_i are distinct   ← the clauses exhaust E's operations, once each
  ───────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ handle e with h : β ! ρ

  h = { handles ent ; cells [r] ( k̄ : σ̄ ) ; return (x : α) -> e_r ; cl_i }
  Γ ⊢ ( ent | ρ ) : Row Effect
  Γ;· ⊢ e : α ! ( ent | ρ )                         ← no region: the handled code reaches no cell
  payload(ent) = E τ̄
  the k̄ are distinct      |ē| = |k̄|      ι = ( k̄ : σ̄ )      Γ ⊢ ι : Row Type
  Γ ⊨ RegionKey ∉ ρ                                 ← the residual row carries no region
  r ∉ dom(Γ)                                        ← the binder is fresh, not shadowing
  Γ' = Γ, r : Type          ρ' = ( region r ι | ρ ) ← sharp by that entailment
  each j:  Γ;Δ ⊢ e_j : σ_j ! ρ                      ← initial values, before the handler stands
  Γ, x : α; · ⊢ e_r : β ! ρ                         ← outside the region; no cell is in scope
  each i:  Σ(E).op_i = forall (b̄_i : κ̄_i). σ_i ->* τ_i
           σ_i' = σ_i[ā := τ̄]    τ_i' = τ_i[ā := τ̄]
           if cl_i = full op_i [b̄_i] (x_i : σ_i', k_i : τ_i' -{ρ'}-> β) -> e_i
              Γ', b̄_i : κ̄_i, x_i : σ_i', k_i : τ_i' -{ρ'}-> β; · ⊢ e_i : β    ! ρ'
           if cl_i = fast op_i [b̄_i] (x_i : σ_i') -> e_i
              Γ', b̄_i : κ̄_i, x_i : σ_i'                      ; · ⊢ e_i : τ_i' ! ρ'
  { op_i } = dom(Σ(E))    and the op_i are distinct
  r ∉ ftv(β) ∪ ftv(ρ)                               ← nothing of the region outlives it
  ───────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ handle e with h @ ( ē ) : β ! ρ

  nf(ρ) = ⟨ F ; T ⟩      F(RegionKey) = region r ι      nf(ι) = ⟨ G ; T' ⟩      G(k) = σ
  ──────────────────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ readCell k : σ ! ρ

  nf(ρ) = ⟨ F ; T ⟩      F(RegionKey) = region r ι      nf(ι) = ⟨ G ; T' ⟩      G(k) = σ
  Γ;Δ ⊢ e : σ ! ρ
  ──────────────────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ writeCell k e : Unit ! ρ

  Γ;Δ ⊢ e : τ1 -{r1}-> τ2 ! ρ    Γ ⊨ r1 # r'    Γ ⊢ r' : Row Effect
  ─────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ openEff [r'] e : τ1 -{r1 ⊎ r'}-> τ2 ! ρ
```

That handlers are deep (D15) shows in the type of the continuation `k_i`: calling it returns under the same handler, so the result type is `β`, the result of the `handle`, and the ambient row is the one a clause stands at — `ρ` where the handler owns no region and `ρ'` where it does, the region being open on both sides of a resumption. A shallow handler would give `τ_i -{( ent | ρ )}-> α`.

A `fast` clause's premise names neither `k_i` nor `β`, and that absence is the whole content of the distinction (D28). Having no way to speak of the answer, such a clause cannot bypass the evaluation still to come in order to supply what the `handle` returns, and having no continuation it cannot invoke one zero or several times; its body is an ordinary computation at the residual row, of the type the continuation resumes with.

**There are two rules for `handle` and a handler takes one of them** (D36). Without `cells` the rule is what it always was, and a clause stands at `ρ`. With `cells` the operation clauses stand at `ρ'`, and **three rows come apart**.

| | Row | Why |
| --- | --- | --- |
| the handled computation | `( ent \| ρ )` | it may not reach the handler's cells |
| an operation clause | `ρ'` | it may |
| the return clause | `ρ` | it may not, so no cell reaches the answer |

The return clause's row is the point at which "an ordinary return hands back no state" stops being a convention. Typed at `ρ`, it has no region to name, and reduction closes the region in the same step that runs it ([Semantics](06-Semantics.md)). A `full` clause stands at `ρ'` and may copy a cell's value into the answer where it means to; what the rules withhold is the automatic return, not the ability.

**`ρ'` is sharp only under `RegionKey ∉ ρ`, and the rule requires it.** A handler polymorphic in its residual row cannot derive the absence of a region there, so the constraint is assumed — written in its type as any other is ([Kinds and Types](01-Kinds-and-Types.md)). What the premise rejects is a region opened where one is already open, which is what keeps `readCell` from having two regions to choose between.

`readCell` and `writeCell` read the region out of the ambient row. **Neither says which region**, and neither needs to: a row holds at most one. **`writeCell` evaluates to `Prim.Unit`.** A write is done for its effect on the region and has no result of its own to hand back; giving it the value written would let a use of that value be mistaken for a read. A clause that sets a cell and carries on binds the `Unit` like any other result, Core writing every binding out.

**`r ∉ dom(Γ)` is what lets an occurrence of `r` mean the region.** Core terms are unique up to α-equivalence, and every bound variable is renamed to be unique within its context ([Kinds and Types](01-Kinds-and-Types.md)); the rule writes the condition out because a region binder is where leaving it implicit costs the most. The layout `ι` is kinded under `Γ`, outside the binder, and then stands under it in `ρ'`: a binder shadowing an outer variable would draw that variable's occurrences in `σ̄` under the region, and would make the condition below read an outer variable of the same name as an escape. Under the premise neither can happen.

**`r ∉ ftv(β) ∪ ftv(ρ)` is the whole of the escape discipline.** Every way to reach a cell mentions the region: a closure over a `readCell` carries `ρ'` in its own arrow, and `ρ'` mentions `r`. The condition therefore keeps such a closure out of the answer type and out of the residual row. There is no cell handle to leak, a cell being named by a key rather than held as a value, so these are the only routes there are. This is what a rank-2 quantifier would enforce for a `runST`-shaped function; `cells` being a binder, a side condition enforces it directly.

**What the condition forbids is a reference into a region, not a region.** A term that carries the whole `handle … @ ( … )` — a closure over it, or a continuation an outer handler captured across it — carries the binder along with everything the binder scopes over, and its type mentions no `r` at all, that variable being bound within. Such a term is closed with respect to the region and may be passed anywhere; it is what the snapshot row of [Semantics](06-Semantics.md) describes. The condition is about references that would outlive what binds them, and those alone.

**The layout is a written sequence, and the type is a row.** `cells [r] ( k̄ : σ̄ )` fixes finitely many cells with distinct keys, which is what lets `ē` give one initial value each and what makes the region a finite map at run time. The `ι` of a `region r ι` **type** is an ordinary row and may have a tail, which is what a helper polymorphic over the rest of a region needs; only a layout is closed.

**What the rule establishes is about the clause, not about the program containing it.** The body may diverge, it may fault, and it may perform an operation of `ρ` whose own handler declines to resume, or resumes more than once and so runs the rest of the handled computation again ([Effects](03-Effects.md)). The two forms are otherwise alike, both binding the operation's own type variables `b̄_i` and both checked with `Δ` discarded ([Terms and Matching](04-Terms-and-Matching.md)).

`openEff` is required where a pure function is used in an effectful context.

```text
-- f : Int -> Int                        (pure)
-- to call f where g : Int -{( Console )}-> Int
g = λ(n : Int). (openEff [( Console )] f) n
```

The explicitness is the price of D8. The elaborator inserts it, so an author does not see it.

## Join points and decision trees

```text
  Γ ⊢ τ : Type    Γ ⊢ τ̄ : Type
  Γ, x̄ : τ̄; Δ, j : (τ̄) -> τ ! ρ ⊢ e1 : τ ! ρ      ← the root of e1 is in tail position
  Γ;      Δ, j : (τ̄) -> τ ! ρ ⊢ e2 : τ ! ρ
  ───────────────────────────────────────────────────
  Γ;Δ ⊢ letjoin j (x̄ : τ̄) : τ = e1 in e2 : τ ! ρ

  ( j : (τ̄) -> τ ! ρ ) ∈ Δ    each i: Γ;Δ ⊢ e_i : τ_i ! ρ    jump is in tail position
  ──────────────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ jump j (ē) : τ ! ρ

  each i: Γ;Δ ⊢ e_i : τ_i ! ρ        Γ;Δ; { s_i ↦ τ_i } ⊢ dt : τ ! ρ
  ────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ case (ē) of dt : τ ! ρ

  Γ;Δ ⊢ e : τ ! ρ                      Ω ⊢ o : τ_o    Γ, x : τ_o; Δ; Ω ⊢ dt : τ ! ρ
  ────────────────────────             ────────────────────────────────────────────
  Γ;Δ;Ω ⊢ leaf e : τ ! ρ               Γ;Δ;Ω ⊢ bind x = o in dt : τ ! ρ

  Ω ⊢ o : T σ̄       T is a data type, not an intrinsic one (§6.2 Prim and Base)
  each Ctor_i is a constructor of T, Ctor_i : forall ā. τ̄_i -> T ā
  the Ctor_i are distinct
  each i: Γ;Δ; Ω ∪ { o ! Ctor_i . j ↦ τ_ij[ā := σ̄] } ⊢ dt_i : τ ! ρ
  with a default:     Γ;Δ;Ω ⊢ dt_0 : τ ! ρ
  without a default:  {Ctor_i} exhausts the constructors of T
  ─────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ switchCtor o { Ctor_i -> dt_i } [default -> dt_0] : τ ! ρ

  Ω ⊢ o : τ_o       τ_o is a primitive type with literals
  the c_i are literals of τ_o and are distinct
  each i: Γ;Δ;Ω ⊢ dt_i : τ ! ρ
  Γ;Δ;Ω ⊢ dt_0 : τ ! ρ                          ← a default is mandatory
  ─────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ switchLit o { c_i -> dt_i } default -> dt_0 : τ ! ρ

  Ω ⊢ o : Variant r        nf(r) = ⟨F ; T⟩
  each k_i ∈ dom(F) and the k_i are distinct
  each i: Γ;Δ; Ω ∪ { o ? k_i ↦ F(k_i) } ⊢ dt_i : τ ! ρ
  with a default:     Γ;Δ; Ω ∪ { o ↦ Variant r' } ⊢ dt_0 : τ ! ρ
                      where nf(r') = ⟨ F ∖ {k_1..k_n} ; T ⟩
  without a default:  T = ∅ and {k_i} = dom(F)
  ─────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ switchKey o { k_i -> dt_i } [default -> dt_0] : τ ! ρ

  Γ;Δ ⊢ e : Boolean ! ρ    Γ;Δ;Ω ⊢ dt_1 : τ ! ρ    Γ;Δ;Ω ⊢ dt_2 : τ ! ρ
  ─────────────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ guard e dt_1 dt_2 : τ ! ρ

  Γ ⊢ ρ ≡ ( Partial | ρ' )    Γ ⊢ τ : Type
  ──────────────────────────────────────────────────  (derived; see §3.3 Effects)
  Γ;Δ;Ω ⊢ fail : τ ! ρ
```

**A handler writes the element it removes, not only its key.** The row being handled appears nowhere else in the term, so neither half of the element is recoverable from the other: a key does not name an effect, and the arguments `τ̄` are not determined by the clauses without first-order matching. What `Ω` and `Σ` give the rules is then a lookup rather than a search. Only `key(ent)` has meaning at run time; the payload is an annotation and erases.

### Occurrence typing

```text
  ( s_i ↦ τ ) ∈ Ω
  ───────────────
  Ω ⊢ s_i : τ

  ( o ↦ τ ) ∈ Ω                    ← a dispatch records what it takes apart
  ─────────────
  Ω ⊢ o : τ

  Ω ⊢ o : Record r    nf(r) = ⟨F ; T⟩    F(k) = τ
  ───────────────────────────────────────────────
  Ω ⊢ o . k : τ
```

`o ! Ctor . j` and `o ? k` are typed by the branch that established them and by nothing else: what a constructor or a variant carries is known only under the dispatch that selected it, so those paths reach `Ω` through `switchCtor` and `switchKey`. A record needs no such branch, having one element at every key of its row, so `o . k` is read off the type of what it projects from.

In the default branch of `switchCtor` and `switchLit` the occurrence context `Ω` is unchanged, because Core does not track the refinement "not one of the enumerated cases". Refinement happens only in the default branch of `switchKey`, where the occurrence takes the residual type `Variant r'`.

That branch is the term-level appearance of residual computation over an unknown tail: when `T ≠ ∅` the condition `{k_i} = dom(F)` cannot be met, so a default is required, and its type is the residual. An open variant cannot be enumerated by pretending it is closed.
