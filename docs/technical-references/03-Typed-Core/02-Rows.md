# Rows

Rows are a first-class structure of the type system. Structural relationships between rows are discharged by a dedicated solver, not encoded as type class search.

## A row is a keyed set

Row theory concerns **keyed, unordered, duplicate-free collections**. Where a key comes from is not a concern of the theory.

| Structure | Key | Payload |
| --- | --- | --- |
| record | `SymbolKey`, the field name | the field's type |
| tuple | `PositionKey`, the component's index | the component's type |
| variant | `TagKey`, the constructor written with it | the payload's type |
| labelled variant | `SymbolKey`, the name written for it | the payload's type |
| effect | `EffectKey`, derived from the effect at the head | the effect application |
| labelled effect | `SymbolKey`, the instance name written for it | the effect application |
| region | `RegionKey ℓ`, the name of the `region` binder | the region name |

Seven structures, one theory (D16). What changes between them is which key constructor the elements carry and what a payload is; normalization, equality, and entailment run the same algorithm over all of them and branch on none of it.

**The table reads as the conventional interpretations, not as a restriction.** Kinding admits any structural key in a `Row Type`, so `Record ( #Ok : Int )` is well-kinded; which keys a structure uses is settled by surface syntax and the elaborator ([Kinds](01-Kinds-and-Types.md)).

**A key is always present, even where nothing is written.** A tuple's components are keyed by position because their types cannot tell them apart — `(Int, Int)` has two elements and no way to name either — and an effect's key is its constructor because the payload already carries it. "Unlabelled" means no symbol is written, never that no key exists.

### Structural and nominal

The key constructors divide once more, and this division the checker does see.

| | Keys | Identity decided by | Needs `Σ` |
| --- | --- | --- | --- |
| **structural** | `SymbolKey`, `TagKey`, `PositionKey` | the syntax itself | no |
| **nominal** | `EffectKey` | a declaration | yes |
| **bound** | `RegionKey ℓ` | the `region` binder in scope | no |

A `#Ok` written in one module and a `#Ok` written in another are the same key, and neither requires anything to have been declared. That is what lets an open variant be shared between modules that know nothing of each other.

An `EffectKey` is the opposite. `Console.Log` and `Audit.Log` are different effects whatever their names look like, and `perform State.get` can only be checked by reading `State`'s declaration for the operation's argument and resumption types. An undeclared effect key would leave a `perform` with no type and a handler with no set of operations to exhaust.

The two meet in a labelled effect, where **the key and the protocol come apart**.

```text
cache : State Int
```

Here `SymbolKey cache` identifies the instance within the row, while `State` decides which operations may be performed on it. Collapsing the two would lose one or the other.

A `RegionKey ℓ` is a third thing again: neither written nor declared, but **bound**. Its identity is the region name `ℓ` a `region` binder of the term introduces, so each region has a key of its own, and regions open at one point stand side by side in one sharp row (D16, D36). A cell is reached by naming its region together with its key, `readCell ℓ.k`, so nothing has to search a row to decide which region is meant. No syntax writes the key, so nothing but the `region` that binds `ℓ` puts `region ℓ` in a row or takes it out.

Sharing one theory does not mean sharing one notation.

## Sharpness

A row well-kinded in a consistent context never contains the same key twice (D4). Sharpness is what kinding establishes; type equality does not rest on it, comparing [canonical forms](#canonical-form) that every row has, sharp or not.

PureScript, following Leijen's scoped labels, admits `( a :: Int, a :: String )`. That choice makes row unification unitary, which is a real benefit. Stella nevertheless rejects it, because Stella has `⊎`.

With duplicates permitted, `⊎` is not commutative, and worse, the **position of known fields relative to an unknown tail** becomes significant.

```text
  ( k : Int ) ⊎ r     versus     r ⊎ ( k : Int )
```

Under scoped labels these differ once `r` turns out to contain `k`. `⊎` then has no normal form, and deciding row equality must wait for `r` to be instantiated — which defeats the goal of normalizing open rows without closing them.

With sharp rows, `⊎` is a disjoint union: commutative, associative, with unit `()`. A normal form always exists and no row variable need be closed. The price is managing Lacks constraints.

For effect rows, sharpness means that no **key** occurs twice, which is not the same as no effect occurring twice. `( Exn String, Exn Int )` is ill-kinded, both elements deriving the key `EffectKey Exn`; `( primary : Exn String, fallback : Exn Int )` is well-kinded, the two carrying different symbols. Writing the instance name is how one effect is used twice.

Koka-style languages permit duplicates in effect rows and use them for masking (`mask<exn>`), which needs an offset — which occurrence of the key — rather than a key. Stella has no masking in v0.1, and a labelled instance is what it offers instead.

## Constraints

Core has exactly two constraints.

```text
C ::= k ∉ ρ        ρ does not contain the key k
    | ρ1 # ρ2      ρ1 and ρ2 share no key
```

`k ∉ ρ` is equivalent to `( ent | () ) # ρ` for any element `ent` whose key is `k` — `( k : τ | () ) # ρ` at `Row Type`, `( E τ̄ | () ) # ρ` at `Row Effect`. It is kept as a separate form because the kinding rule for row extension uses it constantly.

### Entailment

The rules are **kind-independent**: a row element is an `ent` with key `key(ent)`, and the shape is the same at `Row Type` and `Row Effect`.

```text
  (C) ∈ Γ                    ────────────      ──────────
  ─────────                  Γ ⊨ k ∉ ()        Γ ⊨ ρ # ()
  Γ ⊨ C

  k ≠ key(ent)    Γ ⊨ k ∉ ρ               Γ ⊨ ρ1 # ρ2
  ───────────────────────────             ───────────────
  Γ ⊨ k ∉ ( ent | ρ )                     Γ ⊨ ρ2 # ρ1

  Γ ⊨ k ∉ ρ1    Γ ⊨ k ∉ ρ2                Γ ⊨ ρ1 # ρ3    Γ ⊨ ρ2 # ρ3
  ────────────────────────                ────────────────────────────
  Γ ⊨ k ∉ ρ1 ⊎ ρ2                         Γ ⊨ (ρ1 ⊎ ρ2) # ρ3

  Γ ⊨ key(ent) ∉ ρ2    Γ ⊨ ρ1 # ρ2
  ──────────────────────────────────
  Γ ⊨ ( ent | ρ1 ) # ρ2

  Γ inconsistent    Γ ⊢ C ok
  ──────────────────────────   ← ex falso
  Γ ⊨ C
```

`Console ∉ e` at `Row Effect` and `name ∉ r` at `Row Type` are derived by the same rules.

### Inconsistent assumptions

**An assumption need only be well formed, not satisfiable.** A type application checks only that its argument has the quantified kind, so it can substitute a row into a constraint abstraction and make what that abstraction assumes false:

```text
( Λ (r : Row Type). Λ (_ : name ∉ r). v ) [ ( name : Int ) ]
```

steps to an abstraction assuming `name ∉ ( name : Int )`. Refusing to form a context holding that assumption would leave the reduct with no type, so `C => τ` and `Λ (_ : C). v` ask `Γ ⊢ C ok` and nothing more, and `Γ, C` is formed whatever `C` says ([Typing Rules](05-Typing-Rules.md)). `e [•]`, which eliminates a constraint abstraction, still asks `Γ ⊨ C`, so an assumption that cannot hold is never discharged in a context where it does not already.

**A context whose assumptions are inconsistent entails every well-formed constraint, and that is the whole of ex falso.** It makes no unbound variable bound, no ill-kinded application such as `Int Int` well-kinded, and no kind mismatch a match. What it can do is satisfy a sharpness premise of kinding, because that premise is an entailment: under `name ∉ ( name : Int )`, `r ⊎ r` is well-kinded.

**Inconsistency is decided one assumption at a time.** Both constraints are negative, so the empty row satisfies whatever an assumption says of a row variable, and assumptions each satisfiable on their own are satisfiable together. An assumption is inconsistent exactly when its known keys contradict it:

```text
inconsistent( k ∉ ρ )      ⟺   k ∈ keys(ρ)
inconsistent( ρ1 # ρ2 )    ⟺   keys(ρ1) ∩ keys(ρ2) ≠ ∅
```

`keys(ρ)` is the set of keys of the canonical form of `ρ` ([below](#canonical-form)). `Γ` is inconsistent when one of its assumptions is. `r # r` is not inconsistent: it is satisfied by `()`. A positive constraint, were one ever added, would make the characterization depend on how assumptions interact, and it would have to be revisited.

**What a `region` binder records is not an assumption.** The facts `RegionKey ℓ ∉ t` it adds for the row variables bound before it are what freshness gives, as `Γ*` below sets out, and none is ever false; they are kept apart from what constraint abstractions assume, though entailment reads both.

**Constraints carry no run-time content.** Introduction and elimination appear in terms as `Λ(_ : C). e` and `e [•]`, and both are erased. This has nothing to do with dictionary passing: the row solver and the type class resolver are separate mechanisms (D5).

The Core type checker **re-derives** `Γ ⊨ C` for each `e [•]`. No proof term is carried. The derivation is comparison of canonical forms plus a scan of the context, and involves no search.

## Canonical form

**Every type has a canonical form, and type equality compares canonical forms.** Canonicalization is total: it is defined on every type, well-kinded or not, in any context, consistent or not.

```text
can( a )                  = a, a bound variable identified by the depth of its binder
can( T [[κ̄]] )            = T [[κ̄]]
can( τ1 τ2 )              = can(τ1) can(τ2)
can( forall (a : κ). τ )  = forall κ. can(τ)
can( C => τ )             = can(C) => can(τ)
can( () )                 = ⟪ ∅ ; ∅ ⟫
can( (ent | ρ) )          = ⟪ { key(ent) ↦ can(payload(ent)) } ; ∅ ⟫ ∪ parts(can(ρ))
can( ρ1 ⊎ ρ2 )            = parts(can(ρ1)) ∪ parts(can(ρ2))
```

A canonical row `⟪ P ; U ⟫` is a set `P` of pairs `k ↦ π`, a key with a canonical payload, and a set `U` of canonical tails. `can(C)` canonicalizes the rows of a constraint and keeps its form. `parts(c)` is `c` itself where `c` is a row and `⟪ ∅ ; {c} ⟫` otherwise, and `∪` is the union of both parts. Three rules make the form unique:

- **Equal pairs collapse.** `P` is a set, so `ρ ⊎ ρ` and `ρ` are one row. Two pairs of one key with different payloads stay apart; the form does not become undefined.
- **A row of no pairs and one tail is that tail.** `a ⊎ ()`, `() ⊎ a`, and `a` have one form.
- **A type that is no row is an opaque tail where it stands in one.** Canonicalization does not kind its input. A well-kinded row has only row variables in its tails, a row kind being produced by row syntax alone ([Kinds and Types](01-Kinds-and-Types.md)).

The payload is a type `τ` at `Row Type`, and at `Row Effect` an effect application `E τ̄` or, for a region, its name. The key is whichever of the five constructors the element carried, and `P` no more distinguishes them than a map distinguishes how its keys were spelled.

**Sharpness is not a property of the form.** Kinding establishes it, and on a row kinded in a consistent context `P` pairs each key with one payload, which is the finite map of the [sharp normal form](#sharp-normal-form). What the form does not assume is what keeps equality meaningful where sharpness is not given. `r ⊎ r ≡ r` holds because tails are a set; substituting `( x : Int )` for `r` gives `( x : Int ) ⊎ ( x : Int ) ≡ ( x : Int )`, which an equality defined through the finite map would leave without meaning. Rows stay keyed sets; no multiset is introduced.

Canonicalization terminates and its result is unique, provided `key(ent)` cannot change during it. Every key constructor is rigid for its own reason: a `SymbolKey` and a `TagKey` are written literals (D13), a `PositionKey` is fixed by where the element stands, an `EffectKey` comes from the constructor the element well-formedness rule requires at the head of a payload (D16), and a `RegionKey ℓ` carries a region name, which no instantiation replaces ([Kinds and Types](01-Kinds-and-Types.md)). **No key depends on a metavariable**, and that is the substance of both decisions.

### Equality

```text
Γ ⊢ τ1 ≡ τ2   ⟺   can(τ1) = can(τ2)
```

The right-hand side consults nothing of `Γ`. Equality is therefore decidable, **never requires closing a row variable**, and is stable under substitution with no premise: `τ1 ≡ τ2` gives `τ1[σ] ≡ τ2[σ]` whatever `σ` is, kinded or not. Union is idempotent, commutative, and associative under it, with unit `()`.

```text
can( ( name : String | r ) ⊎ ( age : Int ) )
  = ⟪ {name ↦ String, age ↦ Int} ; {r} ⟫
  = can( ( age : Int, name : String | r ) )

can( ( Console | e ) ⊎ ( State Int ) )
  = ⟪ {EffectKey Console ↦ Console, EffectKey State ↦ State Int} ; {e} ⟫
  = can( ( State Int, Console | e ) )

can( ( cache : State Int, counter : State Int ) )
  = ⟪ {SymbolKey cache ↦ State Int, SymbolKey counter ↦ State Int} ; ∅ ⟫
```

On sharp rows this is the comparison of normal forms: the same keys, equal payloads at each, and equal tails. Tails compare as sets. Order is irrelevant, so `r ⊎ s` and `s ⊎ r` are equal. Distinct row variables, however, are **not** identified.

```text
( name : String | r )   and   ( name : String | s )     are different rows
```

`r` and `s` are different type variables standing for different unknowns. Identifying them would force the following type to preserve the remaining fields, which is a stronger claim than it makes.

```purescript
forall r s. Record { name :: String, ...r } -> Record { name :: String, ...s }
```

The symbol `≡` serves two roles that should not be conflated.

| | Where | Subject | Character |
| --- | --- | --- | --- |
| Equality | Core type checker | rigid row variables only, since Core has no metavariables | a decision procedure; it identifies nothing |
| Constraint | elaboration | may contain metavariables | [unification](../02-Surface-Language/01-Elaboration.md) constructs a substitution |

`( name : String | ?r ) ≡ ( name : String | ?s )` is a constraint, not a question of equality, and unification solves it with a fresh `?t`, setting `?r := ?t` and `?s := ?t`. Unification produces a substitution that makes the rows equal; equality itself identifies nothing.

## Sharp normal form

A rule that reads the payload at a key reads it through the normal form of a sharp row.

```text
RNF ::= ⟨ F ; T ⟩

F : RowKey ⇀ Payload      a finite map
T : { RowVar }            a finite set of row variables
```

`nf(ρ) = ⟨ F ; T ⟩` is **defined where `can(ρ) = ⟪ P ; U ⟫` pairs each key with one payload and every tail is a row variable**: `F` maps each key of `P` to its payload and `T` is `U`. Kinding a row in a consistent context establishes both. On such a row it is computed as

```text
nf( () )              = ⟨ ∅ ; ∅ ⟩
nf( a )               = ⟨ ∅ ; {a} ⟩
nf( (ent | ρ) )       = ⟨ F ∪ {key(ent) ↦ payload(ent)} ; T ⟩   where ⟨F;T⟩ = nf(ρ)
nf( ρ1 ⊎ ρ2 )         = ⟨ F1 ∪ F2 ; T1 ∪ T2 ⟩                   where ⟨Fi;Ti⟩ = nf(ρi)
```

where a union of maps is defined when the two agree at every key they share, payloads being compared by `≡`.

**`F(k) = τ` exhibits a type.** A rule written so asks for a type `τ` whose canonical form is the one payload at `k`, which sharpness makes unique up to `≡`. Where a row is not sharp — kinded under an inconsistent assumption, which entails every sharpness premise — two payloads may stand at one key, and such a rule then has no `τ` to read.

`nf` is not what equality is defined by. Type equality compares canonical forms, which every type has.

## Deciding entailment

```text
Γ ⊨ C            where Γ is inconsistent

Γ ⊨ k ∉ ρ        ⟺   k ∉ keys(ρ),
                       ∀t ∈ tails(ρ). (k ∉ t) ∈ Γ*

Γ ⊨ ρ1 # ρ2      ⟺   keys(ρ1) ∩ keys(ρ2) = ∅,
                       ∀t ∈ tails(ρ1). ∀k ∈ keys(ρ2). (k ∉ t) ∈ Γ*,
                       ∀t ∈ tails(ρ2). ∀k ∈ keys(ρ1). (k ∉ t) ∈ Γ*,
                       ∀t1 ∈ tails(ρ1). ∀t2 ∈ tails(ρ2). (t1 # t2) ∈ Γ*
```

`keys(ρ)` is the set of keys of the pairs of `can(ρ)`, and `tails(ρ)` its set of tails. **A fact is about a canonical tail**, a row variable or an opaque one alike, and a tail meets a fact only when the two are the same canonical form. Of an opaque tail, which only an ill-kinded row holds, a fact comes from an assumption about it and from nothing else.

**Entailment is preserved by every substitution.** `Γ ⊨ C` gives `Γ[σ] ⊨ C[σ]`, with no kinding or admissibility premise on `σ`. What a substitution does to a tail it does on both sides: substituting `Int` for `r` turns `k ∉ r ⊨ k ∉ r` into `k ∉ Int ⊨ k ∉ Int`, and a fact restricted to row variables would lose it. Where the substitution brings a key into a tail, the assumption that gave the fact becomes inconsistent, and the context entails the constraint all the same.

`t1 = t2` is not excluded. `r # r` is satisfiable — it constrains `r` to the empty row — and an assumption entails itself, so a context assuming it must be able to discharge it. What makes `r ⊎ r` ill-kinded in an ordinary context is that nothing there derives `r # r`.

### `Γ*`: decomposing assumptions into atomic facts

The conditions above look for **atomic facts about tails** — `k ∉ t` and `t1 # t2` — whereas assumptions in `Γ` concern composite rows. Each assumption is decomposed over its canonical form.

```text
assumption (k ∉ ρ)      if k ∈ keys(ρ) the assumption makes Γ inconsistent
                          otherwise it yields  { k ∉ t | t ∈ tails(ρ) }

assumption (ρ1 # ρ2)    if keys(ρ1) ∩ keys(ρ2) ≠ ∅ the assumption makes Γ inconsistent
                          otherwise it yields
                            { k ∉ t | k ∈ keys(ρ1), t ∈ tails(ρ2) }
                            { k ∉ t | k ∈ keys(ρ2), t ∈ tails(ρ1) }
                            { t1 # t2 | t1 ∈ tails(ρ1), t2 ∈ tails(ρ2) }
```

The only closure added is symmetry of `#`. Since `Γ` is finite and each canonical form is finite, `Γ*` is finite and is constructed once.

Two binders change `Γ*` besides the assumptions.

**A type binder hides what was assumed of a variable it shadows.** A `forall` met while kinding is scoped lexically, and binding `a` again removes every atomic fact about a tail the outer `a` occurs free in: what was assumed of it says nothing of the inner one ([Kinds and Types](01-Kinds-and-Types.md)).

**A `region` binder adds facts that freshness gives.** A row variable bound outside `ℓ` cannot be instantiated with a row mentioning `ℓ`: wherever its instantiation is formed, `ℓ` is not in scope, and capture-avoiding substitution keeps it so. Entering the body of `region [ℓ]` therefore adds

```text
{ RegionKey ℓ ∉ t  |  t : Row Effect ∈ Γ }
```

for every row variable of kind `Row Effect` bound before `ℓ`. A row variable bound later, inside the body, gets no such fact; a function that abstracts over a row there and needs the key absent says so in its type, as for any other key. This is what lets a function polymorphic in its row be applied inside a region with no constraint written for it, and what makes the body's row `( region ℓ | ρ )` sharp ([Typing Rules](05-Typing-Rules.md)). A run-time region frame adds none, its residual row being closed ([Semantics](06-Semantics.md#run-time-forms)).

### What entailment does not derive

`Γ ⊨ C` is the finite, syntax-directed relation above, and the only closure `Γ*` computes is symmetry of `#`. It is **sound with respect to the set-theoretic reading of rows, and intentionally incomplete**: a constraint may hold of every row satisfying the assumptions without being derivable.

`r # r` is the clearest instance. It is admissible, and it restricts the instantiations of `r` to the empty row, yet it entails neither `k ∉ r` nor `r # s`; nor does type equality identify `r` with `()`.

Leaving that consequence out is not a matter of cost. `Γ*` could record which variables are known to be empty and consult that table, and deciding would remain a scan. The reason is that each such addition carries a further piece of the row semantics into the entailment relation, and this one widens the set of accepted programs very little. The question is worth reopening if a need for it is observed.

**Symmetry is a property of entailment, not of type equality.** `ρ1 # ρ2` and `ρ2 # ρ1` entail each other, yet `C => τ` is compared structurally, so the two are distinct types. Where a term of one is wanted at the other, `Λ (_ : ρ2 # ρ1). e [•]` adapts it. Admitting symmetry into type equality would raise the general question of whether mutually derivable constraints are the same type, which is a larger question than row theory settles.

There is no backtracking and no search order. This is the answer to the objection that instance chain search order becomes an accidental compile-time language.

## Diagnostics

A failed row constraint is reported by the row solver directly.

```text
  row constraint unsatisfied
    required : "name" ∉ r
    r is universally quantified at Example.stella:12:8
    no assumption gives "name" ∉ r
```

It does not appear as an instance resolution error. A failure that is a row problem is reported as a row problem.

## Why `Difference` and `Map` are not in Core

**`Difference ρ K`.** For an open row, `ρ - {k}` has no determinate meaning unless membership of `k` is known. Where `k` is a known field, the term-level `restrict` already covers it, with type `Record (k : τ | ρ) -> Record ρ`. A type-level `Difference` would be needed only to name the remainder of `ρ` while assuming `k ∈ ρ`, and that is an **equality constraint**, `ρ ≡ (k : τ | ρ')`. A `HasField k τ r` predicate is therefore not a new constraint in Core but the equation `r ≡ ( k : τ | r' )` for a fresh `r'`. The solver solves an equation, not a predicate.

**`Map f ρ`.** This requires type-level functions, whose introduction and termination are unsettled. Admitting computation of unknown termination into the trusted core is not compatible with the checker's self-contained character. Uses such as `Record (Map Maybe r)` are expressed for now with term-level residual evidence ([Elaboration](../02-Surface-Language/01-Elaboration.md)).

Both can be added later as type-level functions over `Row ε`. Adding them now would make row equality undecidable.

## Surface syntax: spread notation

This section describes convention rather than Core. It belongs with row theory because it is **common to every row kind**: if rows are one theory, they should have one notation.

### The common shape

A row literal is written as a set of elements. Brackets differ by kind; the contents obey the same rules.

```text
RowLit ::= open ent1 "," … "," entn close       (n >= 0)

ent ::= element                 written per kind
      | "..." ρ                 spreading a row
      | "..."                   anonymous spread
```

| Structure | Brackets | Element | Key it makes | Example |
| --- | --- | --- | --- | --- |
| record | `{` `}` | `s :: τ` | `SymbolKey s` | `{ name :: String, age :: Int }` |
| tuple | `(` `)` | `τ` | `PositionKey n`, from where it stands | `(Int, String)` |
| variant | `[` `]` | `'T :: τ` | `TagKey T` | `[ 'Ok :: Int, 'Err :: String ]` |
| labelled variant | `[` `]` | `s :: τ` | `SymbolKey s` | `[ ok :: Int, err :: String ]` |
| effect | `{\|` `\|}` | `E τ̄` | `EffectKey E`, derived | `{\| Console, State Int \|}` |
| labelled effect | `{\|` `\|}` | `s :: E τ̄` | `SymbolKey s` | `{\| cache :: State Int \|}` |

A tuple is written with at least two components and takes no spread, its keys being positions; `()` is `Unit` and not an empty tuple. An empty variant is `[]`. A tag is written `'Ok` in the surface and `#Ok` in Core ([Syntax](../02-Surface-Language/05-Syntax.md)).

Desugaring is `⊎` at every kind.

```text
{ name :: String, ...r }        ⟹  ( name : String ) ⊎ r
{ ...r, ...s }                  ⟹  r ⊎ s
{| Console, ...e |}             ⟹  ( Console ) ⊎ e
{| ...e, ...f |}                ⟹  e ⊎ f
{}  /  {||}                     ⟹  ()
```

`( name : String ) ⊎ r` and the row extension `( name : String | r )` share a normal form, so which one the desugaring chooses does not affect meaning; the Lacks constraint `name ∉ r` is the same either way.

`...` follows JavaScript's spread syntax. It does not make case distinguish roles, and it generalizes: **what is spread need not be a variable.**

```purescript
{ id :: Int, ...(Shape.fieldsOf t) }
{| Console, ...(Handler.effectsOf f) |}
```

`...τ` requires only that `τ` have the right kind. That generality belongs to `⊎` already; singling out variables would be arbitrary.

### Anonymous spread

The operand of `...` may be omitted, denoting an implicitly quantified row variable.

**Every anonymous `...` in one signature denotes the same variable, per kind.** Writing a name is what distinguishes separate variables.

This rule is what makes useful signatures expressible. Under a rule that generates a fresh variable per occurrence, none of the following can be written.

```purescript
-- record: "preserves the other fields" becomes inexpressible
setAge :: Int -> { age :: Int, ... } -> { age :: Int, ... }
-- forall r. age ∉ r => Int -> Record ( age : Int | r ) -> Record ( age : Int | r )

-- effect: a higher-order function's effect transparency becomes inexpressible
map :: (a -> b / {| ... |}) -> List a -> List b / {| ... |}
-- forall e. (a -{e}-> b) -> List a -{e}-> List b

-- handler: "remove this one, leave the rest" becomes inexpressible
runState :: (Unit -> a / {| State s, ... |}) -> s -> Tuple a s / {| ... |}
-- forall e. State ∉ e => (Unit -{ ( State s ) ⊎ e }-> a) -> s -{e}-> Tuple a s
```

The rule can instead be too strong, when two independent open rows are wanted.

```purescript
-- intended: two unrelated records
-- actual: forall r. a ∉ r, b ∉ r => Record ( a : Int | r ) -> Record ( b : Int | r ) -> Int
f :: { a :: Int, ... } -> { b :: Int, ... } -> Int
```

Names are written in that case (`...r` and `...s`). What matters is that the rule **never admits an incorrect program**: an over-strong signature fails at the call site rather than quietly meaning something else. A diagnostic should say that the anonymous spreads in a signature denote one row and that names separate them.

This limitation is met more often at `Row Type` than at `Row Effect`, because an effect row is a single ambient context for a computation whereas record arguments may be unrelated.

**Implicit binders belong to the outer spine of a scheme**, and never arise at a higher-rank position, where a quantifier must be written explicitly. The sharpness constraints of the rows may stand between them, each under the innermost binder of a variable it is about ([Elaboration](../02-Surface-Language/01-Elaboration.md#a-signatures-type)).

### Openness is visible in the syntax

Without `...` a row is closed; with it, open.

```purescript
exactly :: { name :: String } -> String              -- a record with only `name`
atLeast :: { name :: String, ... } -> String         -- `name` and possibly more

handleAll  :: (Unit -> a / {| Console |}) -> a        -- Console alone
handleSome :: (Unit -> a / {| Console, ... |}) -> a   -- Console and possibly more
```

In PureScript, whether a row is open or closed varies with the surrounding inference context. `...` settles it in the text of the signature. This, rather than brevity, is the notation's principal value.

PureScript's `{ name :: String | r }` is not adopted because `|` privileges the tail position: it cannot be written among the elements, cannot appear more than once, cannot spread anything but a variable, and cannot be omitted. `...` does all four.

### Nothing reaches Core

`...`, anonymity, implicit quantification, and the filling in of Lacks and Disjoint constraints all disappear during elaboration. Core sees only `⊎`, `forall`, `∉`, and `#`.

**Implicit sharpness constraints.** `{ name :: String, ...r }` is `( name : String ) ⊎ r`, which the kinding rules require `name ∉ r` for. That constraint is supplied implicitly, exactly as `forall` is, whether the spread is named or anonymous, and so is `r # s` for a row spreading two, `{ ...r, ...s }` being `r ⊎ s`. Each stands under the innermost binder of a variable it is about ([Elaboration](../02-Surface-Language/01-Elaboration.md#a-signatures-type)).

```purescript
logAll :: List String -> Unit / {| Console, ...e |}

-- implicitly
-- forall (e : Row Effect). Console ∉ e
--   => List String -{ ( Console ) ⊎ e }-> Unit
```

The author never writes a Lacks or a Disjoint constraint. The cost of sharpness is absorbed here.
