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
    | Γ, region ℓ : ι   region name, with its layout ι = ( k1 : σ1, …, kn : σn ), closed

Δ ::= · | Δ, j : (τ̄) -> τ ! ρ              join point context
Ω ::= occurrence ⇀ τ                        occurrence context
```

There are four contexts because their **scoping rules differ in four ways**. Merging them would erase the differences.

| | Σ | Γ | Δ | Ω |
| --- | --- | --- | --- | --- |
| Contains | declarations | local bindings | join points | occurrence types |
| Populated by | a module's declarations and its imports | `λ`, `Λ`, `let`, `letrec`, `bind`, `region`; kind variables while checking a declaration | `letjoin` | `case` and `switch*` |
| Lifetime | fixed throughout checking of a module | grows at a binder, shrinks on leaving it | **discarded at a lambda** | within a decision tree only |
| Structure | an unordered table | ordered; later entries may refer to earlier ones | ordered | a map from occurrences |
| Names | fully qualified `M.x`, `T`, `M.Ctor` | local names `x`, `a`; region names `ℓ` | join names `j` | not names but paths |
| Kind schemes | yes | no | no | no |
| On lookup | instantiates the kind scheme | taken as is | taken as is | taken as is |
| In judgements | implicit, omitted below | explicit | explicit | decision tree judgements only |

The distinction between `Σ` and `Γ` is the most basic.

`Σ` is a table of declarations, built from a module's top-level declarations and from the signatures of imported modules, and fixed throughout the checking of that module. The typing rules neither extend nor shrink it; they only look things up in it. That is why the judgements below omit it.

`Γ` is a sequence of local bindings. It grows on entering `λ`, `Λ`, `let`, or the body of a `region` and shrinks on leaving. It is ordered, and later entries may refer to earlier ones: `Γ, a : Type, x : a` is meaningful while the reverse order is not. Order matters for a region name in one more way: entering `region [ℓ]` records that every `Row Effect` variable already in `Γ` lacks `RegionKey ℓ` ([Rows](02-Rows.md)), and a variable bound after `ℓ` gets no such fact.

**`Γ, C` requires `C` to be well formed, not satisfiable.** A type application checks only the kind of its argument, so it may substitute a row that makes what a constraint abstraction assumes false: `( Λ (r : Row Type). Λ (_ : name ∉ r). v ) [ ( name : Int ) ]` steps to an abstraction assuming `name ∉ ( name : Int )`, which keeps the type of the redex only if such a context can be formed. A context whose assumptions are inconsistent entails every well-formed constraint ([Rows](02-Rows.md)), and that is the whole of ex falso: no unbound variable becomes bound and no ill-kinded type well-kinded. `e [•]`, which eliminates a constraint abstraction, still asks `Γ ⊨ C`, so an assumption nothing satisfies is never discharged where the context does not already entail it. The facts a `region` binder records are kept apart from what is assumed: they are what freshness gives, and none is ever false.

The distinction is also the unit of **separate compilation**. `Σ` is what a module's interface publishes for other modules; `Γ` never crosses a module boundary. That only `Σ` carries kind schemes follows from instantiation occurring only when a declaration is referenced.

`Ω` is separate because an occurrence is not a variable. It is a path from a scrutinee, derived structurally as the tree is descended rather than introduced by a binder. It becomes a variable only by passing through `bind x = o`, at which point it enters `Γ`.

### What `Σ` is held to

```text
Σ ok   =   Σ wf  ∧  Σ prim
```

**Every judgement below presupposes `Σ ok`**, kinding included, and so do conformance of a global environment and every safety statement of [Semantics](06-Semantics.md). The rules read constructors, foreigns, and the classes of intrinsics out of `Σ` and rely on what they find there; `Σ ok` is the one statement of what that is. A signature a module's declarations produce satisfies it by construction ([Modules](../06-Modules/01-Modules.md)). One assembled from interfaces is checked against it where it is assembled, rather than trusted to have arisen through declarations.

`Σ wf` holds when each of the following does.

**Names.**

- A global name is a constructor, a foreign, or a top-level value, and never two of these. `(M.x : forall k̄. σ) ∈ Σ` is defined only where exactly one of them classifies `M.x`. No precedence between the tables resolves a collision, so lookup cannot hide one.
- The operations of one effect have distinct names, each the name its signature is looked up by.

**Type constructors and effects.**

- Every `T : forall k̄. κ` has `κ` a quantifiable kind under `k̄` and nothing else, and `result(κ) = Type` ([Kinds and Types](01-Kinds-and-Types.md)).
- Every parameter of an effect has a quantifiable kind. Every operation `op : forall (b̄ : κ̄'). σ ->* τ` has `κ̄'` quantifiable, and `σ` and `τ` of kind `Type` under the effect's parameters and `b̄`.

**Data constructors.**

- A constructor's owner is a data entry, and a data entry lists exactly the constructors naming it as owner, each once.
- Where the owner is `T : forall k̄. κ1 -> … -> κm -> Type`, the constructor has exactly the scheme

  ```text
  Ctor : forall k̄. forall (a1 : κ1) … (am : κm). τ1 -> … -> τn -> T [[k̄]] a1 … am
  ```

  up to α-equivalence: the owner's kind variables, parameters at the owner's kinds with distinct names, pure arrows, and the owner applied to exactly those parameters. `τ1 … τn` are the fields `Σ` records for it, `n` is its arity, and the scheme is well kinded.
- Each recorded field has `·, k̄, a1 : κ1, …, am : κm ⊢ τi : Type` in its own right. Type equivalence relates ill-kinded types as well, `() ⊎ Int` to `Int` among them, so a well-kinded scheme does not make the fields it is equivalent to well kinded, and dispatch binds the recorded fields.
- The tags of one owner's constructors are distinct.

**Values and foreigns.**

- Every scheme `forall k̄. σ` has `·, k̄ ⊢ σ : Type`.
- Every arrow of a foreign's type standing where a value passes through is pure (D23), the payload of a row element included. A constraint carries no value, so the arrows inside one are not held to it.
- A foreign's type takes no type and no constraint after its last value: no `forall` and no `=>` stands on its spine after its last arrow, nor anywhere on it where it has no arrow (D49).

**A foreign is saturated by a value, or by its bare reference.** Erasure removes type and constraint applications and keeps value arguments ([Semantics](06-Semantics.md#erasure)), so an erased chain tells a saturated foreign from an unsaturated one by counting its values against the arity, and nothing else. Were a type argument to saturate one, the typed relation and the erased one would part where it is missing: `foreign make : forall a. a` makes the bare `M.make` a value, `M.make [Int]` the call, and `let x : forall a. a = M.make in 0` steps without calling `δ_make`, while its erasure `let x = M.make in 0` calls it, and faults where `δ_make` does. A β-step builds such a chain from a well-typed term, so no restriction on where a chain is written prevents it; the declaration is where it is ruled out. `forall a. Unit -> a` is what such a foreign is declared as instead.

**The exact shape of a constructor is what dispatch relies on.** `switchCtor` instantiates a constructor's fields at the type arguments of the occurrence it takes apart, and construction instantiates them at the arguments the scheme was applied to. The two agree only because the scheme's result is the owner applied to its own parameters. A constructor of `T : Type -> Type` declared `C : forall (a : Type). a -> T Int` breaks that: `C [String] s` has type `T Int`, and a branch taking it apart types the field at `Int` while the value carries a `String`. Under `Σ wf` a field obtained by dispatch is well kinded at the occurrence's own kind and type arguments, and `cursorΣ` may take every arrow of a constructor or a foreign to be pure ([Chains of a constructor or a foreign](#chains-of-a-constructor-or-a-foreign)).

`Σ prim` holds when `Σ` holds `Σ_Prim` exactly as [Prim and Base](../06-Modules/02-Prim-and-Base.md) fixes it, and holds nothing else under `Prim`:

```text
Prim.Function : Type -> Row Effect -> Type -> Type     intrinsic function
Prim.Record   : Row Type -> Type                       intrinsic record
Prim.Variant  : Row Type -> Type                       intrinsic variant
Prim.Int, Prim.Number, Prim.String, Prim.Char, Prim.Boolean : Type     intrinsic literal
Prim.IO       : Type -> Type                           intrinsic opaque
Prim.Unit     : Type                                   data { Prim.Unit }    Prim.Unit : Unit, tag 0, no field
attribute Prim.macro, attribute Prim.entrypoint, attribute Prim.elaborationOnly     no parameter
```

**No type constructor outside `Prim` has the class literal, function, record, or variant.** Each of those classes comes with a canonical form the rules build and take apart, a literal, a `λ`, a record, or a variant, and the canonical-forms argument progress rests on is stated for `Prim`'s types alone. A type of one of those classes declared elsewhere would have no canonical value, a foreign's result being an opaque value. Every other intrinsic is of the class opaque.

## Judgement forms

```text
Γ ⊢ κ kind                  kind well-formedness
Γ ⊢ κ qkind                 κ is a quantifiable kind
Γ ⊢ k key ε                 key well-formedness
Γ ⊢ τ : κ                   kinding
Γ ⊢ C ok                    constraint well-formedness
Γ ⊨ C                       constraint entailment
Γ ⊢ τ1 ≡ τ2                 type equality
⊢ Γ ok                      local context well-formedness
Γ ⊢ Δ ok    Γ ⊢ Ω ok        join point and occurrence context well-formedness
Γ; Δ ⊢ e : τ ! ρ            term typing; ρ is the ambient effect row
Γ; Δ; Ω ⊢ dt : τ ! ρ        decision tree typing
Γ; Ω ⊢ o : τ                occurrence typing
```

`ρ` is the range of effects a term's evaluation may produce. Pure constructs are typeable under any `ρ`. Constructs that produce effects require agreement with `ρ`. Containment on an arrow's effect row is never inserted automatically (D8).

A context is well formed when each entry is formed under the entries before it:

```text
               ⊢ Γ ok    Γ ⊢ κ qkind       ⊢ Γ ok    Γ ⊢ τ : Type       ⊢ Γ ok    Γ ⊢ C ok
  ⊢ · ok       ─────────────────────       ──────────────────────       ──────────────────
               ⊢ Γ, a : κ ok               ⊢ Γ, x : τ ok                ⊢ Γ, C ok

  ⊢ Γ ok                  ⊢ Γ ok    ℓ ∉ dom(Γ)    Γ ⊢ ι : Row Type
  ──────────              ──────────────────────────────────────────
  ⊢ Γ, k ok               ⊢ Γ, region ℓ : ι ok

  each ( j : (τ̄) -> τ ! ρ ) ∈ Δ:   Γ ⊢ τ̄ : Type    Γ ⊢ τ : Type    Γ ⊢ ρ : Row Effect
  ─────────────────────────────────────────────────────────────────────────────────
  Γ ⊢ Δ ok

  each ( o ↦ τ ) ∈ Ω:   Γ ⊢ τ : Type
  ──────────────────────────────────
  Γ ⊢ Ω ok
```

**Regularity.** If `⊢ Γ ok`, `Γ ⊢ Δ ok`, and `Γ;Δ ⊢ e : τ ! ρ`, then `Γ ⊢ τ : Type` and `Γ ⊢ ρ : Row Effect`; with `Γ ⊢ Ω ok` as well, the same holds of `Γ;Δ;Ω ⊢ dt : τ ! ρ`. **Every rule carries what this needs among its own premises.** A rule typing no subterm at its row asks `Γ ⊢ ρ : Row Effect`, a literal's and a variable's among them; a rule whose type no premise kinds kinds it, the annotation of a `let` and the answer type of a `handle` among them; and a dispatch that may have no branch asks both. A derivation therefore never leans on an induction hypothesis that a dispatch with no branch, or a `case` or a `jump` with no argument, does not supply. The checker kinds every row where it introduces one — a `λ`'s, a `handle`'s inner row, a region's body row — so every row it carries meets these premises already.

## Basic rules

```text
  Γ ⊢ ρ : Row Effect               (x : τ) ∈ Γ    Γ ⊢ ρ : Row Effect
  ──────────────────────────       ──────────────────────────────────
  Γ;Δ ⊢ c : litType(c) ! ρ         Γ;Δ ⊢ x : τ ! ρ

  (M.x : forall k̄. σ) ∈ Σ    Γ ⊢ κ̄' qkind    |κ̄'| = |k̄|    Γ ⊢ ρ : Row Effect
  ──────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ M.x [[κ̄']] : σ[k̄ := κ̄'] ! ρ

  Γ ⊢ τ1 : Type    Γ ⊢ ρ' : Row Effect    Γ, x : τ1; · ⊢ e : τ2 ! ρ'
  Γ ⊢ ρ : Row Effect
  ─────────────────────────────────────────────────────────────────   ← the row the λ writes is its arrow's
  Γ;Δ ⊢ λ(x : τ1) / ρ'. e : τ1 -{ρ'}-> τ2 ! ρ                            ← Δ is discarded

  Γ;Δ ⊢ e1 : τ1 -{ρ}-> τ2 ! ρ    Γ;Δ ⊢ e2 : τ1 ! ρ
  ────────────────────────────────────────────────   ← the arrow's row equals the ambient row;
  Γ;Δ ⊢ e1 e2 : τ2 ! ρ                                  a chain of a constructor or a foreign
                                                        has a rule of its own, below

  Γ ⊢ κ qkind    Γ, a : κ; · ⊢ v : τ ! ()    v is a value form    Γ ⊢ ρ : Row Effect
  ───────────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ Λ(a : κ). v : forall (a : κ). τ ! ρ

  Γ;Δ ⊢ e : forall (a : κ). τ ! ρ    Γ ⊢ σ : κ
  ─────────────────────────────────────────────
  Γ;Δ ⊢ e [σ] : τ[a := σ] ! ρ

  Γ ⊢ C ok    Γ, C; · ⊢ v : τ ! ()    v is a value form    Γ ⊢ ρ : Row Effect
  ────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ Λ(_ : C). v : C => τ ! ρ

  Γ;Δ ⊢ e : C => τ ! ρ    Γ ⊨ C
  ───────────────────────────────   ← no proof term; the checker re-derives
  Γ;Δ ⊢ e [•] : τ ! ρ

  Γ ⊢ τ1 : Type    Γ;Δ ⊢ e1 : τ1 ! ρ    Γ, x : τ1; Δ ⊢ e2 : τ2 ! ρ
  ──────────────────────────────────────────────────────────────
  Γ;Δ ⊢ let x : τ1 = e1 in e2 : τ2 ! ρ

  Γ' = Γ, x1 : σ1, …, xn : σn      each i:  Γ ⊢ σi : Type
  each i:  Γ'; · ⊢ ei : σi ! ()
  { x̄ = ē } is initialization-safe          ← each ei reads only x1 … xi-1
  Γ'; Δ ⊢ e : τ ! ρ
  ──────────────────────────────────────────────────
  Γ;Δ ⊢ letrec { xi : σi = ei } in e : τ ! ρ

**An initializer is checked under no join point**, `Δ = ·`, and out of tail position: one jumping
to a join point outside its group would leave the group half initialized. Its row is `()`, so
initialization has no effect to order beside what it reads ([Initialization Safety](10-Initialization.md)).

  Γ;Δ ⊢ e : τ1 ! ρ1    Γ ⊢ τ1 ≡ τ2    Γ ⊢ ρ1 ≡ ρ2
  Γ ⊢ τ2 : Type        Γ ⊢ ρ2 : Row Effect
  ─────────────────────────────────────────────────   ← conversion is by equality; there is no subtyping
  Γ;Δ ⊢ e : τ2 ! ρ2
```

**Conversion changes the type and the row together, and each only by equality.** It is not effect-row subtyping (D8): `ρ1 ≡ ρ2` relates rows with one canonical form, so a row is never widened by it, which takes `openEff` or `openEffC`. The targets are kinded because equality does not keep a kind: it relates ill-kinded types as well, `() ⊎ Int` to `Int` among them ([What `Σ` is held to](#what-σ-is-held-to)), so a conversion to an ill-kinded type would break regularity.

`litType` assigns each literal its primitive type: an integer literal has type `Int`, a floating-point literal `Number`, a string literal `String`, a character literal `Char`, and `true` and `false` have type `Boolean`. A literal produces no effect, so it is typeable under any ambient row.

**`Unit` is not a literal.** `Prim` declares `data Unit = Unit`, so `Prim.Unit` is an ordinary data constructor of arity 0 and one `switchCtor` branch exhausts it. As a literal it would fall under `switchLit`, where a default is mandatory because literals cannot be exhausted. Surface syntax writes the value `()`; Core writes `Prim.Unit`.

**Substituting a type for a type variable is capture-avoiding and simultaneous**, as `τ[a := σ]` is meant: a `forall` binding `a` again leaves it alone beneath it, a `forall` binding a variable free in `σ` is renamed first, and `τ[ā := τ̄]` replaces every variable at once rather than one after another. Core gives no binder a name unique across a module — a scheme is instantiated at the variables of whatever term uses it — so neither condition can be left to the names chosen. **Substituting a type into a term is capture-avoiding for region binders as well**: substituting `σ` for `a` under `region [ℓ]` renames the binder first where `ℓ ∈ frn(σ)`. That arises when a global's body is instantiated at a type mentioning a region of the caller, two binders of one name being possible across globals.

**Binder freshness is a well-formedness condition on the checker's input, not a rule of the language.** Core is a language of terms up to α-equivalence, and in it a term written with a shadowing binder is the same term as its renamed form. What the checker receives is a representation, and it requires that representation to follow the unique-binder convention for the binders of terms that bind a type-level name: no `Λ`, type binder of an operation clause, or `region` binds a name already bound where it stands, and the type binders of one clause are distinct. The checker rejects a representation that breaks it — `TypeBinderShadows` for a type binder, `RegionBinderShadows` for a region binder — rather than renaming it: elaboration generates fresh names, so such an input is an elaborator defect. Accepting it would let a type binder shadowing an outer variable be read with the wrong meaning, and a region binder shadowing an outer one make a reference to the outer region read the inner. Types are not held to the convention and are scoped lexically ([Kinds and Types](01-Kinds-and-Types.md)). Reduction keeps the convention: opening a region introduces a globally fresh name, and type substitution renames a binder it would capture ([Semantics](06-Semantics.md)).

The rules for global names instantiate a kind scheme with `κ̄'`, which is **pure substitution**: `κ̄'` is written in the term, so the checker neither guesses nor searches for it. It verifies only that the arity matches and that each `κ'` is a quantifiable kind. Where a global name has an empty scheme, `[[]]` is omitted and the rule reads as `(M.x : σ) ∈ Σ`, which is the case for most of Core.

## Chains of a constructor or a foreign

**A constructor or a foreign is applied through its application chain, and Core has no other form of the call.** `M.Cons [Int] 1 xs` is the global `M.Cons` under a type application and two applications, and reduction reads that same term ([Semantics](06-Semantics.md#chains-of-a-constructor-or-a-foreign)). The **spine view** decomposes such a term into its head, with its kind arguments, and its other arguments in written order:

```text
M.g [[κ̄]] α1 … αn         M.g a constructor or a foreign of Σ
α ::= [τ]  |  [•]  |  e     a type, a constraint, or a value argument
values(ᾱ)                   the value arguments of ᾱ, in order
```

The arguments come in whatever order the declared type calls for: a declared type may interleave quantifiers, constraints, and arrows, and nothing requires the erased arguments to precede the values. A type such as `Int -> forall a. a -> a` is therefore usable, with `[String]` supplied after the first value argument.

### The cursor

`cursorΣ` is a partial function that walks the **declared** type through the view, consuming one argument at a time. It performs no well-formedness checking.

```text
cursorΣ(M.g [[κ̄]] ᾱ)  =  ⟨ σ ; θ ⟩    σ is the unconsumed remainder of the declared type
                                       θ is the accumulated kind and type substitution
```

```text
cursorΣ(M.g [[κ̄]])         = ⟨ σ ; [k̄ := κ̄] ⟩    where ( M.g : forall k̄. σ ) ∈ Σ
cursorΣ(M.g [[κ̄]] ᾱ [τ])   = ⟨ σ ; θ[a := τ] ⟩    where cursorΣ(M.g [[κ̄]] ᾱ) = ⟨ forall (a : κ). σ ; θ ⟩
cursorΣ(M.g [[κ̄]] ᾱ [•])   = ⟨ σ ; θ ⟩            where cursorΣ(M.g [[κ̄]] ᾱ) = ⟨ C => σ ; θ ⟩
cursorΣ(M.g [[κ̄]] ᾱ e)     = ⟨ τ2 ; θ ⟩           where cursorΣ(M.g [[κ̄]] ᾱ) = ⟨ τ1 -{()}-> τ2 ; θ ⟩
```

It is undefined in every other case. At most one clause applies at each step, since the shape of the unconsumed declared type distinguishes them. The arrow the last clause consumes is pure: a constructor's arrows are pure by its exact scheme, and a `foreign`'s by D23, `Σ ok` holding both of every entry, an imported one included.

**A chain is saturated** when `cursorΣ(M.g [[κ̄]] ᾱ) = ⟨ σ ; θ ⟩` and the **unconsumed declared type `σ`** is not a `forall`, a constraint arrow, or a function type, so that no clause extends it. The test is on `σ`, not on `θ(σ)`. Substitution can introduce arrows that the declaration never called for, and treating those as argument positions would absorb arguments that do not belong to the global.

```text
foreign id : forall a. a -> a

M.id                       ⟨ forall a. a -> a ; id ⟩          expects a type
M.id [Int -> Int]          ⟨ a -> a ; [a := Int -> Int] ⟩      expects one value
M.id [Int -> Int] f        ⟨ a ; [a := Int -> Int] ⟩           saturated
```

The last line is saturated because the declared remainder is the variable `a`, even though `θ(a) = Int -> Int` is a function type. **A chain ends where it is saturated**, and an argument beyond is an ordinary application of what the chain returns: `M.id [Int -> Int] f 0` is the application of the chain `M.id [Int -> Int] f` to `0`, typed by the rule for `e1 e2`. `foreign make : forall a. Unit -> a` instantiated at a function type behaves the same way: `M.make [Int -> Int] Prim.Unit` is saturated, and an argument after it is applied to what the call returns. A constructor's declared result is `T ᾱ`, never an arrow, so nothing applies a saturated one.

**Arity is a static property of the declaration.** The number of value-argument positions is the number of arrows on the declared type's spine, which is what the cursor walks and what substitution never changes. **A chain is saturated exactly when it holds as many values as that**: the cursor passes every quantifier and constraint before an arrow to reach it, and `Σ ok` leaves none after the last arrow of a foreign, nor of a constructor, whose scheme ends in its owner. Erasure therefore keeps both: after type arguments are gone, a backend still calls `δ_f` with exactly that many run-time arguments, and at the point the typed relation does.

### Typing a chain

```text
  M.g a constructor or a foreign      Γ ⊢ κ̄ qkind    |κ̄| = |k̄|    Γ ⊢ ρ : Row Effect
  cursorΣ(M.g [[κ̄]] α1 … αn) = ⟨ σ ; θ ⟩    n ≥ 1    each αi well formed, as below
  ──────────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ M.g [[κ̄]] α1 … αn : θ(σ) ! ρ
```

An argument is well formed when, writing `⟨ σ' ; θ' ⟩` for the cursor **before** it is consumed:

| Argument | Condition |
| --- | --- |
| `[τ]` | `Γ ⊢ τ : θ'(κ)`, where `σ' = forall (a : κ). …` |
| `[•]` | `Γ ⊨ θ'(C)`, where `σ' = C => …` |
| `e` | `Γ;Δ ⊢ e : θ'(τ1) ! ρ`, where `σ' = τ1 -{()}-> τ2` |

**The value arguments stand at the ambient row of the whole chain.** An arrow the cursor consumes is pure, so the call itself performs nothing: building a constructor's value runs nothing it is given, and a saturated foreign steps to a value or a fault and performs no proper effect ([Semantics](06-Semantics.md)). What an argument's evaluation performs is bounded by the row ambient where the chain stands, as it would be beside any other pure form. The rule for `e1 e2` would instead ask the arrow's row `()` to be the ambient row, and an `openEff` per argument where it is not.

**Preservation needs the rule, and does not merely admit it.** A widened computation ends in `openEffC [ρ] v → v` ([Semantics](06-Semantics.md)), and where `v` is `M.Just [Int] 1` the term after the step stands at the widened row, which the rule for `e1 e2` does not type it at. The rule gives a chain of values every row, as a `λ` has every row.

**A chain's arrows are those of the declaration, and only a constructor's and a foreign's chains have the rule.** A top-level value's scheme may carry an effectful arrow, and its body is unfolded and evaluated as written ([Semantics](06-Semantics.md)), so a defined global is applied by the rule for `e1 e2`. The checker types a constructor's or a foreign's chain by this rule; one typed at `()` by the rules for application alone has the same type.

`openEff` is still what widens a pure **function value** — a variable, a `λ`, a defined global, or a chain passed where a wider arrow is expected — since the function's type, not the place it is applied, is what changes there.

## Records and variants

```text
  Γ ⊢ ρ : Row Effect
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
  Γ;Δ ⊢ inject k [r] e : Variant ( k : τ | r ) ! ρ

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

`r # s` is a `C => τ`, not a synthesized argument, and disappears at run time.

**An injection writes the row its variant holds besides its key**, as `weaken` writes the payload it adds and `absurd` the type it answers at. The type of `inject k [r] e` is therefore read off the term wherever it stands, a field of a record and a scrutinee among them; where a type is expected of it, `r` is the rest of that variant, and the payload is checked against the type that variant gives `k`. The variant of one element is `inject k [()] e`.

## Effects

```text
  Γ ⊢ ρ ≡ ( ent | ρ' )    key(ent) = k            ← the key selects the element
  Γ ⊢ ( ent | ρ' ) : Row Effect    payload(ent) = E τ̄
  ( op : forall (b̄ : κ̄'). σ ->* τ ) ∈ Σ(E)         ← the payload selects the protocol
  E's type parameters are ā
  Γ ⊢ σ̄ : κ̄'      Γ;Δ ⊢ e : σ[ā := τ̄][b̄ := σ̄] ! ρ
  ────────────────────────────────────────────────────
  Γ;Δ ⊢ perform k.op [σ̄] e : τ[ā := τ̄][b̄ := σ̄] ! ρ

  h = { handles ent ; return (x : α) -> e_r ; cl_i }
  Γ ⊢ ( ent | ρ ) : Row Effect                      ← the element the handle removes
  Γ ⊢ α : Type      Γ ⊢ β : Type                    ← the annotation and the answer
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

  the k̄ are distinct      |ē| = |k̄|      ι = ( k̄ : σ̄ )      Γ ⊢ ι : Row Type
  each j:  Γ;Δ ⊢ e_j : σ_j ! ρ                      ← initial values, outside the region
  ℓ ∉ dom(Γ)                                        ← the binder is fresh
  Γ' = Γ, region ℓ : ι, { RegionKey ℓ ∉ t | t : Row Effect ∈ Γ }
  Γ' ⊢ ( region ℓ | ρ ) : Row Effect                ← sharp by the recorded facts
  Γ';· ⊢ e : β ! ( region ℓ | ρ )
  Γ ⊢ β : Type      Γ ⊢ ρ : Row Effect              ← the answer and the residual row, outside
  ℓ ∉ frn(β) ∪ frn(ρ)                               ← nothing of the region outlives it
  ───────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e : β ! ρ

  ( region ℓ : ι ) ∈ Γ      ι(k) = σ      RegionKey ℓ ∈ keys(ρ)      Γ ⊢ ρ : Row Effect
  ──────────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ readCell ℓ.k : σ ! ρ

  ( region ℓ : ι ) ∈ Γ      ι(k) = σ      RegionKey ℓ ∈ keys(ρ)      Γ;Δ ⊢ e : σ ! ρ
  ─────────────────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ writeCell ℓ.k e : Unit ! ρ

  Γ;Δ ⊢ e : τ1 -{r1}-> τ2 ! ρ    Γ ⊨ r1 # r'    Γ ⊢ r' : Row Effect
  ─────────────────────────────────────────────────────────────────
  Γ;Δ ⊢ openEff [r'] e : τ1 -{r1 ⊎ r'}-> τ2 ! ρ
```

**The element a `perform` names is one the row decomposes into**, as the residual of a `switchKey` is ([Join points and decision trees](#join-points-and-decision-trees)). In a consistent context the kinding premise asks `k ∉ ρ'`, so the element is unique up to `≡`, and `E τ̄` is the payload the row's [sharp normal form](02-Rows.md#sharp-normal-form) has at `k`. Read off that normal form, the rule would hold of a row only as it is written: a substitution bringing a second element keyed `k` into a tail leaves the row with no normal form, while a decomposition is an equality and a kinding, which every substitution preserves ([Rows](02-Rows.md)). `readCell` and `writeCell` need no payload, an element keyed `RegionKey ℓ` being `region ℓ` and nothing else, and ask only that the key be among the row's: `keys(ρ)` is defined on every row, and a substitution only adds to it. **The checker reads the element off the sharp normal form**, as it does a `switchKey`'s decomposition: a row with two payloads at one key has none, and is reported. Only an inconsistent context kinds such a row.

That handlers are deep (D15) shows in the type of the continuation `k_i`: calling it returns under the same handler, so the result type is `β`, the result of the `handle`, and the ambient row is `ρ`, the row a clause stands at, which holds every region open around the `handle` on both sides of a resumption. A shallow handler would give `τ_i -{( ent | ρ )}-> α`.

A `fast` clause's premise names neither `k_i` nor `β`, and that absence is the whole content of the distinction (D28). Having no way to speak of the answer, such a clause cannot bypass the evaluation still to come in order to supply what the `handle` returns, and having no continuation it cannot invoke one zero or several times; its body is an ordinary computation at the residual row, of the type the continuation resumes with.

**What the rule establishes is about the clause, not about the program containing it.** The body may diverge, it may fault, and it may perform an operation of `ρ` whose own handler declines to resume, or resumes more than once and so runs the rest of the handled computation again ([Effects](03-Effects.md)). The two forms are otherwise alike, both binding the operation's own type variables `b̄_i` and both checked with `Δ` discarded ([Terms and Matching](04-Terms-and-Matching.md)).

`openEff` is required where a pure function is used in an effectful context, a constructor or a foreign applied through its chain aside ([Chains of a constructor or a foreign](#chains-of-a-constructor-or-a-foreign)).

```text
-- f : Int -> Int                        (pure)
-- to call f where g : Int -{( Console )}-> Int
g = λ(n : Int) / ( Console ). (openEff [( Console )] f) n
```

The explicitness is the price of D8. The elaborator inserts it, so an author does not see it.

### Regions

**`handle` has one rule, and a region is a binder of its own** (D36). The handled computation, the return clause, and the operation clauses of a `handle` stand at rows the context gives — `( ent | ρ )`, `ρ`, and `ρ` — so a region open where the `handle` stands is open in all three. Which of them names its cells is the surface's decision ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)).

**A `return` clause reading a cell is admitted by Core on purpose.** Region and `handle` are separate binders, so nothing in Core can tell a return clause inside a region from any other term inside one. The surface produces no such read; a backend and an optimizer must not assume that a return clause reads no cell.

**The layout and the initial values stand outside the region.** The layout is kinded under `Γ`, and kinding it is what rejects a key written twice, a row extension requiring its key absent from the rest. Each initial value is checked at the ambient row `ρ` and keeps `Δ`, being evaluated before the region opens. A `region` given a number of initial values its layout does not declare is rejected with `CellCount`.

**The body stands at `( region ℓ | ρ )`, under `Γ` extended with `ℓ` and with `Δ` discarded.** A join point does not cross into it, as it does not cross into a `handle` ([Terms and Matching](04-Terms-and-Matching.md)). `Γ'` records, for every row variable `t : Row Effect` bound before `ℓ`, the fact `RegionKey ℓ ∉ t`: whatever `t` is instantiated with is formed where `ℓ` is not in scope ([Rows](02-Rows.md)). A row variable bound later, inside the body, gets no such fact, and a function abstracting over a row there that needs the key absent writes `RegionKey ℓ ∉ t` in its type, discharged at each application like any other constraint.

**`( region ℓ | ρ )` is sharp because the binder is fresh.** `ρ` is kinded under `Γ`, where `ℓ` is not in scope, so its known part has no element keyed `RegionKey ℓ`; the recorded facts cover its row variables. So no premise asks the residual row to be free of regions, and **regions nest without restriction**: a region opened inside another carries a different key and stands beside it in one sharp row.

`readCell` and `writeCell` **name the region they reach**. The name is looked up in `Γ` for the layout, which gives the cell's type, and the ambient row must hold `region ℓ`: a reference out of scope is ill-kinded (`UnboundRegion`), one where the region is not ambient is rejected with `RegionNotAmbient`, and one naming a key the layout does not declare with `NoCellAt`. That the row must hold the region is what keeps a closure over a cell from being applied where the region is not open: its arrow carries `region ℓ`, and application requires the arrow's row to equal the ambient one. **`writeCell` evaluates to `Prim.Unit`.** A write is done for its effect on the region and has no result of its own to hand back; giving it the value written would let a use of that value be mistaken for a read. A term that sets a cell and carries on binds the `Unit` like any other result, Core writing every binding out.

**`ℓ ∉ dom(Γ)` is binder freshness**, the well-formedness condition on the checker's input stated above, and a binder breaking it is rejected with `RegionBinderShadows`. It is what lets an occurrence of `ℓ` mean the region it is written under: a binder shadowing an outer one would make a reference to the outer region read the inner, and would make the condition below read an outer region of the same name as an escape.

**`ℓ ∉ frn(β) ∪ frn(ρ)` is the whole of the escape discipline**, and a term breaking it is rejected with `RegionEscapes`. Every way to reach a cell mentions the region: a closure over a `readCell ℓ.k` carries `region ℓ` in its own arrow. The condition therefore keeps such a closure out of the answer type and out of the residual row. There is no cell handle to leak, a cell being named by its region and key rather than held as a value, so these are the only routes there are. This is what a rank-2 quantifier would enforce for a `runST`-shaped function; `region` being a binder, a side condition enforces it directly. **The answer type and the residual row are kinded under `Γ` as well**, where the term stands, the body's derivation kinding them under `Γ'` alone. `ℓ` is not bound in `Γ`, so the kinding premises imply the condition; it is written apart because it is the escape discipline, and the checker reports it as such, every row it carries being kinded where it was introduced.

**What the condition forbids is a reference into a region, not a region.** A term that carries the whole `region` — a closure over it, or a continuation an outer handler captured across it — carries the binder along with everything the binder scopes over, and its type mentions no `ℓ` at all, that name being bound within. Such a term is closed with respect to the region and may be passed anywhere; what each application of it sees is settled in [Semantics](06-Semantics.md). The condition is about references that would outlive what binds them, and those alone.

**The layout is a written sequence, and the element carries none.** `( k̄ : σ̄ )` fixes finitely many cells with distinct keys, which is what lets `ē` give one initial value each and what makes the region a finite map at run time. The element `region ℓ` holds only the name, the layout being read from `Γ`. A region name is never quantified, so a function reaching a cell is written where the region's name is in scope.

## Join points and decision trees

```text
  Γ ⊢ τ : Type    Γ ⊢ τ̄ : Type    Γ ⊢ ρ : Row Effect
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

  Γ;Δ ⊢ e : τ ! ρ                      Γ;Ω ⊢ o : τ_o    Γ, x : τ_o; Δ; Ω ⊢ dt : τ ! ρ
  ────────────────────────             ──────────────────────────────────────────────
  Γ;Δ;Ω ⊢ leaf e : τ ! ρ               Γ;Δ;Ω ⊢ bind x = o in dt : τ ! ρ

  Γ;Ω ⊢ o : T σ̄       T is a data type, not an intrinsic one (§6.2 Prim and Base)
  Γ ⊢ τ : Type      Γ ⊢ ρ : Row Effect             ← the branches may be none
  each Ctor_i is a constructor of T, Ctor_i : forall ā. τ̄_i -> T ā
  the Ctor_i are distinct
  each i: Γ;Δ; Ω ∪ { o ! Ctor_i . j ↦ τ_ij[ā := σ̄] } ⊢ dt_i : τ ! ρ
  with a default:     Γ;Δ;Ω ⊢ dt_0 : τ ! ρ
  without a default:  {Ctor_i} exhausts the constructors of T
  ─────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ switchCtor o { Ctor_i -> dt_i } [default -> dt_0] : τ ! ρ

  Γ;Ω ⊢ o : τ_o       τ_o is a primitive type with literals
  the c_i are literals of τ_o and are distinct
  each i: Γ;Δ;Ω ⊢ dt_i : τ ! ρ
  Γ;Δ;Ω ⊢ dt_0 : τ ! ρ                          ← a default is mandatory
  ─────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ switchLit o { c_i -> dt_i } default -> dt_0 : τ ! ρ

  Γ;Ω ⊢ o : Variant r        the k_i are distinct
  Γ ⊢ τ : Type      Γ ⊢ ρ : Row Effect             ← the branches may be none
  Γ ⊢ r ≡ ( k_1 : τ_1, …, k_n : τ_n | r' )       ← r decomposes into the enumerated
  Γ ⊢ ( k_1 : τ_1, …, k_n : τ_n | r' ) : Row Type    elements and a residual r'
  each i: Γ;Δ; Ω ∪ { o ? k_i ↦ τ_i } ⊢ dt_i : τ ! ρ
  with a default:     Γ;Δ; Ω ∪ { o ↦ Variant r' } ⊢ dt_0 : τ ! ρ
  without a default:  Γ ⊢ r' ≡ ()
  ─────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ switchKey o { k_i -> dt_i } [default -> dt_0] : τ ! ρ

  Γ;Δ ⊢ e : Boolean ! ρ    Γ;Δ;Ω ⊢ dt_1 : τ ! ρ    Γ;Δ;Ω ⊢ dt_2 : τ ! ρ
  ─────────────────────────────────────────────────────────────────────
  Γ;Δ;Ω ⊢ guard e dt_1 dt_2 : τ ! ρ

  Γ ⊢ ρ ≡ ( Partial | ρ' )    Γ ⊢ ( Partial | ρ' ) : Row Effect    Γ ⊢ τ : Type
  ──────────────────────────────────────────────────────────────────────────  (derived; see §3.3 Effects)
  Γ;Δ;Ω ⊢ fail τ : τ ! ρ
```

**A handler writes the element it removes, not only its key.** The row being handled appears nowhere else in the term, so neither half of the element is recoverable from the other: a key does not name an effect, and the arguments `τ̄` are not determined by the clauses without first-order matching. What `Ω` and `Σ` give the rules is then a lookup rather than a search. Only `key(ent)` has meaning at run time; the payload is an annotation and erases.

### Occurrence typing

```text
  ( s_i ↦ τ ) ∈ Ω
  ───────────────
  Γ;Ω ⊢ s_i : τ

  ( o ↦ τ ) ∈ Ω                    ← a dispatch records what it takes apart
  ─────────────
  Γ;Ω ⊢ o : τ

  Γ;Ω ⊢ o : Record r    Γ ⊢ r ≡ ( k : τ | r' )    Γ ⊢ ( k : τ | r' ) : Row Type
  ──────────────────────────────────────────────────────────────────────────
  Γ;Ω ⊢ o . k : τ
```

`o ! Ctor . j` and `o ? k` are typed by the branch that established them and by nothing else: what a constructor or a variant carries is known only under the dispatch that selected it, so those paths reach `Ω` through `switchCtor` and `switchKey`. A record needs no such branch, having one element at every key of its row, so `o . k` is read off the type of what it projects from. The element is one the row decomposes into, as a `perform`'s is ([Effects](#effects)), and the checker reads it off the sharp normal form in the same way. The kinding premise is what keeps `Ω` well formed: it kinds `τ`, which a `bind` puts into `Γ`.

In the default branch of `switchCtor` and `switchLit` the occurrence context `Ω` is unchanged, because Core does not track the refinement "not one of the enumerated cases". Refinement happens only in the default branch of `switchKey`, where the occurrence takes the residual type `Variant r'`.

That branch is the term-level appearance of residual computation over an unknown tail: where `r` has a row variable among its tails, so has every `r'` it decomposes into, `r' ≡ ()` cannot be met, and a default is required, its type being the residual. An open variant cannot be enumerated by pretending it is closed.

**The residual is what the row decomposes into, not what deleting the keys leaves.** In a consistent context the kinding premise asks `k_i ∉ r'` of every enumerated key, so `r'` is unique up to `≡`: it is the row whose [sharp normal form](02-Rows.md#sharp-normal-form) is that of `r` with the `k_i` deleted, and each `τ_i` is the payload `r` has at `k_i`. Stated by deletion, the rule would hold of a row only as it is written, and a substitution can change what deleting finds. Under `x ∉ s`, `Variant ( x : Int | s )` has the residual `s`. Substituting `( x : Int )` for `s` turns the assumption into the inconsistent `x ∉ ( x : Int )` and collapses the row to `( x : Int )`, whose deletion leaves `()`, while the default was typed at `Variant s`, now `Variant ( x : Int )`. The decomposition admits that residual still, `( x : Int | ( x : Int ) )` being kinded wherever the context entails every constraint. Equality and entailment are preserved by every substitution ([Rows](02-Rows.md)), and so is this rule.

**The checker reads the decomposition off the sharp normal form**: each `τ_i` is `r`'s payload at `k_i`, a key `r` lacks is rejected with `NoElementAt`, and `r'` is what deleting the `k_i` leaves, which is a residual the rule admits wherever the normal form exists. A row with two payloads at one key has none, and is reported. Only an inconsistent context kinds such a row, and a substitution makes one out of a sharp row; the rule has a derivation for it, which a reduct needs and the checker, checking no reduct, does not.
