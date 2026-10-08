# Kinds and Types

## Names and binding

By the time a term reaches Core, name resolution and hygiene are complete.

- A **qualified name** `M.x` refers to a top-level name of module `M`, where `M` is a fully qualified module name.
- A **local name** `x` is introduced by `λ`, `Λ`, `let`, `letrec`, or a decision tree's `bind`.
- A **region name** `ℓ` is introduced by the `region` binder and by nothing else ([Region names](#region-names)).
- Core terms are identified up to α-equivalence. What the checker receives is a representation, and for the binders of terms that bind a type-level name — a `Λ`, the type binders of an operation clause, and a `region` — that representation follows the **unique-binder convention**: none binds a name already bound where it stands. A representation that breaks it is rejected as malformed, not renamed ([Typing Rules](05-Typing-Rules.md)). A `forall` within a type is not held to the convention, and neither is a value binder; both are scoped lexically.
- Names introduced by macro expansion are already made unique. **Core carries no hygiene information.** Scopes and expansion traces belong to the Surface AST and to diagnostics.

```text
ModuleName ::= Upper ("." Upper)*
Ident      ::= value-level identifier
TyIdent    ::= type-level identifier
Ctor       ::= data constructor name
Symbol     ::= a written field or instance name
Tag        ::= a structural constructor of a variant
EffName    ::= effect name
OpName     ::= effect operation name
JoinName   ::= join point name
RegionName ::= region name, written ℓ

QIdent   ::= ModuleName "." Ident | Ident
QEffName ::= ModuleName "." EffName
```

An effect name is always qualified where it is a key, since an `EffectKey` is the identity of a declaration and identities do not float free of the module that made them.

A row key is not a name either; it is one of five things.

```text
RowKey ::= SymbolKey Symbol        a written field or instance name
         | TagKey Tag              a structural variant constructor
         | PositionKey Nat         a component of a tuple, 0-origin
         | EffectKey QEffName      a declared effect, fully qualified
         | RegionKey RegionName    the region of cells named ℓ (D36)
```

`Nat` is a non-negative integer, written in the key and nowhere else; it is not a type, and the kind grammar gains nothing from it.

**The first three are structural, the fourth is nominal, and the last is neither.** A `SymbolKey` and a `TagKey` are what they are by virtue of being written, a `PositionKey` by where the component it keys stands; nothing declares any of them, and two occurrences of `#Ok` in unrelated modules are the same key. An `EffectKey` is the identity of a declaration in `Σ`, so `Console.Log` and `Audit.Log` are different keys however alike they read ([Rows](02-Rows.md)). A `RegionKey ℓ` is the identity of a `region` binder in scope: two are the same key exactly when they carry the same region name, so every region has a key of its own.

**Two of the five have no source syntax.** Elaborating a tuple derives a `PositionKey`, and only a `region` binder produces a `RegionKey ℓ`. That the second cannot be written is what it is for: no declaration names a region, so no `handles` can name one and no `perform` can reach one, and the only thing that removes `region ℓ` from a row is the `region` that opens it ([Effects](03-Effects.md)).

Neither the row theory nor the solver distinguishes any of them: to those, all five are rigid keys that compare for equality. What distinguishes them is well-formedness, since only an `EffectKey` sends the checker to `Σ` and only a `RegionKey` to the regions in scope.

Every expression, declaration, and module carries a source span. Types, kinds, the structure of a decision tree, and the structure of a handler carry none; an error in one of those is reported at the nearest enclosing node that has a span. Spans have no influence on type checking or semantics; they exist for diagnostics alone, and the grammars below omit them.

A diagnostic is located where the problem is, and an enclosing node contributes context rather than a location. The body of a `leaf` that fails to typecheck is reported at that body; a `switch*` that is not locally total, or a handler that omits a clause, is reported at the `case` or `handle` that contains it.

## Kinds

Kinds and types are separate syntactic classes (D2). Kinds are stratified into three layers (D24).

```text
ε ::= Type | Effect                  row element kinds

κ ::= k                              kind variables
    | Type                           the kind of value types
    | Effect                         the kind of effect constructors
    | Row ε                          rows of ε
    | κ1 -> κ2                       type constructors

q ::= k                              quantifiable kinds, a subset of κ
    | Type
    | Row Type
    | Row Effect
    | q1 -> q2                       where q2 produces Type
```

Kind equality is syntactic, up to α-equivalence. There is no computation at the kind level.

### Well-formedness

Two judgements decide the grammar above. `Γ ⊢ κ kind` holds of a kind the checker may work with; `Γ ⊢ κ qkind` holds of the subset that may be quantified over.

```text
  k ∈ Γ
  ─────────────       ─────────────────       ───────────────────
  Γ ⊢ k kind          Γ ⊢ Type kind           Γ ⊢ Effect kind

  ───────────────────       ─────────────────────
  Γ ⊢ Row Type kind         Γ ⊢ Row Effect kind

  Γ ⊢ κ1 kind    Γ ⊢ κ2 kind
  ──────────────────────────
  Γ ⊢ κ1 -> κ2 kind
```

`Row` has no rule of its own. `Row Type` and `Row Effect` are the only two, which is what confines `Row` to row element kinds.

```text
  k ∈ Γ
  ──────────────       ──────────────────       ────────────────────
  Γ ⊢ k qkind          Γ ⊢ Type qkind           Γ ⊢ Row Type qkind

  ────────────────────       Γ ⊢ q1 qkind    Γ ⊢ q2 qkind    result(q2) = Type
  Γ ⊢ Row Effect qkind       ─────────────────────────────────────────────────
                             Γ ⊢ q1 -> q2 qkind
```

`Effect` has no `qkind` rule, and that absence is D24. Every quantifiable kind is a kind, so `Γ ⊢ κ qkind` implies `Γ ⊢ κ kind`.

`result` is what a kind produces once it is fully applied.

```text
result( κ1 -> κ2 )  = result( κ2 )
result( κ )         = κ                 otherwise
```

**Only row syntax produces a row.** The side condition confines a row kind to the argument side of an arrow: `Row Type -> Type` is quantifiable and `Row Type -> Row Type` is not, and a kind variable is excluded from the result position as well, since it may be instantiated with a row kind. The same condition holds of the kind of every type constructor in `Σ`.

What this buys is the domain of `nf`. A type of kind `Row ε` is then a row variable, `()`, a row extension, or a union and nothing else, which is exactly what normalization is defined on, so **every well-kinded row has a normal form** ([Rows](02-Rows.md)). Row equality, entailment, and unification all rest on that. A type-level function producing a row would have to arrive together with normalization rules of its own.

A kind variable is quantifiable, and every `[[κ̄]]` requires `qkind` of what it supplies, so a kind variable stands only for a quantifiable kind.

Representative kinds, drawn from `Prim`, the standard library, and a user module alike:

```text
Int        : Type
Unit       : Type
List       : Type -> Type
Record     : Row Type -> Type
Variant    : Row Type -> Type
Function   : Type -> Row Effect -> Type -> Type
State      : Type -> Effect
```

These illustrate the shapes a kind takes; which of them `Prim` declares is settled in [Prim and Base](../06-Modules/02-Prim-and-Base.md).

`Row Type` is the row kind of records and variants; `Row Effect` is that of effect rows. Both share the row theory of [Rows](02-Rows.md).

### Why the three layers

**`Row` takes only `ε`.** Row element well-formedness is defined for the shapes of exactly two kinds: a key paired with a type at `Row Type`, and an effect application with or without a written key at `Row Effect`. Permitting `Row κ` for arbitrary `κ` would admit degenerate row kinds such as `Row (Type -> Type)`, inhabited only by the empty row, row variables, and `⊎`, and having no elements at all.

**Quantification is restricted to `q`**, expressed by the judgement `Γ ⊢ κ qkind`.

```text
  Γ ⊢ κ qkind    Γ, a : κ ⊢ τ : Type
  ──────────────────────────────────
  Γ ⊢ forall (a : κ). τ : Type
```

The same condition applies at every site that introduces a type variable: `forall (a : κ). τ`, `Λ (a : κ). v`, the type parameters of data and effect declarations, the type parameters of operations, and the instantiation `[[κ̄]]`.

| | Admitted | Reason |
| --- | --- | --- |
| `forall (r : Row Effect). …` | yes | `Row Effect ∈ q` |
| `forall (f : Type -> Type). …` | yes | higher-kinded types are retained |
| `forall (e : Effect). …` | **no** | `Effect ∉ q`. Abstracting over a single effect is done with a `Row Effect` variable |
| `forall (f : Type -> Effect). …` | **no** | `Effect ∉ q` |
| `forall (f : Row Type -> Type). …` | yes | a row may be consumed |
| `forall (f : Row Type -> Row Type). …` | **no** | only row syntax produces a row |
| `forall (f : Type -> k). …` | **no** | `k` may be instantiated with a row kind |
| `Proxy [[Effect]]` | **no** | instantiation also requires `qkind` |
| `State : Type -> Effect` | yes | the kind of a declared constructor is a `κ`, not a `q` |

`Effect` belongs to `κ` but not to `q`: it is required as the result kind of effect constructors, and it cannot be quantified.

One could instead permit quantification over `Effect`. That design is also coherent, but it then needs a separate rule forbidding a type variable at the head of a row element, since effect row keys must be rigid (D16). Stella takes the stratification instead.

## Kind schemes

```text
σκ ::= forall k1 .. kn . κ       (n >= 0)
```

Kind schemes appear **only on declarations**. The global signature `Σ` carries one for each of three things.

| Entity | Form |
| --- | --- |
| Type constructor | `T : forall k̄. κ` |
| Data constructor | `Ctor : forall k̄. σ` |
| Top-level value or foreign | `M.x : forall k̄. σ` |

The kind of a type constructor produces `Type`, that is `result(κ) = Type`. `Record : Row Type -> Type` is admitted; a constructor producing a row is not, for the reason above.

**An effect constructor is not among them.** Its kind is `κ̄ -> Effect`, binding no kind variable, so an element of a `Row Effect` is written `E τ̄` and carries no `[[κ̄]]` ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

Neither the type grammar nor the term grammar has a kind **quantifier**: there is no `forall (k : Kind). τ` and no `Λ (k : Kind). e`. Quantification happens only in declarations. A kind variable enters the local context `Γ` only while checking a declaration whose scheme binds it.

### Instantiation is explicit

A kind scheme is instantiated **explicitly at the use site**, in both types and terms.

```text
τ ::= …  | T [[κ̄]]        instantiate a type constructor's kind scheme
e ::= …  | M.x [[κ̄]]      instantiate a global name's kind scheme
```

`[[…]]` is not an application to an arbitrary expression; it is an annotation on the occurrence of a global name. Since D3 provides no introduction form for kind abstraction, there can be no elimination form either, and the grammar forbids terms such as `(λ(x : τ). x) [[Type]]`.

When the scheme is empty, `[[]]` is omitted. Most declarations are in this case, so `[[…]]` appears only where a kind-polymorphic declaration is used.

```text
Proxy [[Type]] Int              -- in a type
Proxy [[Type]] [Int]            -- in a term
List Int                        -- empty kind scheme; nothing is written
```

Making instantiation explicit keeps the rules a matter of **substitution alone**. Implicit instantiation would require bidirectional kind checking and first-order matching in the type checker, together with a well-formedness condition guaranteeing that every bound kind variable is determined. Two grammar productions cost less than that machinery in the trusted core. This is also consistent with Core generally: implicit arguments become ordinary arguments (D11), type instantiation is `e [τ]`, constraints are `e [•]`, and effect widening is `openEff`.

Surface syntax never contains `[[κ]]`; the elaborator emits it.

## Types

```text
τ, σ, ρ ::= a                        type variable
          | T [[κ̄]]                  type constructor; `T` when κ̄ is empty
          | τ1 τ2                    type application
          | forall (a : κ) . τ       universal quantification
          | C => τ                   constraint abstraction, erased
          | ()                       the empty row
          | ( ent | ρ )              row extension
          | ρ1 ⊎ ρ2                  row union

ent ::= k : τ                        a `Row Type` element; the key is written
      | E τ̄                          a `Row Effect` element; the key is derived
      | SymbolKey s : E τ̄            a labelled `Row Effect` element
      | region ℓ                     the region named ℓ is open (D36)

k   ::= a RowKey                     one of the five constructors above
s   ::= a Symbol                     the written name of a labelled element
ℓ   ::= a RegionName                 bound by a `region` of the term

C ::= k ∉ ρ                          Lacks
    | ρ1 # ρ2                        Disjoint
```

**Core writes the key constructor; these documents drop it where it is evident.** `( name : String | r )` abbreviates `( SymbolKey name : String | r )`, and `( cache : State Int )` abbreviates `( SymbolKey cache : State Int )`. The abbreviation is for reading only: what an AST holds, and what the rules below match on, is the constructor.

A function type is an application of the type constructor `Function`; Core has no arrow syntax.

```text
τ1 -{ρ}-> τ2   ≡   Function τ1 ρ τ2
τ1 -> τ2       ≡   Function τ1 () τ2        (a pure function)
```

**The arrow is notation used in these documents and in surface syntax, not a Core name.** Core names are fully qualified, so the constructor is `Prim.Function`. All infix operators are surface aliases resolved to qualified names during name resolution; Core has no counterpart to PureScript's `TypeOp`. These documents write `Int`, `Unit`, `Record`, and `Function` without the `Prim.` prefix for readability.

`Record ρ` and `Variant ρ` are likewise ordinary type constructor applications.

### Region names

**A region name `ℓ` is a syntactic class of its own.** It is not a type and has no kind. The `region` binder of a term binds it ([Effects](03-Effects.md)), and no `forall`, `Λ`, or metavariable stands for one: no type or term abstracts over a region name, so **a region name is never the target of an instantiation**. The only operations that replace one are binder-aware α-renaming and the replacement of a binder by a fresh run-time name when a region opens ([Semantics](06-Semantics.md)). Region names are what make a region's identity static.

A type mentions a region name in three places: in a `region ℓ` element, in a `RegionKey ℓ` key of a row, and in the key of a `Lacks` constraint. `frn(τ)` is the set of region names occurring in `τ`. A type binds no region name, so `frn` of a type is plain occurrence.

- **α-equivalence** renames a region binder together with every occurrence it binds, in the term and in the types the term annotates.
- **Key equality.** `RegionKey ℓ1 = RegionKey ℓ2` exactly when `ℓ1 = ℓ2` after α-renaming. No instantiation replaces a region name, and α-renaming and opening replace a binder together with all its occurrences, so the key is rigid and row equality stays decidable (D13, D16).

In a term, `region [ℓ] … in e` binds `ℓ` in `e` and in nothing else — not in the layout's types and not in the initial values ([Typing Rules](05-Typing-Rules.md)).

## Kinding

The judgement is `Γ ⊢ τ : κ`. Contexts are defined in [Typing Rules](05-Typing-Rules.md).

```text
  (a : κ) ∈ Γ                (T : forall k̄. κ) ∈ Σ   Γ ⊢ κ̄' qkind   |κ̄'| = |k̄|
  ───────────                ────────────────────────────────────────────────
  Γ ⊢ a : κ                  Γ ⊢ T [[κ̄']] : κ[k̄ := κ̄']

  Γ ⊢ τ1 : κ1 -> κ2    Γ ⊢ τ2 : κ1
  ────────────────────────────────
  Γ ⊢ τ1 τ2 : κ2

  Γ ⊢ κ qkind    Γ, a : κ ⊢ τ : Type     Γ ⊢ C ok    Γ, C ⊢ τ : Type
  ──────────────────────────────────     ──────────────────────────────
  Γ ⊢ forall (a : κ). τ : Type           Γ ⊢ C => τ : Type

  ─────────────────
  Γ ⊢ () : Row ε

  Γ ⊢ ent : ε entry    Γ ⊢ ρ : Row ε    Γ ⊨ key(ent) ∉ ρ
  ──────────────────────────────────────────────────────  ← sharpness
  Γ ⊢ ( ent | ρ ) : Row ε

  Γ ⊢ ρ1 : Row ε    Γ ⊢ ρ2 : Row ε    Γ ⊨ ρ1 # ρ2
  ────────────────────────────────────────────────  ← disjointness
  Γ ⊢ ρ1 ⊎ ρ2 : Row ε
```

**A constraint is assumed while its body is kinded.** A row that is sharp only under `k ∉ r` — `(k ∉ r) => Record ( k : τ | r )`, the shape every row-polymorphic function has — is well-kinded for that reason and for no other. Writing `Γ, C` also requires `C` to be satisfiable ([Typing Rules](05-Typing-Rules.md)).

**A `forall` is scoped lexically.** `Γ, a : κ` hides an outer variable of the name `a`, together with every assumption made of it: what was assumed of the outer variable says nothing of the inner one. Types are not held to the unique-binder convention, since a type reaches the checker from `Σ` and from substitution as well as from the term, and types are compared up to α-equivalence.

That row extension and row union require **entailment from the context** is the centre of the design. PureScript admits `RCons` unconditionally and performs no elimination of duplicate labels; in Stella a well-kinded row is sharp by construction.

### Row elements

An element pairs a key with a payload. What may stand on each side is fixed by the row element kind.

```text
  k ∈ { SymbolKey s, TagKey t, PositionKey n }      Γ ⊢ τ : Type
  ──────────────────────────────────────────────────────────────
  Γ ⊢ ( k : τ ) : Type entry                        key( k : τ ) = k

  ( E : κ̄ -> Effect ) ∈ Σ      Γ ⊢ τ̄ : κ̄
  ────────────────────────────────────────
  Γ ⊢ E τ̄ : Effect entry                            key( E τ̄ ) = EffectKey E

  ( E : κ̄ -> Effect ) ∈ Σ      Γ ⊢ τ̄ : κ̄
  ────────────────────────────────────────
  Γ ⊢ ( SymbolKey s : E τ̄ ) : Effect entry          key( SymbolKey s : E τ̄ ) = SymbolKey s

  ( region ℓ : ι ) ∈ Γ
  ────────────────────────────
  Γ ⊢ region ℓ : Effect entry                       key( region ℓ ) = RegionKey ℓ
```

**A region consults `Σ` nowhere.** It names no declaration, which is why nothing can declare one. What it needs is its name in scope: `Γ` holds `region ℓ : ι` for every `region` binder standing around the type, `ι` being that region's layout, and a region name out of scope makes the type ill-kinded (`UnboundRegion`), as an unbound type variable does. This is the scope check for region names. The element carries no layout; the type of a cell is read from `Γ` (D36).

Two functions read an element apart, and both are total on well-formed ones.

```text
key( k : τ )                = k             payload( k : τ )                = τ
key( E τ̄ )                  = EffectKey E   payload( E τ̄ )                  = E τ̄
key( SymbolKey s : E τ̄ )    = SymbolKey s   payload( SymbolKey s : E τ̄ )    = E τ̄
key( region ℓ )             = RegionKey ℓ   payload( region ℓ )             = region ℓ
```

Normalization pairs them — `nf` maps `ent` to `key(ent) ↦ payload(ent)` ([Rows](02-Rows.md)) — and the rule for `handle` uses both, one to find the element and the other to find its operations ([Typing Rules](05-Typing-Rules.md)).

At `Row Type` the key is written and the payload is the type. At `Row Effect` there are three forms. Two of them differ only in where the key comes from — **the unlabelled form derives it from the effect at the head, and the labelled form writes one** — and in both the payload is an application of a declared effect constructor, which is what the operations of a `perform` are looked up through. The third is a region, whose payload is its own name and no effect application at all, so the rules that read one find nothing to read: a `perform` cannot name a region and a `handles` cannot write one ([Typing Rules](05-Typing-Rules.md)).

**A `Row Type` element admits any structural key, and the type constructor wrapping the row does not narrow that.** `Record ( #Ok : Int )` and `Variant ( 0 : Int )` are well-kinded, oddly as they read. Core keeps one row theory rather than three, and which keys a structure conventionally uses is a matter for surface syntax and the elaborator, not for kinding.

The alternative was rejected on a concrete ground: a restriction would have to hold of open rows too, and `Record r` says nothing about the keys of `r`. Enforcing it would mean carrying a per-constructor condition through unification and entailment, which is precisely the generality the row theory exists to avoid.

The labelled form is what lets one effect appear twice.

```text
( State Int )                                     one State
( cache : State Int, counter : State Int )        two, distinguished by their keys
```

Without it the row would be ill-kinded, both elements having the key `EffectKey State`.

An element of a `Row Effect` that carries a payload **must have a declared effect constructor at the head of it**; a payload headed by a type variable is not admitted. A region is the one element that carries no such payload, and it needs none: it names no declaration, and its key is the region name it carries (D36).

Keys are therefore rigid whatever their kind — a `SymbolKey`, a `TagKey`, and a `PositionKey` are structural constants, independent of how metavariables are solved; an `EffectKey` is a declaration identity; and a `RegionKey ℓ` carries a region name, which no instantiation replaces — which is what makes row equality decidable ([Rows](02-Rows.md)). The `qkind` condition of D24 reinforces this: since `Effect` is not quantifiable, `forall (e : Effect). …` cannot be written, so a type variable can never reach the head of a payload.

### Constraint well-formedness

```text
  Γ ⊢ ρ : Row ε    Γ ⊢ k key ε          Γ ⊢ ρ1 : Row ε    Γ ⊢ ρ2 : Row ε
  ─────────────────────────────         ───────────────────────────────
  Γ ⊢ k ∉ ρ ok                          Γ ⊢ ρ1 # ρ2 ok
```

Key well-formedness is determined by `ε`.

```text
  k ∈ { SymbolKey s, TagKey t, PositionKey n }      ( E : κ̄ -> Effect ) ∈ Σ
  ────────────────────────────────────────────      ────────────────────────────
  Γ ⊢ k key Type                                    Γ ⊢ EffectKey E key Effect

                                       ( region ℓ : ι ) ∈ Γ
  ──────────────────────────────       ────────────────────────────
  Γ ⊢ SymbolKey s key Effect           Γ ⊢ RegionKey ℓ key Effect
```

A structural key is well formed wherever it may occur, needing nothing from `Σ`. An `EffectKey` is well formed only where the declaration exists, which is the whole of the difference between the two. A `RegionKey ℓ` is well formed at `Row Effect` alone and only where `ℓ` is in scope, so **`RegionKey ℓ ∉ ρ` is a constraint that can be written and assumed inside the region** — which is what a function that abstracts over a row there and needs the key absent from it writes in its type ([Typing Rules](05-Typing-Rules.md)). A row variable bound outside the region needs no such constraint, the `region` binder recording the fact for it ([Rows](02-Rows.md)).

`SymbolKey` occurs at both kinds, since it is the key of a record field and of a labelled effect instance alike. A `TagKey` and a `PositionKey` are confined to `Row Type`: an effect row's payload is an effect application, and neither a tag nor a position says which effect.

```text
cache ∉ e                 -- admitted: `cache` may key a labelled instance
Console ∉ e               -- admitted: `Console` is declared
#Ok ∉ e                   -- not admitted: a tag is not a key of a Row Effect
```

Both sides of `#` must share the same `ε`; a Disjoint constraint spanning `Row Type` and `Row Effect` is not expressible.

## Type equality

`Γ ⊢ τ1 ≡ τ2` holds when the types are α-equivalent, their rows agree by the normal form of [Rows](02-Rows.md), and they are otherwise structurally identical.

There is no β-reduction and no δ-reduction, because there are no type-level functions. Apart from row normalization, deciding equality is syntactic.

The type grammar has application `τ1 τ2` but **no abstraction**, and that is what gives this property. Type constructors can be abstracted over — `forall (f : Type -> Type). …` — but anonymous type constructors cannot be defined. Core therefore lies between System F and System Fω (D1). Introducing a type-level lambda would make it Fω and would bring β-reduction into type equality.
