# Terms and Pattern Matching

## Term syntax

```text
e ::= x | M.x [[κ̄]]                    variable; `M.x` when κ̄ is empty
    | c                                literal
    | λ (x : τ) . e                    value abstraction
    | e1 e2                            value application
    | Λ (a : κ) . e                    type abstraction
    | e [τ]                            type application
    | Λ (_ : C) . e                    constraint abstraction
    | e [•]                            constraint application
    | let x : τ = e1 in e2             non-recursive binding
    | letrec { x̄ : σ̄ = v̄ } in e        recursive binding group
    | case (ē) of dt                   pattern match
    | letjoin j (x̄ : τ̄) : τ = e1 in e2  join point
    | jump j (ē)                       jump to a join point; tail position only
    | fail τ                           non-exhaustive; derived notation
    -- records
    | {}
    | extend k e1 e2
    | select k e
    | restrict k e
    | update k e1 e2
    | merge e1 e2
    -- variants
    | inject k e
    | weaken k [τ] e
    | absurd [τ] e
    -- effects
    | perform k.op [τ̄] e
    | handle e with h
    | openEff [ρ] e
    -- regions of cells
    | region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e
    | readCell ℓ.k
    | writeCell ℓ.k e

c ::= literals of Int, Number, String, Char, Boolean
```

There is no array literal and no object literal. Arrays are the `Array` type constructor together with primitives; records are built by iterating `extend`. There is no dedicated constructor node: a data constructor is an ordinary global name `M.Ctor` whose type the declaration table records, and construction is ordinary application.

## Value forms

```text
v ::= c
    | λ (x : τ) . e
    | Λ (a : κ) . v
    | Λ (_ : C) . v
    | M.Ctor ς                 a constructor spine
    | {} | extend k v1 v2
    | inject k v
```

`ς` is the spine of arguments the constructor has accumulated: kind, type, and constraint instantiations together with values, in whatever order the declared type calls for. [Semantics](06-Semantics.md) gives the full value grammar, which adds the forms that arise only during reduction.

**A constructor application need not be saturated.** Data constructors have curried function types, so `Main.Cons [Int] 1 : List Int -> List Int` is a legitimate term. Were it not a value form, it would be neither a value nor reducible, since a constructor, unlike a lambda, has no body to reduce.

With `|v̄| = arity` it is a completed structure; with `|v̄| < arity` it is a value that behaves as a function. Both are value forms and evaluation stops at them.

**The body of a type or constraint abstraction must be a value form** (the value restriction). This makes `Λ`, `[τ]`, and `[•]` fully erasable and removes any question of evaluation order at type application. The elaborator eta-expands where necessary.

The right-hand side of a recursive binding is restricted further (D14).

```text
FunVal ::= λ (x : τ) . e
         | Λ (a : κ) . FunVal
         | Λ (_ : C) . FunVal
```

Under strict evaluation a binding such as `letrec x = f x` has no meaning. PureScript leaves this to an uninitialized reference at run time; Stella rejects it syntactically in the type checker.

## Join points

**A join point writes its result type.** It is the type of the whole `letjoin` and of every `jump` to `j`, and neither of the two bodies settles it ahead of the other: a definition may jump to itself and a body may be nothing but a jump. Writing it keeps the rule free of any order of checking.

`letjoin` and `jump` follow the standard join point discipline.

- A join point is not first class. It cannot be passed as a value and forms no closure.
- `jump` occurs only in tail position.
- A join point's result type and ambient effect row match those of the enclosing scope.
- **A join point does not cross a function boundary.**

The last condition is what makes a join point a join point. `jump j` must be implementable as a transfer of control **within the same function activation** as `letjoin j`. If a closure could capture a join point, it would no longer be a goto but a genuine continuation, and would not lower to a Mid IR join point directly.

The typing rules enforce this by **discarding** the join point context `Δ`.

```text
λ (x : τ). e                 check e with Δ := ·
Λ (a : κ). v                 check v with Δ := ·
handle e with h              check e, the return clause, and every operation clause with Δ := ·
region [ℓ] … @ ( ē ) in e    check e with Δ := ·
```

This is why `Δ` is a context separate from `Γ`: their scoping rules differ. `Γ` extends into the body of a lambda; `Δ` is cut off there. A single context could not express the difference.

Discarding `Δ` at `handle` is conservative. A clause is entered from the `perform` site, which lies at an arbitrary depth inside the handled computation and in general in another function activation, so an outward `jump` from a clause body would be a non-local exit that unwinds the handler. This holds of both clause forms ([Effects](03-Effects.md)): a `full` clause is a function boundary outright, receiving a continuation and being invoked later, while a `fast` clause builds no continuation but is still entered from that arbitrary point. v0.1 takes the simple rule and may relax it; since the elaborator can move join points inward, the practical restriction is small.

Discarding `Δ` at a `region`'s body has a reason of its own. A region closes only when its body reaches a value, so a tail context does not pass through its frame ([Semantics](06-Semantics.md)), and a `jump` out of the body would find no `letjoin` to transfer to. The initial values stand outside the region and keep `Δ`.

Join points exist for two reasons: so that a decision tree can hold each alternative's body once, and so that lowering to Mid IR join points preserves structure.

## No implicit arguments

Core has no constructor for implicit arguments (D11). A surface signature such as

```purescript
eq :: forall a. {{dict :: Eq a by Typeclass.resolve}} -> a -> a -> Boolean
```

elaborates to the Core type

```text
M.eq : forall (a : Type). Record ( eq : a -> a -> Boolean ) -> a -> a -> Boolean
```

Neither `{{…}}` nor `by` survives. An argument omitted at the call site is filled by an ordinary term that `Typeclass.resolve` constructed, applied with `App`. The Core type checker does not know that the term is a dictionary, and does not need to.

This is the necessary condition, on the Core side, for type classes to be implementable as a library.

## Pattern matching

PureScript's CoreFn keeps `Case` with binders and guards, a representation that preserves the shape of the source; which field is examined in which order cannot be read from the term. Stella's Core holds a decision tree (D9).

### Occurrences

An occurrence is a path from a scrutinee.

```text
o ::= s_i              the i-th scrutinee, 0-origin
    | o ! Ctor . j     the j-th field of constructor Ctor
    | o . k            the payload of the record element keyed k
    | o ? k            the payload of the variant element keyed k
```

Occurrences are **projections only** and have no effects, so the same occurrence may be referenced any number of times within a tree.

### Decision trees

```text
dt ::= leaf e
     | bind x = o in dt
     | switchCtor  o { Ctor_1 -> dt1 ; … ; Ctor_n -> dtn } [ default -> dt0 ]
     | switchLit   o { c1 -> dt1 ; … ; cn -> dtn }   default -> dt0
     | switchKey   o { k1 -> dt1 ; … ; kn -> dtn } [ default -> dt0 ]
     | guard e dt_then dt_else
     | fail
```

- `switchCtor` is a single dispatch on a data type's tag. The branches are mutually exclusive and their written order carries no meaning.
- `switchKey` dispatches on the key of a variant element. In the `default` branch the occurrence has the residual variant type `Variant ρ'`, with the enumerated keys removed. This is the structural decomposition of an open variant.
- `guard` is the only sequential test, corresponding to CoreFn's `Guard`. Fall-through is expressed by placing `jump j` in `dt_else`.
- `fail` is derived notation for `leaf (perform Partial.abort [τ] Prim.Unit)` and produces a `Partial` effect (D10).

Sharing an alternative's body between several leaves is done by lifting it into a `letjoin` and placing `leaf (jump j ē)`, so that building a decision tree never duplicates code.

```text
letjoin alt0 (x : Int) : Int = … in
case (xs) of
  switchCtor s0 {
    Nil  -> leaf 0
    Cons -> bind h = s0 ! Cons . 0 in
            bind t = s0 ! Cons . 1 in
            leaf (jump alt0 (h))
  }
```

### Where ordering disappears

That branch order carries no meaning is a property of the **Core decision tree**, not of a surface `case`. The two must not be conflated.

A surface `case`, as in other functional languages, tries alternatives top to bottom and runs the first that matches; overlapping patterns are resolved by that order.

```purescript
case x of
  Just 0  -> "zero"      -- swapping these changes the meaning
  Just _  -> "other"
  Nothing -> "none"
```

Compiling this into a decision tree during elaboration **resolves the overlap and removes the ordering**. The example becomes a `switchLit` on the field of `Just`, nested inside a `switchCtor`, and every branch is mutually exclusive.

```text
switchCtor s0 {
  Main.Just    -> bind y = s0 ! Main.Just . 0 in
                  switchLit y { 0 -> leaf "zero" } default -> leaf "other"
  Main.Nothing -> leaf "none"
}
```

This translation is what D9 buys. Neither the Core type checker nor a backend carries a rule about trying alternatives in order. The one construct where sequencing remains is `guard`, since boolean tests cannot be made mutually exclusive.

### Totality

Two requirements must be distinguished.

**What the Core type checker requires: that each switch be locally total.** Every `switch*` must either have a default or exhaust its cases. A tree that does not is rejected, because no value may be left without a destination.

**What it does not require: coverage analysis of source patterns.** Whether nested patterns cover the original program is not checked. Partiality appears in the tree as `fail`, and the term's effect row then contains `Partial`.

```text
switchCtor s0 {
  Main.Nil -> leaf 0
} default -> fail            ← total; carries a Partial effect

switchCtor s0 {
  Main.Nil -> leaf 0
}                            ← rejected; Cons has no destination
```

The condition for having no default differs by node.

| Node | Condition when no default is present |
| --- | --- |
| `switchCtor` | `{Ctor_i}` exhausts the constructors of `T` |
| `switchLit` | unattainable; **a default is mandatory**, since literals cannot be exhausted |
| `switchKey` | the unknown tail is empty and `{k_i} = dom(F)` |

For `switchKey` over a closed variant, a tree that enumerates only some known keys and omits the default is **not admitted**; without this condition a value could be left with no destination at run time.

This separation keeps the trusted core free of a coverage algorithm, which grows complex quickly with GADTs, views, and literal ranges. What it keeps is the local and self-evident check that each dispatch is exhaustive or has a default.
