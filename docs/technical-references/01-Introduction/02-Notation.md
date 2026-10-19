# Notation

This document lists the notation used throughout the Stella design documents.
Notation confined to a single document is introduced where it is used.

## Metavariables

| Symbol | Ranges over |
| --- | --- |
| `k` | kind variables |
| `κ` | kinds |
| `ε` | row element kinds (`Type` or `Effect`) |
| `q` | quantifiable kinds |
| `a`, `b` | type variables |
| `τ`, `σ` | types |
| `ρ`, `r`, `s`, `e` | rows (`e` usually an effect row) |
| `ς` | an argument spine of a constructor or foreign |
| `α` | a spine argument: `[τ]`, `[•]`, or a value |
| `θ` | a kind and type substitution |
| `δ_f` | the implementation of a foreign `f` |
| `ω` | the payload of an opaque value, held by the backend |
| `k` | row keys |
| `s` | the symbol of a `SymbolKey` |
| `T` | type constructors |
| `Ctor` | data constructors |
| `E` | effect constructors |
| `x`, `y` | value variables |
| `j` | join points |
| `ℓ` | region names |
| `ι` | region layouts, `( k1 : σ1, …, kn : σn )` |
| `ν` | locations of by-need cells, which exist only at run time |
| `o` | occurrences |
| `C` | constraints |
| `Σ`, `Γ`, `Δ`, `Ω` | contexts |
| `Ψ` | the metavariable context, which exists only in Core⁺ |
| `?α`, `?m`, `?r` | metavariables, which exist only in Core⁺ |
| `Int`, `Unit`, `Function`, … | type constructors from `Prim`. These documents write them unqualified for readability; their Core names are fully qualified, as in `Prim.Function` |

`k` and `s` each range over two things, and position tells them apart. A `k` is a kind variable under the binder of a kind scheme and a row key everywhere else; an `s` is a row variable where a row is expected and the symbol of a `SymbolKey` where a key is.

## Sequences

An overbar (combining macron, U+0304) denotes a sequence of zero or more items.

```text
k̄    =  k1, …, kn         a sequence of kind variables
κ̄    =  κ1, …, κn         a sequence of kinds
ā    =  a1, …, an         a sequence of type variables
τ̄, σ̄  =  τ1, …, τn        sequences of types
b̄_i  =  b_i1, …, b_in     an indexed sequence
x̄, ē, v̄                   sequences of value variables, terms, and values
```

`T : forall k̄. κ` reads as `T : forall k1 … kn. κ`. A sequence may be empty, in which case the binder disappears entirely.

## Symbols

| Symbol | Reading | Defined in |
| --- | --- | --- |
| `⊎` | row union | [Types](../03-Typed-Core/01-Kinds-and-Types.md), [Rows](../03-Typed-Core/02-Rows.md) |
| `k ∉ ρ` | Lacks constraint | [Rows](../03-Typed-Core/02-Rows.md) |
| `ρ1 # ρ2` | Disjoint constraint | [Rows](../03-Typed-Core/02-Rows.md) |
| `Γ ⊨ C` | constraint entailment | [Rows](../03-Typed-Core/02-Rows.md) |
| `Γ ⊢ τ1 ≡ τ2` | type equality | [Types](../03-Typed-Core/01-Kinds-and-Types.md), [Rows](../03-Typed-Core/02-Rows.md) |
| `can(τ)` | the canonical form of a type, which equality compares | [Rows](../03-Typed-Core/02-Rows.md) |
| `⟪ P ; U ⟫` | a canonical row: a set of key–payload pairs and a set of tails | [Rows](../03-Typed-Core/02-Rows.md) |
| `⟨ F ; T ⟩` | the normal form of a sharp row | [Rows](../03-Typed-Core/02-Rows.md) |
| `A ⇀ B` | finite map, that is, a partial function | [Rows](../03-Typed-Core/02-Rows.md) |
| `l ↦ τ` | an entry of a finite map | [Rows](../03-Typed-Core/02-Rows.md) |
| `Γ ⊢ κ qkind` | `κ` is a quantifiable kind | [Kinds](../03-Typed-Core/01-Kinds-and-Types.md) |
| `Γ ⊢ k key ε` | `k` is a well-formed key for rows of `ε` | [Types](../03-Typed-Core/01-Kinds-and-Types.md) |
| `Γ ⊢ C ok` | constraint well-formedness | [Types](../03-Typed-Core/01-Kinds-and-Types.md) |
| `σ ->* τ` | an operation signature: an argument type paired with the type the continuation resumes with. **Not a function type** | [Effects](../03-Typed-Core/03-Effects.md) |
| `C => τ` | constraint abstraction, erased at run time | [Types](../03-Typed-Core/01-Kinds-and-Types.md) |
| `e [•]` | constraint application, carrying no proof term | [Typing Rules](../03-Typed-Core/05-Typing-Rules.md) |
| `e [τ]` | type application | [Terms](../03-Typed-Core/04-Terms-and-Matching.md) |
| `T [[κ̄]]`, `M.x [[κ̄]]` | instantiation of a kind scheme. Omitted when the scheme is empty | [Kinds](../03-Typed-Core/01-Kinds-and-Types.md) |
| `τ1 -{ρ}-> τ2` | notation for `Function τ1 ρ τ2`. Core has no arrow syntax | [Types](../03-Typed-Core/01-Kinds-and-Types.md) |
| `τ1 -> τ2` | notation for `Function τ1 () τ2`, a pure function | [Types](../03-Typed-Core/01-Kinds-and-Types.md) |
| `Γ; Δ ⊢ e : τ ! ρ` | term typing. The row to the right of `!` is the ambient effect row | [Typing Rules](../03-Typed-Core/05-Typing-Rules.md) |
| `Σ ⊢ decl ⊣ Σ'` | declaration checking, extending the signature | [Modules](../06-Modules/01-Modules.md) |
| `G ⊢ N; e → N'; c` | reduction of a store and a term to a store and a configuration, a term or a fault; `G ⊢ e → c` where the store stands | [Semantics](../03-Typed-Core/06-Semantics.md) |
| `cursorΣ(M.g, ς)` | the unconsumed declared type and accumulated substitution of a spine | [Semantics](../03-Typed-Core/06-Semantics.md) |
| `ftv(τ)` | the type variables occurring free in `τ`, and likewise of a row | [Typing Rules](../03-Typed-Core/05-Typing-Rules.md) |
| `dom(F)` | the keys a finite map is defined on | [Rows](../03-Typed-Core/02-Rows.md) |
| `·` | the empty context | [Typing Rules](../03-Typed-Core/05-Typing-Rules.md) |
| `⟹` | desugaring of surface syntax | [Rows](../03-Typed-Core/02-Rows.md) |
| `∈ ∪ ∩ ∖ ∅` | ordinary set operations | — |

## Surface syntax in examples

Examples labelled `purescript` are surface syntax. Examples labelled `text` are Core, or grammar and inference rules. Core is never written by hand in ordinary use; it is the output of elaboration.
