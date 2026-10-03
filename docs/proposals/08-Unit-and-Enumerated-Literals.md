# Unit and Enumerated Literal Domains

Status: Proposed for a future version

## What is This?

### Background

`Unit` presently sits on the data side of Core:

```text
data Unit = Unit
```

Surface `()` resolves to the nullary constructor `Prim.Unit`. This gives the type's one value a
slightly indirect account: it behaves as a literal in source and at run time, but Core dispatches on
it with `switchCtor`. The reason is local totality. A `switchCtor` may omit its default when its
branches exhaust a data type, while a `switchLit` always requires a default because Core currently
records no literal domain as exhaustible.

`Boolean` exposes the same missing notion from the other direction. It is already an intrinsic
literal type and has exactly two values, but a `switchLit` with branches for `false` and `true` must
still carry a default.

This proposal makes the finite domain explicit and puts `Unit` beside `Boolean`.

### Proposal Sketch

#### 1. `Unit` is an intrinsic literal type

`Prim.Unit` remains the type constructor, but it is an `intrinsic literal` rather than a data
declaration. Core adds the literal `unit`, whose type is `Prim.Unit`, and removes the value constructor
`Prim.Unit`.

Consequently, uses that currently construct the nullary data value use the literal instead:

```text
perform Partial.abort [τ] unit
```

The type remains named `Prim.Unit`; only its one value ceases to be a global constructor.

#### 2. A literal type may publish an enumerated domain

The canonical class of an intrinsic literal records whether its values are enumerated:

```text
literal-domain ::= not-enumerated
                 | enumerated { c1, ..., cn }
```

The list is non-empty, contains distinct literals under literal identity, and every listed literal
has the intrinsic type carrying the domain. `Prim` gives the initial domains:

```text
Unit     enumerated { unit }
Boolean  enumerated { false, true }
Int      not-enumerated
Number   not-enumerated
Char     not-enumerated
String   not-enumerated
```

The term *enumerated* is deliberate. `Int`, `Number`, and `Char` are finite as mathematical machine
domains, but their values are not a branch set that a Core term is expected to enumerate.

#### 3. An exhaustive `switchLit` may omit its default

The default of `switchLit` becomes optional. With a default, the existing rule is unchanged. Without
one, the occurrence's type must have an enumerated domain and the branches must exhaust that domain
exactly:

```text
switchLit u { unit  -> dt }

switchLit b {
  false -> dt_false
  true  -> dt_true
}
```

Branch uniqueness and exhaustion use literal identity, not a library equality operation. In
particular, the distinction fixed by D37 remains: every NaN is one literal, while `0.0` and `-0.0`
are different literals.

This is a local Core check, not source-pattern coverage analysis. A decision tree may still carry a
default where one is convenient, and the separate conservative rule that an or-pattern is refutable
does not change merely because some literal domains are enumerated.

#### 4. Surface spelling

`unit` is the literal's spelling. In a term position, the adjacent characters `()` are syntax sugar
for `unit`. The lexer recognizes only the adjacent spelling as this sugar: `( )` and
`(/* comment */)` are not unit.

Before adoption, the corresponding pattern and type spellings must be stated explicitly. The
natural continuation of the present surface is:

- a pattern `()` is the literal pattern `unit`, and is irrefutable because `Unit` has the singleton
  enumerated domain;
- a type `()` remains sugar for `Prim.Unit`.

Whether both `unit` and `()` are printed by surface tools, or one is chosen as their canonical
output, is a formatter decision rather than a semantic one.

## Consequences

The change removes `Unit` from constructor tables, value exports, constructor arities, and
`switchCtor`. A runtime may represent it as a dedicated immediate value rather than interning a
constructor identity. Results that carry no information — a cell write, an array write, a foreign
`unit`, and similar operations — all produce that same literal.

It also reaches every representation of a literal and every consumer of `Prim.Unit`:

- Typed Core's literal, typing, canonical-forms, decision-tree, and totality rules;
- the Surface AST and pattern irrefutability;
- `.dmo` encoding and interface/signature encoding of intrinsic literal domains;
- Mid IR, bytecode, backends, and foreign marshalling;
- Steam's value representation, module loading, and typed guest bundle;
- the `Prim` surface interface and import/export examples that currently expose the constructor.

The encoded formats therefore need a version change when this is adopted.

## Status and Timing

This proposal does not change the current language. For now, `Unit` remains `data Unit = Unit`, `()`
continues to resolve to `Prim.Unit`, and every `switchLit` keeps a default.

If adopted, the change should be made before the surface decision-tree compiler is finalized. That
avoids teaching the new compiler that unit patterns are constructor patterns and then immediately
replacing that account with a literal one.
