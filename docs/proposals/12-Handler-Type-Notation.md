# The Handler Type Notation `~>`

Status: Accepted

## What is This?

### Background

[Handler Surface Syntax](./02-Handler-Surface-Syntax.md) writes a handler declaration's signature
as `E ~> ( t̄ )`, and [Effect Handlers](../technical-references/02-Surface-Language/02-Effect-Handlers.md)
fixes it today as a shorthand for one shape, standing as a handler declaration's signature alone:
written anywhere else, `~>` is rejected ([Syntax](../technical-references/02-Surface-Language/05-Syntax.md)).

Two readings of `~>` remain open, and the elaboration of handler declarations depends on which
is taken:

- **an abbreviation a declaration writes**, which is what the documents say today, or
- **a type of its own**, which may stand wherever a type stands, so that a handler can be a
  parameter, a result, a field, or a component of a record, with a type that says what it
  translates.

The choice reaches the syntax, the scheme a handler declaration is given, where its quantifiers
stand and where the `Lacks` atoms of its residual row come from, how its value parameters are
typed, what the `.dmi` holds, the Surface AST (`HandlerSignature`'s `Capability` and `General`),
and how an implicit handler is registered. Handler declarations are therefore not elaborated
until it is settled.

### Proposal

1. **`~>` is a derived type notation**, and not a new type of Core: it stands for an ordinary
   polymorphic function type, written out below, and nothing beneath the surface sees it.
2. **The target row appears on both sides**, in the row of the thunk taken and in the row of the
   result.
3. **`...e` is the residual row the source and the targets are taken out of**, the same variable
   on both sides.
4. **A handler value is an ordinary first-class function**, and `~>` stands wherever a type
   stands.
5. **That a value is a handler, and that it is implicit, is metadata** — `SortHandler`, the
   `implicit` modifier, and an interface's `ImplicitHandler { handler, source, targets }` — read
   off the declaration, and no part of what `~>` means.

## 1. The expansion

```text
E ~> ( t1, …, tn )

  ≝  forall (e : Row Effect). C̄ =>
       forall (a : Type).
         ( Unit -{ ( E, t1, …, tn | e ) }-> a ) -{ ( t1, …, tn | e ) }-> a

     C̄ = E ∉ e, t1 ∉ e, …, tn ∉ e, normalized
```

`e` and `a` are named apart from every name the program writes. The empty target is `()`:
`E ~> ()` is `forall e. E ∉ e => forall a. ( Unit -{ ( E | e ) }-> a ) -{ e }-> a`. In general,
the surface spelling of the expansion is `forall e a. (Unit -> a / {| E, t̄, ...e |}) -> a / {| t̄, ...e |}`,
the atoms written by no one and read off its rows, as below.

**No form is added beneath the surface.** Core holds the expansion, as any type a signature
writes; the Core type checker, the `.dmi`, a backend, and a synthesizer see an ordinary
`forall` over an ordinary function type, and the Core type checker validates a handler as it
validates any other function (D29).

**The `Lacks` atoms come from the rows the expansion writes, by the rule every type is read by.**
The thunk's row spreads `e` beside `E` and each `tᵢ`, so its sharpness needs `E ∉ e`, `t1 ∉ e`,
…, `tn ∉ e`. As for any type, they are normalized, each once and in the one order normalization
gives, and **stand directly under the innermost binder that binds a variable they are about**,
which is `e`'s ([Elaboration](../technical-references/02-Surface-Language/01-Elaboration.md)): no
order or place of their own is given them, and so `C̄` stands between `e`'s binder and `a`'s. The
source and the targets are known elements, so the disjointness of `( E, t̄ )` and `e` is these
atoms and nothing besides. `Console ~> ( LiftIO )` is `forall e. C̄ => forall a. …` with `C̄`
the two atoms `Console ∉ e` and `LiftIO ∉ e` in the order normalization puts them in, whichever
is written first. The shape
[Effect Handlers](../technical-references/02-Surface-Language/02-Effect-Handlers.md) gives
`runConsole` today, with both quantifiers in front of the atoms, is not this one, and is
corrected with it.

**The source and the targets are effects applied to their arguments, with keys pairwise
distinct.** Each is unlabelled, as a handler handles one effect and a labelled instance is
handled in place ([Effect Handlers](../technical-references/02-Surface-Language/02-Effect-Handlers.md)).
A key written twice is rejected where the second is written, as a row holding a key twice is:
`State Int ~> ( State String )` and `Log ~> ( Log )` are refused.

**Only `e` and `a` are the expansion's own.** A type variable `E` or a target mentions is bound
by what binds a type variable where the `~>` stands, as any other type variable written there
is, and the expansion binds none of them:

- **in a signature** — a value's, a handler declaration's, a local one — it is quantified
  implicitly at the signature's head as any variable the signature mentions, or by a `forall`
  written there: `forall s. State s ~> ()`, or `State s ~> ()` alone;
- **in a type synonym's body**, it is one of the synonym's parameters, or bound by a `forall` in
  the body: `type Stateful s = State s ~> ()`;
- **in a field of a data type**, it is one of the declaration's parameters, or bound by a
  `forall` in the field: `data Runner s = Runner (State s ~> ())`;
- **in an annotation**, it is one the context binds around it, as any variable an annotation
  writes.

A variable these leave free is reported as it is anywhere else; a `~>` quantifies nothing beyond
`e` and `a`.

## 2. The target row on both sides

The narrower expansion,

```text
forall e a. (Unit -> a / {| E, ...e |}) -> a / {| t̄, ...e |}
```

reads well and does not compose. A handler lowering `Console` into `LiftIO` is applied, in
practice, to a computation that performs `LiftIO` already — it is where every lowering handler
after the first stands once two of them lower into one target, and where the insertion of
implicit handlers puts it, since a computation is brought to a row carrying every target before
any handler is applied. Under the narrower expansion, that computation's row would be
`( Console, LiftIO | e' )` matched against `( Console | e )`, so `LiftIO` would have to be in `e`,
and the result `( LiftIO | e )` would hold `LiftIO` twice, which a row never does: `LiftIO ∉ e`
fails, and the application is refused.

With the targets on both sides, `Console ~> ( LiftIO )` is
`forall e a. (Unit -> a / {| Console, LiftIO, ...e |}) -> a / {| LiftIO, ...e |}`, and

- a computation performing `{| Console |}` is passed, widened by a wrapping fit to
  `{| Console, LiftIO |}`;
- one performing `{| Console, LiftIO |}` already is passed as it stands;
- the application performs `{| LiftIO |}`;
- `LiftIO` is never put into `e`, so it is held once.

```stella
-- runConsole :: Console ~> ( LiftIO ),  runFS :: FS ~> ( LiftIO )
handle work with
  runConsole
  runFS
-- work : Unit -> a / {| Console, FS, LiftIO |}
-- runFS instantiated at e = ( Console ), runConsole at e = ()
```

## 3. The residual row

`e` is one variable, on both sides: what the handler passes through untouched, holding neither
the source nor a target. The answer `a` is the same on both sides, so a `~>` never changes the
answer; a handler that does is written in [the general form](../technical-references/02-Surface-Language/02-Effect-Handlers.md#the-general-form).

The expansion names `e` itself, so the question of how far an anonymous `...` is shared — one
signature, or a declaration written on several lines — does not arise for `~>`.

## 4. Handler values are first-class

**`~>` stands wherever a type of kind `Type` stands**: the argument or the result of an arrow, a
field of a data type, a record's field, the body of a type synonym, an annotation, and a local
signature, as well as a handler declaration's signature. The grammar already reads it where an
arrow stands (`type1 ::= typeOp "~>" typeOp`), so `(E ~> ( F )) -> τ` and `τ -> E ~> ( F )` parse
today; what changes is that they are no longer rejected.

```stella
applyHandler :: (Console ~> ( LiftIO )) -> (Unit -> Int / {| Console |}) -> Int / {| LiftIO |}
applyHandler h work = h work

type Lowering = Console ~> ( LiftIO )

data Interpreters = Interpreters { console :: Lowering, fs :: FS ~> ( LiftIO ) }
```

**Where it stands as an argument, its quantifiers stand there**, so the type is of rank 2, and a
handler passed to it is checked as any higher-rank argument is: the quantifiers and the atoms
expected are opened where the argument stands, and the argument is elaborated under them. A
handler declared at the top level, or bound as a parameter, passes as it is, `applyHandler
runConsole w`. **An application does not**: `applyHandler (runWithLimit 1000) w` puts
`runWithLimit 1000` under the `Λ` the opened quantifiers make, it is no form that may move under
a λ, and it is refused, a parameter asked for
([η-expansion](../technical-references/02-Surface-Language/01-Elaboration.md#η-expansion)):
`applyHandler (\t -> runWithLimit 1000 t) w` is accepted. This is a consequence of a handler
being an ordinary function, and a handler type of Core would not lift it without an
introduction form of its own.

**Where it stands as a result, its quantifiers stand there too.** Nothing is moved: a `~>` is
expanded where it is written, and a type synonym standing for one is read through as any synonym
is, so `type Lowering = Fuel ~> (); mkLimit :: Int -> Lowering` and `mkLimit :: Int -> Fuel ~> ()`
are one scheme, with nothing to remember of where the `forall` came from. A handler's value
parameters come ahead of the thunk, as
[Effect Handlers](../technical-references/02-Surface-Language/02-Effect-Handlers.md#parameters)
says, and ahead of the expansion's quantifiers as well:

```text
handler runWithLimit (limit :: Int) :: Fuel ~> () where …

  ⟹  runWithLimit : Int -> forall (e : Row Effect). Fuel ∉ e =>
                      forall (a : Type). ( Unit -{ ( Fuel | e ) }-> a ) -{ e }-> a
```

**A function whose type is a `forall` or a constraint where it is applied is instantiated
there**, as a global is where it is referred to: each quantifier a fresh metavariable — an
instantiation row for one at `Row Effect` — and each constraint required where the function
stands. `runWithLimit 1000` is at the type above past its first arrow, and applying it to a thunk,
as `handle work with runWithLimit 1000` does, instantiates that type where the application
stands; so does `r.console work`, a handler read out of a field. This is a rule of application,
of every type and not of `~>` alone: today such an application is refused, its function being
equated with an arrow it is not, so the rule admits programs and refuses none.

**This proposal decides the function position alone.** It instantiates a `forall` where the
function holding it is applied, and nothing else: what becomes of a `forall` an application gives
where it is not applied — bound to a local without a signature, `let h = runWithLimit 1000 in …`,
whose type a metavariable would have to be solved at — is part of how much higher-rank
polymorphism to infer, and of impredicativity, both left open
([Open Questions](../technical-references/99-Open-Questions/01-Open-Questions.md)). A local that
holds a handler polymorphically is written with its signature, and as a function where its
right-hand side is no form that may move:

```stella
let h :: Fuel ~> ()
    h t = runWithLimit 1000 t
in …
```

`h` is checked against the expansion, its quantifiers and atoms opened, and `runWithLimit 1000`
is applied to `t` under them, instantiated there by the rule above, `Fuel ∉ e` assumed where it
is required.

## 5. What is metadata

**A handler declaration is a declaration form, and its value an ordinary global.** That it was
declared with `handler` is kept beside its type, as the interface's `SortHandler`; that it is
`implicit`, by the modifier; and what insertion reads of it, as `ImplicitHandler { handler,
source, targets }`, read off the `~>` the declaration writes — the condition of an implicit
handler "written with `~>`" is a condition of the declaration, not of its type
([Effect Handlers](../technical-references/02-Surface-Language/02-Effect-Handlers.md#implicit-handlers)).

So a value at a `~>` type is never a candidate for insertion because of its type. A parameter,
a local, a field, or a top-level value written as a function, at the very type a handler
declaration has, is none; the search runs over the implicit handler declarations of `Ξ`, and
nothing else. Nor does the type say whether the clauses are `fast` or `full`, whether there is a
return clause, or whether a continuation is duplicated: those are the declaration's, checked
where it is declared.

## Not proposed

### A handler type of Core

A type of its own, `E ~> ρ` in Core, would let Core tell a handler from a function of the same
shape. It would buy:

| With a Core type | Needed now |
| --- | --- |
| Restricting how a handler is made, by an opaque type and an introduction form of its own | No: nothing relies on a handler having been made by a declaration |
| Finding implicit handlers through higher-order functions and records, by type | No: insertion searches declared globals, by their metadata |
| A local handler value as an implicit candidate | No: excluded on purpose |
| Recognizing a handler a Core module declares when its interface is made | No: a module written in Core declares no implicit handler |
| A calling convention or an optimization of its own for handler application | Not yet: left to the optimizer |

None is needed, and each can be had later. Turning `~>` into a Core type later changes the
schemes of the `.dmi` of every module that writes it, which is the cost to weigh then; nothing a
source program means changes.

### `~>` as a declaration's abbreviation alone

Keeping today's rule loses the type of a handler as a parameter, a result, or a field — written
out in full instead, the target row twice and the residual named by hand — and gains nothing the
expansion does not already give the declaration.

### A separate signature line for a handler declaration

Writing a handler declaration's signature on a line of its own, as a value's is, is a question
of the declaration's syntax, independent of what `~>` means, and is not part of this proposal.

## Worked example: composing two handlers

```stella
compose :: (E ~> ( F )) -> (F ~> ( G )) -> E ~> ( F, G )
compose h1 h2 thunk = h2 (\_ -> h1 thunk)
```

`compose` is accepted: under `forall e. C̄ => forall a.`, `C̄` holding `E ∉ e`,
`F ∉ e`, and `G ∉ e`, `h1` is instantiated at `( G | e )` and `h2` at `e`, and the result
`( G | e )` is widened into `( F, G | e )`. The composite written `E ~> ( G )` is refused, and
rightly: it would let `F` be in `e`, and `h2`, installed around the computation, would then
handle the operations of `F` the computation performs itself, which a handler of `E` must leave
alone. An intermediate target stays a target of the composite.

## Consequences

- **Syntax**: the rejection of `~>` other than as a handler declaration's signature is removed;
  a source or a target that is no effect applied to its arguments, a labelled one, and a key
  written twice stay rejected.
- **Name resolution and the Surface AST**: `~>` is a form of `Type` held as its source and its
  targets; a handler declaration still holds the effect it handles, the source of its `~>` or the
  element its signature written in full removes, and the targets where it writes `~>`.
- **Elaboration**: a `~>` is read as its expansion where the type is read, its atoms normalized
  and placed by the rule every type's are; a function whose type is a `forall` or a constraint is
  instantiated where it is applied. A handler declaration then desugars as
  [Effect Handlers](../technical-references/02-Surface-Language/02-Effect-Handlers.md) describes —
  a `handle` under a thunk, and the region of its cells around it — by the machinery of handling
  expressions.
- **Interface**: a handler's scheme is the expansion; `SortHandler` and the implicit handler
  table are kept as metadata.
- **Documents**: Syntax, Surface AST, Name Resolution, Elaboration (the instantiation of an
  applied function), and Effect Handlers — `~>` no longer "a shorthand for one shape" standing in
  one place, and `runConsole`'s Core type given its atoms under `e`'s binder, ahead of `a`'s.
- **Open Questions**: *whether to provide annotated predicative rank-n checking* is answered by
  what elaboration already does — a parameter annotated at a polytype is bound at it and
  instantiated at each use, and an expression checked against an expected `forall` opens it
  rigidly — together with the instantiation of an applied function above, so the question is
  removed. *How much higher-rank polymorphism to infer* and impredicativity stay open.

## Open questions

- **Diagnostics and hovers show the expansion.** Writing it back as `~>` where a type is the
  expansion of one is left out.
