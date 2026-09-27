# Prim and Base

Four layers stand between the trusted core and an application. Each is settled
by someone different, which is what keeps the boundaries between them worth
drawing.

| Layer | What it holds | Settled by |
| --- | --- | --- |
| `Prim` | the types and constructors the rules of Core name | the Core specification |
| `Base.*` | the versioned runtime contract: portable primitive protocols, and the ABI surface a backend implements | the ABI specification and backend conformance profiles |
| `Prelude` | the default portable environment: foundational types, classes, ordinary names, and syntax macros | the standard library specification |
| portable libraries — `Data.*`, `Effect.*`, and the rest | portable API written in Stella over `Prelude` and, where necessary, `Base.*` | their library packages |

`Prim` is visible without being imported; every other layer is imported like
anything else. A module touching `Base.*` says so in its header (D22), so which
code depends on the ABI surface is readable from headers alone.

**A portable library is one to which neither Core nor the ABI gives any
privilege.** The classification is not about who publishes it: `Data.List` is
distributed with the compiler and is a portable library all the same, holding
no standing that a package written by anyone else lacks.

## The dependency direction is one-way

```text
Prim
  ↑
Base.*
  ↑
Prelude
  ↑
Data.* / Effect.* / user packages          Js.* / Wasm.*
  ↑                                              ↑
applications
```

A portable library may reach past `Prelude` to `Base.*` where it must —
`Data.Array` wraps `Base.Array`, while `Effect.State` needs nothing of the ABI
and is written in Stella alone. What no layer does is reach upwards.

**A target namespace stands beside the portable libraries rather than within
them.** `Js.*` and `Wasm.*` sit at the same depth as `Data.*`, and may name what
`Prelude` owns as freely, so `Js.String.fromJSString` returning a `Maybe` is
well placed where the same signature in `Base.String` would not be. Two things
separate them from a portable library: the ABI manifest may supply a target
namespace with intrinsics, and a program importing one has thereby chosen its
target. `Prelude` depends on neither.

### Who owns a foundational identity

Keeping the direction one-way requires deciding where the **identity** of a
foundational type or effect is declared, separately from where its operations
are written. Otherwise `Prelude` and a library downstream of it each need the other.

| Identity | Owned by | Operations |
| --- | --- | --- |
| `List` | `Prelude` | `Data.List` |
| `Maybe` | `Prelude` | `Data.Maybe` |
| `Array` | `Base.Array`, being a manifest intrinsic | `Data.Array`, with literal syntax from `Prelude` |
| `Partial` | `Prelude` | handlers, wherever they are written |
| `Console`, `LiftIO` | `Base.Effect.*`, being standard primitive capabilities | target adapters, and the terminal interpreter |
| `State`, `Except` | the `Effect.*` library declaring each | the same library |

`Array` is the case where the split does visible work. The `[ … ]` macro belongs
to `Prelude`, and because the type is owned upstream, that macro expands to the
low-level construction entries of `Base.Array` rather than to anything in
`Data.Array`. `Data.Array` then adds a convenient API over the same
`Base.Array.Array`, and `Prelude` does not depend on it.

`Partial` is owned by `Prelude` for a different reason: elaboration emits
`perform Partial.abort` for a non-exhaustive match (D10), so the name has to be
resolvable wherever a program is elaborated. **That is a dependency of
elaboration, not of Core** — the Core type checker still never mentions
`Partial` or `fail`, and an effect declaration is what it finds in `Σ`.

What makes the name resolvable is a rule about the surface, not a privilege.

```text
`import Prelude` is written, as every dependency but `Prim` is.
Elaboration emits the fully qualified `Prelude.Partial` for a non-exhaustive match.
A module that does not import `Prelude` therefore cannot contain one.
```

The dependency is on the **module**, as every dependency is: a header names
`Prelude`, never a name within it. Nothing has to enter scope unqualified
either, since what elaboration emits is already fully qualified.

Writing the import is what keeps D22 intact, and it keeps `Prim` the one thing a
header omits. `Prelude` is an ordinary module in every other respect: the
surface header names it, and the Core header records it as it records any import
([Modules](01-Modules.md)). `Prelude.Partial` reaches `Σ` by the ordinary route rather than
being conjured by the elaborator; without the import an emitted `EffectKey`
would name an effect no `Σ` holds, and the `perform` would not typecheck. A
non-exhaustive match in a module that does not import `Prelude` is reported at
the match, and what it asks for is the import.

## What a backend owes the standard environment

Supporting `Prelude` is what lets a backend run ordinary Stella, so the condition
for it is stated against `Prelude` rather than against `Base.*` as a whole.

```text
backend supports the Base ABI profile that Prelude requires
```

Which profile that is belongs to the version of `Prelude` in question, so a
backend states what it implements once and the condition is decided by
comparison. A backend meeting no more than `core-runtime` fails this condition
and is conformant all the same, at the profile it claims: belonging to `Base.*`
and being obligatory stay separate questions.

## Two different axes

`Prim` and `intrinsic` are often conflated. They answer different questions.

| | Question | Answer |
| --- | --- | --- |
| `Prim` | where does a name live, and must it be imported | a reserved module, visible without being imported |
| `intrinsic` | is this type constructor a `data` declaration | a classification `Σ` records |

Neither implies the other.

| | `data` | `intrinsic` |
| --- | --- | --- |
| **in `Prim`** | `Prim.Unit` | `Prim.Int`, `Prim.Function`, `Prim.Variant`, `Prim.IO` |
| **outside `Prim`** | `Main.List`, `Prelude.Maybe` | `Base.Array.Array`, `Base.Function.Uncurried.Fn2` |

`Prim.Unit` is an ordinary data type that happens to be reserved; `Base.Array.Array` is intrinsic and imported like anything else.

## What `Prim` holds

`Prim` holds the vocabulary the rules of [Typing Rules](../03-Typed-Core/05-Typing-Rules.md) and [Modules](01-Modules.md) name, and nothing else. Every kind scheme is empty, so no use site writes `[[κ̄]]`.

```text
Prim.Function : Type -> Row Effect -> Type -> Type
Prim.Record   : Row Type -> Type
Prim.Variant  : Row Type -> Type
Prim.Int      : Type
Prim.Number   : Type
Prim.String   : Type
Prim.Char     : Type
Prim.Boolean  : Type
Prim.Unit     : Type
Prim.IO       : Type -> Type
```

Each is here because at least one rule names it.

| Type constructor | Named by |
| --- | --- |
| `Function` | `λ` and application, and therefore every arrow these documents write as `τ1 -{ρ}-> τ2` |
| `Record` | `{}`, `extend`, `select`, `restrict`, `update`, `merge` |
| `Variant` | `inject`, `weaken`, `absurd`, and the residual type in a `switchKey` default |
| `Int`, `Number`, `String`, `Char`, `Boolean` | `litType`, which gives a literal its type |
| `Boolean` | also the condition of a `guard` |
| `IO`, `Unit` | the entry point `main : IO Unit` |

`Prim` declares one data type.

```text
data Unit = Unit
  -- Prim.Unit : Unit        tag 0, arity 0
```

`Unit` is a data declaration rather than a literal, so a `switchCtor` exhausts it with one branch. As a literal it would fall under `switchLit`, where a default is mandatory because literals cannot be exhausted ([Typing Rules](../03-Typed-Core/05-Typing-Rules.md)).

**`Array` and the uncurried families are not here.** Core names neither, and neither needs to be reachable without an import; they are intrinsic all the same, and they belong to `Base.*`, which the section below places.

## Intrinsic type constructors

An intrinsic type constructor has a kind in `Σ` and no data constructors whatever.

That is not the same as a data declaration with an empty list of constructors, and the difference is load-bearing. The rule for `switchCtor` permits a missing default when `{Ctor_i}` exhausts the constructors of `T`; a type with no constructors would exhaust vacuously, so a `switchCtor` on an `Int` with no branches and no default would pass. **A `switchCtor` whose occurrence has an intrinsic type is ill-formed**, and `switchLit` is what dispatches on those.

`Σ` therefore distinguishes them, and a type constructor entry is one or the other:

```text
T : forall k̄. κ   intrinsic C        where C is the canonical-value class below
T : forall k̄. κ   data { Ctor … }    the constructors the declaration gives it
```

**The class is part of the entry, not a comment on it.** Rules consult it: the typing of an opaque value requires `Σ(T) = intrinsic opaque` ([Semantics](../03-Typed-Core/06-Semantics.md)), and the canonical-forms lemma progress rests on is stated class by class.

### Where an intrinsic comes from

```text
intrinsic
├─ Core intrinsic       Function, Record, Variant, the literal types, IO
└─ manifest intrinsic
   ├─ portable  Base.*        Base.Array.Array, the uncurried families
   └─ target    Js.*, Wasm.*  Js.String.JSString, opaque handles
```

Both are beyond a user's reach. They differ in who settles them: a **Core intrinsic** is fixed by this specification, a **manifest intrinsic** by the versioned ABI specification that a compiler and its backends implement together.

The second splits again by portability, and the split decides where an entry lives rather than how it behaves.

A **portable** manifest intrinsic is one whose observable meaning is the same on every backend, and it lives in `Base.*`. Portable is not the same as universally present: which backends owe it is what a profile says, so an entry of `Base.Array` is owed by every backend claiming a profile that contains it. A backend claiming `core-runtime` alone owes none of `Base.Array` and is conformant all the same, whether or not it happens to supply some.

A **target** manifest intrinsic is one only some targets have, and it lives under the namespace naming that target — `Js.*`, `Wasm.*` — so that a program naming one has thereby chosen its target.

Both reach `Σ` by the one route, `Σ_ABI(M)`, and the ABI manifest names modules of both kinds.

**A target namespace is a root segment, not a prefixed path.** `Js.String` rather than `Platform.JavaScript.String`: the target is what the first segment says, and reading `import Js.String` in a header is what tells a reader the module is not portable. Which roots exist is not open-ended — the ABI manifest names them, one per target it describes, and package resolution owns each as it owns `Base` (above), so no ordinary package may claim `Js` or `Wasm`.

**A build imports the root of the target it is building for, and no other.** The ABI manifest knows several roots and a build selects one target, so target validation rejects a module whose header names a different root. Importing `Js.String` and `Wasm.String` in one build is the same failure met twice over, and it is caught where the target is known rather than left to produce a program that cannot be lowered.

### The canonical-value class

Having no constructors, an intrinsic type gets its values another way. Which way is the entry's **canonical-value class**, and there are five.

| Class | Type constructors | Canonical form | What examines one |
| --- | --- | --- | --- |
| `intrinsic literal` | `Int`, `Number`, `String`, `Char`, `Boolean` | a literal | `switchLit`, `guard` |
| `intrinsic function` | `Function` | `λ`, an unsaturated spine, `openEff`, `rec_i` | application |
| `intrinsic record` | `Record` | `{}`, `extend` | `select`, `restrict`, `update`, `merge` |
| `intrinsic variant` | `Variant` | `inject`, `weaken` | `switchKey`, `absurd` |
| `intrinsic opaque` | `IO`, and every manifest intrinsic | `opaque ω [τ]` | nothing |

`switchCtor` is absent from the last column throughout: it takes a **data** value apart, and no intrinsic has one.

The last row is the one that shapes the others. **Core has no rule that compares or decomposes an opaque value**; it carries one from the `foreign` that produced it to the `foreign` that consumes it. That is also why the class must be mechanically decidable — `opaque ω [Boolean]` must not typecheck, or a `guard` would meet a value that is not `true` and not `false`.

### No declaration creates one

A module declares `data`, `newtype`, and `foreign`. **None of them produces an intrinsic entry**, and there is no surface syntax that does.

The reason is that an intrinsic is not one thing but several, and a declaration would have to supply all of them: a canonical value form, typing rules, an erasure, a backend representation, a convention for crossing the `foreign` boundary, the canonical-forms lemma progress rests on, and whatever equality or observation it admits. Adding one is an extension of the language, Core, and the backend ABI together — not a library.

A compiler therefore builds its initial signature rather than reading it from source.

```text
Prim.Int      : Type                                    intrinsic literal
Prim.Boolean  : Type                                    intrinsic literal
Prim.Function : Type -> Row Effect -> Type -> Type      intrinsic function
Prim.Record   : Row Type -> Type                        intrinsic record
Prim.Variant  : Row Type -> Type                        intrinsic variant
Prim.IO       : Type -> Type                            intrinsic opaque
```

A manifest intrinsic reaches `Σ` the same way, through the ABI manifest, and is then imported by name like any other declaration.

## How `Σ` acquires these names

`Prim` is never imported, so the rules that build `Σ` must put it there before anything else.

```text
Σ_Prim = the intrinsic type constructors of Prim
       ∪ { Unit : Type  data { Prim.Unit } }  with Prim.Unit's tag, arity, and field types
```

[Modules](01-Modules.md) collects type-level declarations into `Σ_ty` before checking any interior. That collection starts from `Σ_Prim` rather than from the imports alone.

```text
Σ_ty = Σ_Prim ∪ Σ_ABI(M) ∪ Σ_imp ∪ { the module's own data and effect declarations }
```

`Σ_ABI(M)` is what the ABI manifest supplies to `M` itself, and is empty for every module it does not name; the ABI manifest names `Base.*` modules and the target namespaces it describes, and no others, and the section on manifest intrinsics below says what it holds and why it comes before the module's own declarations.

Three consequences are worth stating.

**`Prim` is reserved, and `Base` is owned.** Core names are fully qualified, so a module declaring `Int` contributes `Main.Int` and collides with nothing. What must be forbidden is a module supplying a rival `Prim.Int`, or a rival `Base.Int.add` beside the one a backend implements — but the two are forbidden by different parties, and conflating them puts a condition in the checker that the checker cannot decide.

`Prim` is a reserved module name, and **the Core type checker rejects a module named `Prim`**. It can: the compiler builds `Σ_Prim` itself, so a second `Prim` rivals something the checker holds.

`Base` is a reserved prefix, and **ownership of it is verified by package resolution, not by the Core type checker**. The modules of `Base.*` are ordinary source — `foreign` declarations with the manifest supplying what type constructors they need — so nothing in a Core module, or in the `Σ` it is checked against, tells the ABI implementation of `Base.Int` from a forgery of it. What decides is which package a module came from, and only the package implementing the ABI may claim a name under `Base`. A resolver enforces that against the ABI manifest before any module reaches the checker.

Handing the checker a provenance to trust would not improve on this. It would verify nothing, and a trusted unchecked input is what the `newtype` flag is deliberately not ([Modules](01-Modules.md)).

Within a module, declaring one name twice in a namespace is ill-formed as it is anywhere.

**Header completeness is unaffected** (D22). A module's header determines its dependencies, and `Prim` is a dependency of every module without exception, so a build system needs no entry to discover it. Nothing has to be written because nothing varies. `Base.*` is different: a module using `Base.Array.Array` imports `Base.Array`, and the header says so.

**Linking includes `Prim`.** The global environment `G` of [Semantics](../03-Typed-Core/06-Semantics.md) is built from `G_Prim`, which holds the data constructors of `Prim` — `Prim.Unit` alone — beside the definitions of the imported modules. `Prim` is not among those imports, so without `G_Prim` a `Prim.Unit` in the module would have nothing to unfold to and condition (1) of `Σ ⊨ G` would fail.

## The Base runtime contract

`Base.*` is the versioned runtime contract: the portable primitive protocols and
the common ABI surface. It holds two kinds of thing, and only one of them is
something a backend implements.

| Kind | What it is | Implemented by a backend |
| --- | --- | --- |
| **ABI entry** | a `foreign` whose implementation a backend supplies, `Base.IO.bind` and the arithmetic among them | **yes**, where a profile designates it |
| **protocol** | a standard primitive capability, declared as an effect and nothing more | no; it names operations and has no implementation to supply |

An ABI entry is an ordinary `foreign` declaration, checked where it is written
like any other (D23, well-kindedness); what sets it apart is the obligation on
the other side. A protocol is an ordinary `effect` declaration, and an effect
declares operations without implementations ([Effects](../03-Typed-Core/03-Effects.md)) — there
is nothing for a backend to supply, and what interprets one is ordinary Stella
code.

```text
-- ABI entries
Base.Int.add                 : Int -> Int -> Int
Base.Int.sub                 : Int -> Int -> Int
Base.String.length           : String -> Int
Base.String.codePointAt      : Int -> String -> Char    -- faults out of range
Base.Array.Array             : Type -> Type            -- manifest intrinsic
Base.Array.length            : forall a. Array a -> Int
Base.Array.unsafeNew         : forall a. Int -> Array a          -- faults on a negative count
Base.Array.unsafeSet         : forall a. Int -> a -> Array a -> Unit   -- faults out of range
Base.Array.unsafeIndex       : forall a. Array a -> Int -> a     -- faults out of range
Base.Function.Uncurried.Fn2  : Type -> Type -> Type -> Type   -- manifest intrinsic
Base.IO.pure                 : forall a. a -> IO a
Base.IO.bind                 : forall a b. IO a -> (a -> IO b) -> IO b

-- protocols
Base.Effect.Console          effect Console where log : String ->* Unit
Base.Effect.LiftIO           effect LiftIO  where liftIO : forall a. IO a ->* a
```

**A public `IO`, `Int`, or `Array` module is ordinary Stella code over `Base.*`.**
Nothing obliges `Prelude` or a portable library to expose these names as they
stand; the layers above are where a portable API is shaped.

### Where a capability meets its target

A protocol says what a capability offers; a target says how the thing is done.
Three responsibilities fall to three places, and keeping them apart is what lets
a program name a capability without naming a target.

| | Holds | Written by |
| --- | --- | --- |
| `Base.Effect.Console` | the meaning of the capability and the types of its operations | the ABI specification |
| `Js.Console.log` | a native leaf constructing an `IO` value on one target | that target, as an ABI entry |
| `Js.Effect.Console` | the adapter joining the two | ordinary Stella code |

`Js.Console.log` is an ABI entry like any other, and a **target** one: what
obliges a backend to supply it is its own backend manifest, not a `Base` profile.
There is no third manifest: a backend manifest names the target it builds for
and records what it implements on both sides, the `Base` ABI entries and the
entries of its own target root alike. What differs is only the grading — a
`Base` entry may arrive through a profile, while a target entry is recorded one
by one, there being no profile over a target root.

The adapter is an ordinary handler: it removes `Console` from the row and
performs `LiftIO` in its place, carrying the `IO` value the native leaf built.

```text
Js.Effect.Console.lowerConsole
  : forall (e : Row Effect). forall (a : Type).
    Console ∉ e => LiftIO ∉ e =>
    ( Unit -{ ( Console, LiftIO | e ) }-> a ) -{ ( LiftIO | e ) }-> a
  = Λ (e : Row Effect). Λ (a : Type).
      Λ (_ : Console ∉ e). Λ (_ : LiftIO ∉ e).
        λ (thunk : Unit -{ ( Console, LiftIO | e ) }-> a).
          handle ( thunk Prim.Unit ) with
            { handles Console
            ; return (x : a) -> x
            ; fast log (msg : String) ->
                perform LiftIO.liftIO [Unit]
                  ( ( openEff [( LiftIO | e )] Js.Console.log ) msg )
            }
```

**The clause is `fast`** (D28). An adapter translates one operation into another
and gives control straight back, which is exactly what a `fast` clause expresses:
it binds no continuation, and its body has the type `log` resumes with, `Unit`.
Building a continuation here would cost something and buy nothing
([Effects](../03-Typed-Core/03-Effects.md)).

**The source row carries `LiftIO` beside `Console`.** An adapter accepts a
computation that already lifts and returns one that still does, which is what
lets a second adapter into the same target stand after this one: were the source
`( Console | e )`, the assumption `LiftIO ∉ e` would fail exactly where the row
already carries it. Bringing a computation that lifts nothing yet to this shape
is the caller's `openEff`, and the elaborator writes it where a handler is
supplied rather than written
([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)).

**One widening remains inside, and it is not optional** (D8). `Js.Console.log`
has pure arrows while the clause is typed at `( LiftIO | e )`, so it is widened
for the same reason arithmetic is in
[Examples](../03-Typed-Core/08-Examples.md).

**An adapter stays effect-polymorphic.** It performs another operation rather
than executing anything, so no native action is sequenced there and no closed
row is called for. Only the terminal stage, interpreting `LiftIO` into `IO`,
builds with `Base.IO.bind` and is therefore closed ([Effects](../03-Typed-Core/03-Effects.md)).

```text
{ Console, FileSystem, … }        capabilities a program names
       │  target adapters, ordinary Stella code
       ▼
{ LiftIO }                        one capability carrying an IO value
       │  the terminal interpreter, which takes a closed row
       ▼
IO                                a value, inert until executed
       │  D25
       ▼
the runtime ABI executes it
```

Nothing obliges a capability to travel this route. A handler interpreting
`Console` straight into `IO` is equally ordinary, and takes a closed row for the
same reason the terminal stage does.

### Implementation is what varies, not meaning

A `Base` operation has one observable meaning, fixed by the ABI specification,
and backends differ only in how they implement it. A backend free to choose
what `Base.String.length` returns would give one Core term two meanings, which
is what the backend independence of Mid IR exists to prevent.

Representation is a separate matter and stays free. A JavaScript backend may
hold a `String` as a JavaScript string and a Wasm backend as UTF-8 bytes; what
neither may do is let that choice reach the result of a `Base` operation.

### Profiles

Obligation is graded, and a **profile** is a named set of `Base` **ABI entries**
a backend undertakes to implement. A protocol is never among them: an effect
declaration has no implementation for a backend to supply, so nothing about it
is graded.

| Profile | Contents |
| --- | --- |
| `core-runtime` | `Base.IO.pure` and `Base.IO.bind`, together with the execution D25 places outside Core: native leaf actions, world state, and the invocation of `main` |
| `standard` | `core-runtime`, together with `Base.Int`, `Base.String`, `Base.Array`, the uncurried families, and whatever else the `Prelude` of a given version requires |

**A profile is a floor, not a ceiling.**

```text
A backend implements every entry of every profile it claims.
It may implement further entries, which its manifest records.
```

A small backend offering `core-runtime` and part of `Base.Int` is expressible as
it stands: it claims `core-runtime`, records the arithmetic entries it supplies,
and claims `standard` not at all. What decides whether a program builds is the
manifest; a profile is the shorthand a backend claims, not the limit of what it
may hold.

A backend claiming `core-runtime` alone can run a program that performs no
arithmetic; it is conformant at that profile and not at `standard`. Saying so is
more precise than saying that programs using arithmetic happen not to run.

`standard` is the profile the condition above names, so which entries it holds
moves with the version of `Prelude` rather than being fixed once. A portable
library reaching past `Prelude` to a `Base` ABI entry the backend manifest records
nowhere — neither in a profile it claims nor among the entries it adds — is what
target validation rejects.

### Where obligation is recorded

**Not in `Σ`.** `Σ` records every declaration: a foreign scheme for an ABI
entry, an effect declaration for a protocol. What it does not record is which
profile an entry belongs to, or what a backend implements. For type checking a
`Base` ABI entry the answer is the same as for any other `foreign`.

```text
Base.Int.add : Int -> Int -> Int        declared type, trusted
                                        every arrow pure (D23)
```

Which backends implement it is a fact about targets and linking, and it belongs
to a manifest. Two are in play and they answer different questions: the
**ABI manifest** defines the surface and the profiles over it, once per version,
while a **backend manifest** states what one backend implements — the profiles
it claims, and any entries it adds beyond them.

```text
-- ABI manifest
ABI version: stella-base-0.1

profiles:
  core-runtime:
    Base.IO.pure
    Base.IO.bind

  standard:
    includes core-runtime
    Base.Int.*
    Base.String.*
    Base.Array.*
    Base.Function.Uncurried.*
```

```text
-- backend manifest, for one small target
target:             Js
implements profile: core-runtime
implements also:    Base.Int.add, Base.Int.sub
                    Js.Console.log
```

Three stages then divide the work, and none of them duplicates another.

| Stage | What it establishes |
| --- | --- |
| type checking | the declared type is well-kinded and every arrow is pure (D23) |
| target validation | the backend manifest records every entry the program uses — each `Base` ABI entry, through a profile it claims or beyond them, and each target ABI entry — and every target root the program imports is the selected target's |
| linking | `Σ ⊨ G` condition (3): each `δ_f` returns what it claims, performs no proper effect and runs no reified computation it constructs, applies no Stella function value, terminates, and has no observational effect — faulting among them — where its declaration asserts `#observ(none)`, all of it asked of the calls respecting the entry's ABI preconditions (D42) ([Semantics](../03-Typed-Core/06-Semantics.md)) |

**An unsupported entry is rejected at target validation, not at run time.** A
program naming an ABI entry the chosen backend does not implement fails to
build, rather than building and faulting where the call is reached. This holds
of a target entry as of a `Base` one: importing `Js.Console` says which target
the program wants, and whether `Js.Console.log` is among what that backend
implements is a separate question, settled at the same stage.

### What the ABI specification must fix per ABI entry

- **Observable meaning**, in terms that name no backend
- **Whether it may fault**, and on which inputs ([Semantics](../03-Typed-Core/06-Semantics.md)). This is what a reader of the entry needs; for an optimizer it is not a fact of its own, faulting being one of the things the observational class is defined by, and the bullet below is what carries it there
- **Whether it is an operation, and the code it carries where one is.** An
  operation is named by a code rather than by its entry in a `.dmo`, and that code
  is the manifest's to fix for the life of a version
  ([Encoding](../05-Backend/02-Encoding.md))
- **Whether it returns `IO`.** An entry reaching the **world** returns `IO` — a
  file, a clock, a console, and anything else that outlives the values the program
  itself holds. An entry that stays within those values need not: it may be pure in
  its type and carry an **observational effect** instead. What it may touch is
  **state its arguments reach, and state it creates during the call that is reached
  only through what it returns**. The second half is `Base.Array.unsafeNew`, whose
  array is reachable from no argument — it is fresh, and the call hands it back —
  and without it the pure interface a portable `mapArray` is written over could not
  exist. The division is between reaching the world and reaching the program's own
  values, and **not** between mutating and not mutating
  ([Semantics](../03-Typed-Core/06-Semantics.md))
- **The division is a criterion and not a model.** Neither kind of state appears in
  Core's reduction relation, which records no store, so what an observational entry
  does lies outside what that relation describes and rests on conformance
  ([Semantics](../03-Typed-Core/06-Semantics.md)). Whether to write such a store
  into the relation is open
  ([Open Questions](../99-Open-Questions/01-Open-Questions.md))
- **Whether it asserts `#observ(none)`.** An entry with no observational effect says
  so at its declaration, and one that says nothing is read as one that may observe
  ([Modules](01-Modules.md)). The assertion is strong and covers faulting, so an
  entry the specification fixes as faulting on some input cannot carry it, and one
  whose result depends on its arguments alone and which never faults may. Together
  with `returnsIO`, read off the result type, this is the whole of what an optimizer
  is given ([Interface](../05-Backend/03-Interface.md))

**A `Base` signature ranges over `Prim` types and portable manifest intrinsics.** A standard
library type such as `Maybe` standing in one would fix that type's
representation for every backend, and would make the ABI surface depend on the
layer built over it. A leaf that can fail therefore faults or returns a sentinel,
and a portable library is where a total wrapper is written. What mechanism, if
any, should enforce this is open ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

### The operations of `stella-base-0.1`

Eight entries of this version are **operations**: a `.dmo` names one by a code rather
than through its foreign table, and whatever executes it carries the entry out
itself ([Encoding](../05-Backend/02-Encoding.md)). Their meaning is fixed here, in
terms that name no backend, and so is which of them may fault.

| Entry | Meaning | Faults | `#observ(none)` |
| --- | --- | --- | --- |
| `Base.Int.add`, `Base.Int.sub` | addition and subtraction **modulo 2³², the result read as a 32-bit signed integer** (D37) | never | yes |
| `Base.String.length` | the number of Unicode scalar values in the string (D27) | never | yes |
| `Base.String.codePointAt` | the scalar value at a **scalar index**, counting from zero | on an index outside the string | no |
| `Base.Array.length` | the number of slots the array has, which is the count it was created with | never | yes |
| `Base.Array.unsafeNew` | an array of that many slots, none of them written | on a negative count | no |
| `Base.Array.unsafeSet` | write the element into that slot of the array, and return `Unit` | on an index outside the array | no |
| `Base.Array.unsafeIndex` | the element at an index | on an index outside the array | no |

**A negative count faults rather than being left undefined**, and this is not
symmetry for its own sake. It is the one place every backend has to do something
deliberate anyway — a host whose allocator rejects a negative length would otherwise
raise something of its own, which is not a fault and does not propagate like one —
and the check happens once per allocation rather than once per read, so it costs
what the entry costs nothing to pay. A count of zero is an array of no slots and is
not an error.

**`Base.Array.length` is an operation like the rest, and it is the entry that shows
a mutable structure does not make every entry over it observational.** A slot count
is fixed where the array is created and no entry of this version changes it, so
reading one is reading an immutable property of the argument, exactly as
`Base.String.length` is. It faults on nothing, writes nothing, and creates nothing,
so it carries the annotation and is Core-modelled besides
([Semantics](../03-Typed-Core/06-Semantics.md)). **It is an operation for the same
reason as its siblings**: what a slot count is belongs to the ABI, and whatever holds
the array is what can read it, so nothing outside the machine could carry it out
without being told the representation.

**The last column happens to agree with the one before it in this version, and does
not follow from it.** What the annotation asserts is the absence of an
**observational effect** — a hidden read or write, an observable identity, a fault —
and faulting is one of three ([Modules](01-Modules.md), D41). For the five entries
that touch nothing the agreement is the whole story: each depends on its arguments
alone, so faulting is the only thing that could exclude it. For the unsafe three it
is a coincidence. Each of them faults, so reading the column off faulting gives the
right answer; each of them would be excluded anyway — `unsafeNew` hands back an array
a program can tell from every other one, `unsafeSet` writes, and `unsafeIndex` reads
what that write left. **No entry of this version separates the two**, so the rule is
stated rather than demonstrated, and an entry that is total and
still excluded is a case a later version should expect rather than be surprised by.
An indexing entry is therefore a barrier to an
optimizer, which is the price of its being partial, and a total wrapper written over
it in a portable library is an ordinary Stella function with no such standing.

**Wrapping is what every backend owes**, not what each host happens to do: one on a
host that traps wraps instead, and one on a host that wraps does not check. Either
is implementable everywhere, which is why the choice has to be made here — two
backends disagreeing would give one program two results, and a differential test
between them would be comparing nothing.

**An index is a scalar index and not an index of code units**, which is the split
`String` already rests on: a backend holding UTF-16 counts and indexes scalar values
all the same.

#### `unsafeIndex` carries the one precondition of this version

`unsafeNew n` produces an array of `n` slots and writes none of them, so
`unsafeIndex` has a case its specification above does not cover: an index inside the
array, naming a slot nothing has written.

**That case is a precondition rather than a behaviour**, and **only** that case is.
The range is decided first and is fully specified either way; the precondition
applies to what is left ([Semantics](../03-Typed-Core/06-Semantics.md), D42).

```text
unsafeIndex xs i    out of range             a fault, on every backend
                    in range, written        the element
                    in range, not written    the precondition, violated
```

**Being out of range is not a precondition violation**, and the distinction is what
every backend's obligation rests on: an index outside the array faults, and a
backend that did anything else there would be non-conformant. What is unspecified is
narrower than "outside the specified case" — it is the third line alone, reached only
after the index has been found to be in range.

**A violating program is outside the language's guarantees, type safety included.**
This is not a licence granted to backends so much as a boundary drawn around what
the specification claims: preservation, progress, and the rest are stated over terms
that respect preconditions, and a term that does not is one they say nothing about.
Stating it here is what keeps "undefined" from being read as "unspecified but safe".

**No implementation is obliged to detect a violation, and none is forbidden from
doing so.** A backend may carry, on each array, which of its slots have been written
and fault on a read of one that has not; that backend is conformant, and a program
violating the precondition then runs there and nowhere else — which is precisely the
difference an unspecified case admits. **Neither behaviour may be made a conformance
condition**, in either direction.

**What the specification declines to do is require the check**, and the reason is
where it would stand: on every read, which is the operation a portable array library
is built out of. Nor is it generally removable — an optimizer would have to prove a
slot written, which is the analysis this specification declines to require. A
backend willing to pay for the diagnostic is free to.

**The obligation is discharged one layer up, not by every author.** `Data.Array`
hands back no array with a slot left unwritten — its `mapArray` writes every slot of
the array it allocated before returning it — so an application reaching `unsafeIndex`
through that library respects the precondition without knowing there is one. That is
what `unsafe` names in these entries, and why they are exported for a library to wrap
rather than for a program to reach.

**A fill would remove the precondition and cost more than it removes.** An
`unsafeNew : Int -> a -> Array a` is total and loses nothing in expressiveness — an
array with elements needs an element — but it obliges a builder to have one before it
has computed any, and a fill written and then overwritten is work every allocation
pays.

**The negative count is the same trade answered the other way**, and the difference
is instructive. That check is once per allocation rather than once per read; a host
whose allocator rejects a negative length would otherwise raise something of its own,
so backends genuinely diverge there rather than merely being unconstrained. So it
faults, and this one does not.

### `Base.IO.pure` and `Base.IO.bind`

```text
foreign Base.IO.pure : forall a. a -> IO a
foreign Base.IO.bind : forall a b. IO a -> (a -> IO b) -> IO b
```

Their `pure` and `bind` are distinct from the `Prim.IO` type constructor they
are typed with. **`Base.IO` is imported like any other module**, so a module
using them names it in its header and header completeness is untouched (D22).

The value a saturated `Base.IO.pure` returns is opaque, `IO` having neither
literals nor constructors to be built from ([Semantics](../03-Typed-Core/06-Semantics.md)).

**The continuation of `Base.IO.bind` is a pure arrow.** Every arrow in a
`foreign` type has an empty effect row (D23), so `( a -{f}-> IO b )` cannot be
declared; and the semantics would not hold either, since deferring `k` until the
`IO` is executed would run the residual effect `f` outside the dynamic context
of the handler that installed it ([Effects](../03-Typed-Core/03-Effects.md)).

Executing these two is the runtime ABI's obligation (D25), which is why they are
fixed here rather than left to the surface, and why they alone constitute the
`core-runtime` profile.

## Text: the meaning is portable, the representation is not

`String` is a sequence of **Unicode scalar values**, and `Char` is one. This is
the meaning every backend presents, whatever it holds in memory.

| | Representation | Free to choose |
| --- | --- | --- |
| JavaScript backend | a JavaScript string, UTF-16 code units | yes |
| Wasm and native backends | UTF-8 bytes | yes |
| what a `Base.String` operation returns | scalar values, counted and indexed as such | **no** |

Splitting the two is what keeps the same program computing the same thing
everywhere. Were `String` instead a sequence of whatever code unit the target
holds, `length "😀"` would be 2 on JavaScript, 4 on a UTF-8 backend counting
bytes, and 1 on one counting scalars — a difference in the meaning of a program
rather than in its representation, reaching `switchLit`, equality, and every
decomposition into `Char`.

The cost falls where representation and meaning diverge: a JavaScript backend
implements `Base.String.length` as a count of scalar values rather than as
`.length`, and a slice never divides a surrogate pair.

### Lone surrogates

A JavaScript string may hold an unpaired surrogate, which is not a scalar value.
**A Stella `String` may not.** A literal is a sequence of scalar values, a `Char`
is a scalar value, and a string arriving through the FFI is validated.

Code that must carry a JavaScript string through unchanged uses an opaque type
of its own rather than `String`, and that type is a target manifest intrinsic of
the JavaScript namespace.

```text
-- ABI manifest
module Js.String
  intrinsic opaque JSString : Type
```

```purescript
module Js.String (JSString, fromJSString, fromJSStringLossy, toJSString) where
  import Prelude

  foreign fromJSString      :: JSString -> Maybe String
  foreign fromJSStringLossy :: JSString -> String
  foreign toJSString        :: String -> JSString
```

A `Maybe` may stand here where it may not in a `Base` signature: `Js.String` is
a target module rather than part of the portable ABI, so it sits downstream of
`Prelude` and may name what `Prelude` owns.

### Naming says which unit is meant

An operation names the unit it counts in, so that no reader has to infer it.

| Name | Unit | Where it lives |
| --- | --- | --- |
| `codePointAt` | Unicode scalar value | `Base.String`, being portable |
| `utf16CodeUnitAt` | UTF-16 code unit | `Js.String`, or an encoding library |
| `utf8ByteAt` | UTF-8 byte | the namespace of the target that has it, or an encoding library |

A name such as `codeAt` says none of the three and is not used.

**Target-specific operations live in the namespace of their own target, not in
`Base.*`.** Both are imported, so by D22 a module observing UTF-16 directly says
as much in its header — `import Js.String` names the target in its first
segment — and code that is portable is distinguishable from code that is not by
reading headers. Using UTF-16 inside a backend is unremarkable; making it
observable through the ordinary `String` is what would cost portability.

## Literal domains

Every literal domain is fixed (D37).

| Type | Domain |
| --- | --- |
| `Int` | a 32-bit signed integer, `-2147483648` to `2147483647` |
| `Number` | IEEE 754 binary64 |
| `Char` | a Unicode scalar value, so no unpaired surrogate |
| `String` | a sequence of those, so no unpaired surrogate |
| `Boolean` | `true` and `false` |

**A domain belongs to Core rather than to a target**, because two backends
disagreeing on one would give a Core term two meanings — the thing the backend
independence of Mid IR exists to prevent. Representation is the separate matter it
is for `String`: a backend holds an `Int` however it likes, and what it may not do
is let that choice reach a result.

**Literal identity is equality of the value, and `switchLit` is what needs it**
([Terms and Matching](../03-Typed-Core/04-Terms-and-Matching.md)). For an `Int`, a
`Char`, a `String`, and a `Boolean` that is ordinary equality. For a `Number` it is
equality of the bit pattern, with all NaNs taken as one, so `0.0` and `-0.0` are
**different** literals and a NaN is one literal. IEEE equality decides nothing
usable here, identifying the two zeros and separating a NaN from itself, so a
backend's dispatch implements the relation above rather than `==`.

**Whether arithmetic wraps or faults** on overflow is the ABI specification's, one
answer for every backend, and `stella-base-0.1` fixes it: `Base.Int.add` and
`Base.Int.sub` wrap and fault on nothing (above).

One thing about a literal remains open, and it is not a domain. **Which surface
token denotes which value** is the lexer's: `42`, `0x2a`, and `0b101010` are one
literal, and `"\n"` and `"\u{A}"` are another. `switchLit`
compares the value, never the spelling
([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

## Manifest intrinsics, which live outside `Prim`

**The ABI manifest supplies type constructors and nothing else.** It is not source, and no module may write an intrinsic entry; this is how the ABI surface states what it supplies and to whom.

```text
-- ABI manifest
module Base.Array
  intrinsic opaque Array : Type -> Type

module Base.Function.Uncurried
  intrinsic opaque Fn2 : Type -> Type -> Type -> Type
```

The operations are ordinary source, written in the module the manifest names.

```purescript
module Base.Array (Array, length, unsafeNew, unsafeSet, unsafeIndex) where
  foreign length      :: forall a. Array a -> Int
  foreign unsafeNew   :: forall a. Int -> Array a
  foreign unsafeSet   :: forall a. Int -> a -> Array a -> Unit
  foreign unsafeIndex :: forall a. Array a -> Int -> a
```

**`length` is an operation too**, so all four entries of this module are carried out by whatever executes the code rather than by a host table: an array is an opaque value whose representation belongs to the implementation holding it, and a slot count is as unreachable from outside as an element is.

**The construction entries are these two and no more**, and what they are is settled
by what a portable `mapArray` has to be written over: somewhere to put the elements,
and a way to put them there. Everything above that — a literal, a conversion, a
builder that grows — is a portable library's, written in Stella over these.

**None of the three is pure in the sense the type suggests, and none returns `IO`.**
An array is reached through the program's own values rather than through the world,
so the division that sends an entry to `IO` does not send these there; what they have
instead is an **observational effect**, which appears in no type (D41). `unsafeNew`
creates an identity a program can tell from another, `unsafeSet` writes, and
`unsafeIndex` reads what that write left. This is exactly why a pure `mapArray` can
be written at all, and exactly why none of the three carries `#observ(none)`.

**`unsafeSet` takes the array last and returns `Unit`.** The order is what makes a
partial application useful over the array rather than over the index, and the result
is `Unit` because there is nothing else to return: the array a caller has is the
array that was written.

**`fromList` is not among them.** `List` belongs to `Prelude`, and a `Base`
signature mentions only `Prim` types and portable manifest intrinsics, so a conversion between
the two is `Data.Array`.

Splitting it this way keeps the manifest to what only it can express. A `foreign` is checked wherever it is written — every arrow pure (D23), the type well-kinded — and a manifest entry would either duplicate that or become a trusted input for no reason. It also leaves the module free to hold Stella code beside its primitives, which a portable library needs: `Data.Array.mapArray` is written in Stella and uses `unsafeIndex` ([Modules](01-Modules.md)).

Checking such a module therefore needs its own entries in scope before its declarations are collected. Writing `Σ_ABI(M)` for what the manifest supplies to `M` — empty for every module the manifest does not name — the collection of [Modules](01-Modules.md) reads:

```text
Σ_ty = Σ_Prim ∪ Σ_ABI(M) ∪ Σ_imp ∪ { the module's own data and effect declarations }
```

An importer sees the entry through `Σ_imp`, by the ordinary route. **What it sees is not a data type**: the import path is the same, the entry is not. `Base.Array.Array` keeps its `intrinsic opaque` class, so a `switchCtor` on it is as ill-formed in the importing module as anywhere else.

Core names neither `Array` nor `Fn2`, and the module a name lives in is a question of visibility rather than of status. Both are imported, and a header that omits them is incomplete.

That `Array` has first-class surface syntax is not a reason to move it. **The syntax, the type, and Core are three independent things**: a library syntax macro can expand `[ e1, e2 ]` into a call, leaving Core with an ordinary `foreign` application and an opaque value. Where a standard surface is wanted, it is the standard library that provides it.

Arithmetic is the same story without an intrinsic type of its own: `Base.Int.add : Int -> Int -> Int` operates on a Core intrinsic, so it needs no manifest entry and is an ordinary `foreign` of `Base.Int`. A module using it imports that one.

**`Fn2` and its siblings take no effect row** (D19). Being uncurried and having effects are orthogonal, so `Fn2 a b (IO c)` covers what PureScript needs `EffectFn2` for.

**What may fault, and on which inputs, is unsettled.** An unchecked array index can fail, and no Stella type describes it; a fault is not an effect and no handler intercepts it ([Semantics](../03-Typed-Core/06-Semantics.md)). Enumerating the faulting entries, and the preconditions of each, belongs to the ABI specification.

## Names that are not `Prim`

`List` belongs to `Prelude`, not to `Prim`; the vertical slice of [Examples](../03-Typed-Core/08-Examples.md) declares its own `Main.List` rather than reaching for either.

`Partial` is not here either. It is an ordinary effect declaration of `Prelude` ([Effects](../03-Typed-Core/03-Effects.md)), and `fail` is derived notation for `perform Partial.abort [τ] Prim.Unit` that elaboration expands. The Core type checker never mentions either.

## What is not a name at all

**`merge` is a term constructor, not a value of `Prim`.** The type these documents give it,

```text
forall (r : Row Type). forall (s : Row Type). r # s => Record r -> Record s -> Record ( r ⊎ s )
```

describes the rule for `merge e1 e2`; it declares no global name. The same holds of `extend`, `select`, `restrict`, `update`, `inject`, `weaken`, and `absurd`. Writing them as values as well as constructors would be the duplication Core exists to avoid.
