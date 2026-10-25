# Implicit Effect Runner

Status: Accepted

## What is this?

### Background

Without this feature, developers have to write the entrypoint function as:

```stella
main :: IO Unit
main = Base.IO.Effect.runIO \_ -> handle ... with ...
```

where `runIO :: forall a. (Unit -> a / {| LiftIO |}) -> IO a` reifies effectful terms -- whose
effect rows contain only the `LiftIO` effect -- as values in the `IO` monad. Due to
the core semantics, `runIO` must take a thunk rather than an effectful term, making
`runIO \_ -> ...` seem somewhat clunky. Developers would expect a traditional helloworld
program to be written in a much simpler style, such as:

```stella
main = Console.log "🌍️"
```

This proposal aims to make this possible. It relies on
[Top-level Computation Declaration](./05-Toplevel-Computation-Declaration.md), which gives
a declaration such as `main :: Unit / {| Console |}` its meaning.

### Proposal

The type annotation for the entrypoint specifies the computation type before applying any runner.

```stella
@[entrypoint]
main :: Unit / {| Console |}
main = Console.log "🌍️"
```

1. **`@[entrypoint]` marks the declaration a program starts from**, a value of type `IO Unit`
   or a computation of type `Unit / ρ` with `ρ` closed.
2. **A computation is run by the standard runner**, `Base.IO.Effect.runIO`, an ordinary Stella
   global the `Base` ABI names.
3. **The compiler generates a stub that applies the runner** to the computation's thunk under a
   written annotation, so that implicit handlers lower `ρ` to `{| LiftIO |}` by the ordinary
   insertion rules (D29).
4. **The runner and the handlers are reached through the module's header.** The compiler adds no
   import.
5. **A module's interface records which global its entry point is**, and a build hands that
   identity to whatever runs the program. Nothing searches for an entry point at run time.

## 1. The attribute and what it admits

**`@[entrypoint]` is declared by `Prim` and takes no parameter.** A module carries it on at most
one declaration, and that declaration has a complete signature: none, or a partial one, is
refused where the attribute stands.

| Signature, normalized | Treatment |
| --- | --- |
| `IO Unit`, a value | the entry point as it stands |
| `Unit / ρ`, a computation, `ρ` closed | run by the standard runner, through the stub below |
| anything else | refused where the attribute stands |

**What is refused**: a quantifier, a Core constraint, or a synthesized parameter on the spine; a
result other than `Unit`; and a row that is not closed. A program starts in one way, so the entry
point is one closed type rather than a scheme to instantiate.

## 2. The standard runner

**`Base.IO.Effect` declares `LiftIO` and the runner beside it**, in Stella source:

```stella
module Base.IO.Effect where

import Base.IO (pure, bind)
import Base.Continuation as Continuation

effect LiftIO where
  liftIO :: forall a. IO a ->* a

runIO :: forall a. (Unit -> a / {| LiftIO |}) -> IO a
runIO thunk =
  handle thunk () with
    LiftIO
      | reifiable full liftIO action k -> bind action (Continuation.continue k)
      | return x -> pure x
```

**The runner is an entry the `Base` ABI names, and not a compiler primitive.** Its name is fixed
by the ABI, and its implementation is the ordinary code above, which a backend compiles as it
compiles any module; nothing is hidden in the toolchain. The row it takes is closed because it
sequences a native action before the continuation, which `Base.IO.bind`'s pure arrow requires
([Effects](../technical-references/03-Typed-Core/03-Effects.md)).

## 3. The stub

**Where the entry point is a computation, the compiler generates a value declaration that runs
it:**

```stella
@[entrypoint]
main :: Unit / ρ
main = e

-- generated
$entrypoint :: IO Unit
$entrypoint = Base.IO.Effect.runIO ((\_ -> main) :: Unit -> Unit / {| LiftIO |})
```

**The annotation is what makes insertion happen.** An argument is checked against the type the
function's instantiation gives it, and that is no checking boundary
([Elaboration](../technical-references/02-Surface-Language/01-Elaboration.md#explicit-checking-boundaries)):
written as `runIO (\_ -> main)`, a `main` performing `Console` would be a row mismatch. The
annotation writes the arrow, so the λ is a boundary at `( LiftIO )`, its body is checked to its
complete source row, and a unique plan of implicit handlers lowers that row to `( LiftIO )`
([Effect Handlers](../technical-references/02-Surface-Language/02-Effect-Handlers.md#insertion)).
The rest is standard elaboration: `main` inside the λ is a computation reference, forced as any
other is, and `$entrypoint` is a top-level value with a signature, its right-hand side a boundary
at `()`.

**Where several capabilities lower independently into `LiftIO`, the plan is ambiguous as it is
anywhere** (D29). The entry point is not a special case: its author writes the composition.

**The generated global is private.** Its name, `$entrypoint`, is one source cannot write, and is
fresh in the module, which has one entry point. The name is no part of the ABI: whatever runs the
program reads the identity from the interface (§5). It stands in the module's declaration table as
a value of type `IO Unit`, and in no export, no catalog, and no scope a name is resolved in. The
attribute stays on the declaration its author wrote it on, and is not moved to the stub. The stub is
an ordinary value declaration, initialized as any other is.

## 4. Imports

**The runner and the implicit handlers the lowering uses must be reachable through the imports the
module's header writes.** The compiler adds no import and the stub widens no search: `runIO` is
reached as any qualified global is, and the handlers are those of `Ξ`
([Effect Handlers](../technical-references/02-Surface-Language/02-Effect-Handlers.md#the-judgement)).
A runner the header does not reach is reported where the attribute stands.

**`Ξ` is read through the ordinary value exports of the directly imported modules.** There is no
export table of implicit handlers. A directly imported module's value export publishes a global's
identity, and where the declaration of that global is marked an implicit handler in the interface
of the module declaring it, the handler is in `Ξ`. A re-export publishes the same identity, which
is followed to the declaration and its mark in the same way. A handler a directly imported module
merely imports, without exporting it, is not in `Ξ`. A module importing `Prelude` then reaches
whatever handlers `Prelude` re-exports; a test fixture, before `Prelude` exists, imports
`Base.IO.Effect` and the module declaring each handler it lowers through. What a module only
depends on transitively still changes no search.

## 5. The interface records the entry point

**A module's interface holds `entrypoint`, the identity of the global the program starts from**, or
nothing where the module has no `@[entrypoint]`. For a value, it is that value's global; for a
computation, the stub's. The identity is the Core global as the module's Core declares it, so no
naming convention becomes part of the ABI ([Interface](../technical-references/05-Backend/03-Interface.md)).

## 6. How a program starts

**The entry point is decided in layers, and nothing beneath the compiler searches for one.**

1. The build target decides which module is the entry module.
2. That module's `@[entrypoint]` decides the global.
3. The module's `.dmi` holds the global's identity.
4. The build hands that identity to the backend or to the machine as an input of its own.
5. The runtime executes the identity it is handed. It reads no attribute and scans no `.dmo`.

**A dependency's entry point competes with nothing.** A library may carry one for running it alone,
and only the entry module's interface is read.

**The user-facing `--entry` and `--entry-global` options of `steam run` are withdrawn**, the
attribute deciding what they chose. A set of `.dmo` files alone does not say which global to run,
so the machine is given the identity by the build — through a program descriptor the build writes,
or through the build calling the machine directly ([Abstract Machine](../technical-references/07-Runtime/01-Abstract-Machine.md)).

## Not proposed

### Custom runners

Selecting a runner other than the standard one — an `@[entry_runner]` declaration and an
`@[entrypoint runner=…]` argument — is a proposal of its own,
[Custom Entry Runners](./13-Custom-Entry-Runners.md). Here the runner is fixed.

### Several entry points in one module

A module carries at most one `@[entrypoint]`. Naming several, and choosing among them by a build
target or an argument, is left to a later proposal.

## Consequences

- **Attributes, Modifiers, and Directives**: the `entrypoint` row states what §1 admits and that a
  computation is run by `Base.IO.Effect.runIO`.
- **Prim and Base**: `LiftIO` moves from `Base.Effect.LiftIO` to `Base.IO.Effect`, with `runIO`
  beside it as an entry the ABI names.
- **Modules**: the entry point rule is the attribute's; `M.main : IO Unit` no longer makes a module
  executable by its name.
- **Interface**: the `entrypoint` field.
- **Effect Handlers**: `Ξ` is read through the value exports of the directly imported modules,
  re-exports included, each followed to the declaration's implicit-handler mark (§4).
- **Abstract Machine** and **JavaScript**: the entry point is the identity the build hands over;
  `--entry` and `--entry-global` are withdrawn; the `run` command's regression table in the
  Implementation Plan follows.
- **Top-level Computation Declaration**: its rule 4 uses the annotated stub of §3.

## Open questions

- Whether the machine is handed the identity by a program descriptor or by the build calling it is
  settled where it is implemented.
- Whether the machine keeps a low-level way to run a named global, for its own tests, apart from
  the user-facing command.
