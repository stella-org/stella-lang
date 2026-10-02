# Implicit Effect Runner

Status: Proposed

## What is this?

### Background

Without this feature, developers have to write the entrypoint function as:

```stella
main :: IO Unit
main = runIO \_ -> handle ... with ...
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

The type annotation for the entrypoint specifies the computation type before applying any runners.

```stella
@[entrypoint]
main :: Unit / {| Console |}
main = Console.log "🌍️"
```

#### How it works

**An entrypoint is treated according to the form of its declaration**:

| Declaration Form | Signature | Treatment |
| --- | --- | --- |
| Value | `main :: IO Unit` | used directly as the entrypoint |
| Computation | `main :: Unit / ρ` | a runner and a lowering plan are applied, as below |
| Others | without an annotation, and effectful | rejected with a hint of adding an annotation |

The second is the case treated in the manner described here.

When the system finds the entrypoint `main` is not an `IO`-value, then it generates the stub
which reifies the found `main` as an `IO`:

```stella
main :: Unit / ρ
main = e

-- generated
$entry_main :: IO Unit
$entry_main = runIO (\_ -> main)
```

Note that this first step is purely syntactic work, and the only step
necessary to make this work, because the rest of the job is standard elaboration:

- Since `main` is a computation declaration, it is desugared into the nullary thunk
  `main : Unit -{ρ}-> Unit = λ(_: Unit). e`
- The `main` in the RHS of the `$entry_main` is the same computation declaration, so referring
  to it is desugared into the thunk forcing `main ()`
- Combining these two results in `runIO (λ(_ : Unit). main ())`, which is effectively the `e` --
  the original body of `main`
- the argument to the `runIO` is checked against `Unit -> a / {| LiftIO |}`, so the elaborator
  inserts an implicit handler which lowers `ρ` down to `{| LiftIO |}` if available

#### Possible Future Improvemens

Initially, the standard runner will be hidden within the toolchain, and `@[entrypoint]`
will implicitly utilize it. In the future, when custom runners are exposed to users,
we plan to allow declarations like the following:

```stella
@[entry_runner]
myrunner
  :: forall a.
     (Unit -> a / {| LiftConsole |})
  -> IO a

myrunner k = ...
```

On the user side, a specific runner can be explicitly selected via an attribute on the entrypoint:

```stella
@[entrypoint runner=myrunner]
main :: Unit / {| Console |}
main = Console.log "Hello, World!"
```

> Note: `entrypoint` takes no parameter yet. `runner` would be a keyword parameter of it, and
> the type it is given has to admit every runner `@[entry_runner]` admits, each with its own
> closed row, which no closed parameter type does today; the standard runner, hidden in the
> toolchain, would have to be nameable as its default. `myrunner` is resolved as an ordinary
> name, and counts as a dependency of the module.

In this case, the system applies an implicit lowering plan for `{| Console |} ~> {| LiftConsole |}`,
wraps the computation in a thunk, and passes it to `myrunner`. For the time being, the allowed type
signature for `@[entry_runner]` will be strictly limited to `forall a. (Unit -> a / σ) -> IO a`,
where `σ` is a closed effect row, and no additional value arguments are permitted.

If no runner is specified, the standard runner is used.

If a specific runner is specified, only that runner is applied; the system will not perform
any automated discovery of custom runners.
