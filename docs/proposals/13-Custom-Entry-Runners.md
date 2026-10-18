# Custom Entry Runners

Status: Proposed

## What is this?

### Background

[Implicit Effect Runner](./01-Implicit-Effect-Runner.md) runs a computation entry point with the
standard runner, `Base.IO.Effect.runIO`, fixed. This proposal lets a program choose another.

### Proposal

A runner is declared with an attribute of its own:

```stella
@[entry_runner]
myrunner
  :: forall a.
     (Unit -> a / {| LiftConsole |})
  -> IO a

myrunner k = ...
```

On the user side, a specific runner is selected via an argument of the entry point's attribute:

```stella
@[entrypoint runner=myrunner]
main :: Unit / {| Console |}
main = Console.log "Hello, World!"
```

In this case, the system applies an implicit lowering plan for `{| Console |}` into
`{| LiftConsole |}`, wraps the computation in a thunk, and passes it to `myrunner`. For the time
being, the type signature allowed for `@[entry_runner]` is strictly limited to
`forall a. (Unit -> a / σ) -> IO a`, where `σ` is a closed effect row, and no additional value
argument is permitted.

If no runner is specified, the standard runner is used. If a specific runner is specified, only
that runner is applied; the system performs no automated discovery of custom runners.

## Open questions

- **The type of `runner`.** `entrypoint` takes no parameter today. `runner` would be a keyword
  parameter of it, and the type it is given has to admit every runner `@[entry_runner]` admits,
  each with its own closed row, which no closed parameter type does today; the standard runner
  would have to be nameable as its default. `myrunner` is resolved as an ordinary name, and counts
  as a dependency of the module.
- **The stub's annotation.** The standard runner's stub annotates the thunk at `( LiftIO )`; a
  custom runner's stub annotates it at the runner's own closed row `σ`.
