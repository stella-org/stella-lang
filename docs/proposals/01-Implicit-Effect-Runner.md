# Implicit Effect Runner

Status: Proposed

## What is this?

### Background

Without this feature, developers have to write the entrypoint function as:

```stella
main :: IO Unit
main = runIO \_ -> handle ... with ...
```

where `runIO :: forall a. a / {| LiftIO |} -> IO a` reifies effectful terms -- whose
effect rows contain only the `LiftIO` effect -- as values in the `IO` monad. Due to
the core semantics, `runIO` must take a thunk rather than an effectful term, making
`runIO \_ -> ...` seem somewhat clunky. Developers would expect an traditional helloworld
program to be written in a much simpler style, such as:

```stella
main = Console.log "🌍️"
```

This proposal aims to make this possible.

### Proposal

The type annotation for the entrypoint specifies the computation type before applying any runners.

```stella
@[entrypoint]
main :: Unit / {| Console |}
main = Console.log "🌍️"
```

The right-hand side of `@[entrypoint]` is initially type-checked against the standard `IO Unit`.
If this succeeds, it is directly used as the entrypoint. If the types do not match, the system
infers it as a computation type `a / ρ` and checks it against the provided type annotation, if
present. Next, letting `σ` be the closed effect row accepted by the runner, the system looks
for a unique implicit lowering plan such that `ρ ~> σ`. If the plan combined with the runner
application yields an `IO Unit`, the compiler generates a hidden stub to be passed to the runtime
environment. The original main in the source code retains its annotated computation type.

```stella
main        : Unit / {| Console |}
$entry_main : IO Unit

$entry_main =
  runIO \_ ->
    lowerConsole \_ ->
      main
```

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

In this case, the system applies an implicit lowering plan for `{| Console |} ~> {| LiftConsole |}`,
wraps the computation in a thunk, and passes it to myrunner. For the time being, the allowed type
signature for `@[entry_runner]` will be strictly limited to `forall a. (Unit -> a / σ) -> IO a`,
where `σ` is a closed effect row, and no additional value arguments are permitted.

If no runner is specified, the standard runner is used.

If a specific runner is specified, only that runner is applied; the system will not perform
any automated discovery of custom runners.
