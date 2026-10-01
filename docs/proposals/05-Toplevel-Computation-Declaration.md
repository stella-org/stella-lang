# Top-level Computation Declaration

Status: Accepted

## What is This?

### Background

This proposal is a prerequisite for the [Implicit Effect Runner](./01-Implicit-Effect-Runner.md) proposal.

That proposal allows developers to write the entry point simply as

```stella
@[entrypoint]
main :: Unit / {| Console |}
main = Console.log "🌍️"
```

This, however, contradicts the semantics Core defines head-on. In Core, an effect row is carried by a function arrow, `τ1 -{ρ}-> τ2`, and nowhere else; a top-level **value** is therefore type-checked in the context of the empty row `()`.

This proposal resolves that contradiction.

### Proposal

A third kind of top-level term declaration, the **computation**, is added beside values and functions.

A computation is a declaration that is **not a function but carries an effect row**:

```stella
effect Random where
  random :: Unit ->* Number

randomInt :: Int / {| Random |}
randomInt =
  let n = random () in
  ceil n
```

In general, it is a top-level declaration `e` that

1. takes no arguments, and
2. carries a type annotation, which is mandatory.

Together, the two say that a computation is a term whose type is, in general, `forall ā. C => τ / ρ`.

Note:

- `τ1 -> τ2 / ρ` is not a computation declaration but a function: called with an argument of type `τ1`, it performs `ρ` and returns a value of type `τ2`.
- `e :: (τ1 -> τ2) / ρ`, on the other hand, is a computation declaration and not a function: referring to it performs `ρ` and yields a function of type `τ1 -> τ2`.
- A computation type `τ / ρ`, one with no arrow at the level `/` applies to, may be written only at the top of the signature of a top-level declaration, inside its quantifiers and constraints. It is rejected anywhere else — as an argument type `(τ / ρ) -> σ`, as the type of a record field, or as the parenthesized result `τ1 -> (τ2 / ρ)` — since no value corresponds to it there. Where a suspended computation is wanted, the thunk type `Unit -> τ / ρ` is written instead.

#### Rules

1. This proposal adds no new constructor to Core terms: a computation declaration desugars to an ordinary thunk in Core. The Core term corresponding to a computation declaration `e :: forall ā. C => τ / ρ` is

    ```text
    x : forall (ā : κ̄). C => Unit -{ρ}-> τ
      = Λ(ā : κ̄). Λ(_ : C). λ(_ : Unit). e
    ```

    Here `C` stands for row constraints. A type class constraint becomes a dictionary parameter `λ(dict : D)` in its place, ahead of the `Unit` parameter (see rule 2).

    In particular, a computation declaration `e :: τ / ρ` with neither a quantifier nor a constraint corresponds simply to the nullary thunk

    ```text
    x : Unit -{ρ}-> τ = λ(_ : Unit). e
    ```

    taking a `Unit` argument.

2. Name resolution tells references apart as `ResolvedValueRef x` and `ResolvedComputationRef x`, and leaves the distinction in the resolved AST. The elaborator lowers the latter to `x ⟨type arguments⟩ Prim.Unit`. Since the application is built after the type arguments are instantiated, even a polymorphic computation declaration does not depend on the expected type.

    Where a constraint in `C` is a type class constraint, it is not a Core constraint but a dictionary argument, supplied by synthesis. The reference then lowers to `x ⟨type arguments⟩ ⟨dictionaries⟩ Prim.Unit`: after the type arguments are instantiated, a synthesis goal is created for each dictionary, and `Prim.Unit` is applied last. A row constraint in `C` (`Lacks`, `Disjoint`) stays a Core constraint, applied as any other.

3. The surface scheme (`τ / ρ`), the lowered Core scheme (`Unit -{ρ}-> τ`), and the kind of declaration (value / computation / foreign / constructor …) are kept apart. An importer type-checks `x` as a computation against the surface scheme, and uses the lowered scheme when it builds the Core global. Care must be taken not to replace the scheme in the existing catalog with `τ / ρ`.

4. **Where a thunk is inserted is closed under syntax.** A computation is wrapped automatically
    only in positions where the syntax itself takes "the body of a computation", such as
    `handle e with …`, and in the runner stub that `@[entrypoint]` generates. An ordinary
    function application wraps nothing.

    ```stella
    runIO randomInt          -- wrong: randomInt runs first
    runIO (\_ -> randomInt)  -- passed as a thunk
    ```

    The entry-point stub is generated as surface syntax, `runIO (\_ -> main)`: the thunk is
    the lambda written there, and the reference to main inside it is forced as any other.
    Implicit handlers are inserted at the lambda's body by the ordinary rules, so nothing
    specific to the entry point is needed beyond generating the stub.

5. **An empty row is admitted.** `x :: Int / {||}` is an explicitly pure nullary computation,
    evaluated again at each reference. Forbidding it would make whether a declaration is admitted
    depend on the normalized row after its kind has been settled by syntax, and with open rows and
    row polymorphism involved the rule would become uneven. Where an unintended re-evaluation is
    a concern, a lint can suggest a value declaration.

#### Meaning

A computation runs each time it is referred to. This is close to a parameterless `def x: Int` in Scala, and unlike a value of Haskell's `IO`, which runs when it is bound.

```stella
random' :: Number / {| Random |}
random' = random ()     -- a computation declaration: each mention of random' draws anew
```

This is a deliberate departure from the monadic meaning familiar from Haskell and PureScript, and **a cost in readability** as well: `let a = randomInt` runs `randomInt` rather than referring to it by name.

Where the monadic meaning is wanted, it must be written explicitly as a thunk:

```stella
randomInt :: Unit -> Int / {| Random |}
randomInt _ = let n = random () in ceil n
```

No marker of execution such as `randomInt!` is attached. IDE hovers and diagnostics show that a declaration is a computation.
