# Surface Syntax for Effect Handlers and Implicit `resume`

Status: Proposed

## What is This?

### Background

The syntax for handlers has not yet been finalized, and the current documentation
only reflects a provisional design. This proposal outlines a refined syntax to
officially freeze the specification.

### Proposal

This proposal introduces a vertical-bar `|` clausal notation to enhance readability and
defines a group-level syntax to factor out repetitive markers. It supersedes the provisional
clause form of the current documentation (`fast log msg = …`, with the continuation bound as
`full log s k = …`): a clause body is introduced by `->`, and the continuation is reached through
`resume`.

Furthermore, to prevent continuations from escaping as first-class values without burdening
the backend with escape analysis, we introduce an implicit, second-class `resume` expression
restricted by syntactical boundaries.

#### 1. Formal Grammar

```plain
handler-group
  ::= group-head? group-marker? cell-decl* group-item+

group-head    ::= effect-name | label
group-item    ::= handler-clause | return-clause

handler-clause
  ::= "|" clause-marker? operation pattern* "->" expression

return-clause
  ::= "|" "return" pattern "->" expression

cell-decl     ::= "var" identifier ":=" expression

group-marker  ::= "full" | "fast"
clause-marker ::= "full" | "fast"
```

- `full`, `fast`, and `resume` are reserved keywords.
- The group marker may stand on the line after the group head, and the `|` of the clauses are
  aligned by layout:

  ```stella
  State
    full | get _ -> ...
         | set _ -> ...
  ```

- A group has at most one `return` clause, which takes no marker. A group without one returns
  the computation's own value.
- The patterns of a clause are irrefutable, as in every other binding position: variables, `_`,
  records, tuples, and constructors of a data type with a single constructor.
- The `var` declarations of a group stand before its first `|`. A cell is visible in the
  operation clauses of its group alone, and not in the `return` clause.

#### 2. Semantics & Desugaring Rules

The scoping rule is formalised as follows: **The `group-marker` serves as the default, and**
**any local `clause-marker` overrides it.**

```text
effective-marker(clause) = clause-marker or group-marker or "full"
```

##### Example 1: Explicit Individual Markers

Each clause can explicitly state its own execution strategy.

```stella
State
  | fast get _ -> ...
  | full set s -> ...
```

##### Example 2: Group Marker Factoring (Sugar)

When operations share the same execution strategy, the marker can be moved to the group level.

```stella
State full
  | get _ -> ...
  | set s -> ...
```

##### Example 3: Local Overriding

A localized clause-marker takes precedence over the group-marker.

```stella
State full
  | get _      -> ...
  | fast set s -> ... -- Locally overrides 'full' to 'fast'
```

This desugars into the canonical form where the `set` operation is handled as `fast` and the
`get` operation as `full`. It is an intentional syntax revision that simplifies complex handlers.

#### 3. Where Groups Stand

##### Top-level Handler Declarations

A top-level handler declaration holds exactly one group, **with its head omitted**: which effect
it handles follows from its signature.

```stella
handler runEmit :: Emit ~> () where
  fast | emit _ -> 42
```

- In the `E ~> ρ` form, the handled effect is `E`.
- In the general form, it is the one element that the thunk's row holds and the result's row
  does not. Where there is not exactly one, the declaration is rejected.
  `(Unit -> a / {| Console |}) -> IO a` handles `Console`, and
  `(Unit -> a / {| Partial, ...e |}) -> Maybe a / {| ...e |}` handles `Partial`.

**The type of a handler remains a function taking a thunk.** A parameter of computation type,
evaluated at the call site only when the callee demands it, is not introduced: deciding whether
to wrap an argument would then depend on the type of whatever function is applied, and a thunk
is inserted by syntax alone ([Top-level Computation Declaration](./05-Toplevel-Computation-Declaration.md)).
Applying a handler rarely needs a thunk written, since the forms below insert it.

##### Handling Expressions

`handle e with …` and `using … handle e` take one list of items, aligned by layout, each of
which is either a group or a handler expression. The two forms differ only in order.

```stella
handle work with
  runToStdout            -- a declared handler from a library (outermost)
  runWithLimit 1_000     -- a handler applied to its arguments
  countEmits             -- a handler declared in this module
  State full             -- a group written in place (innermost)
    | get _ -> resume 0
    | set _ -> resume ()

using
  runConsole
  State full
    | get _ -> ...
handle e
```

- **The items are installed from the top down**: the first is the outermost handler, and each
  later one stands closer to the computation. A clause of an inner group may therefore perform
  an effect an outer item handles, and not the reverse — unless a handler further out, or the
  row of an enclosing annotation, provides it.
- The list desugars to `item₁ (\_ -> item₂ (\_ -> … (\_ -> e)))`; a group is a handler built in
  place and applied likewise. The body is wrapped in a thunk by the syntax itself.
- **An item is a group where its head — an effect name, or a label — is followed by a marker or
  by `|`**, and a handler expression otherwise. A handler is a function, so an expression begins
  with a lowercase name, a qualified name, an application, or a parenthesis, and never takes a
  marker or `|` after it; the two are told apart lexically.
- Items are not separated by commas. Whether a comma-separated form is admitted for a list written
  on one line is left to the layout rules.
- A handler function is not named by the effect it handles (`handle e with Console -> runConsoleIO`
  is not a form): the effect name contributes nothing to the application.

##### Labelled Effects

A group handling a labelled element of the row, `{| cache :: State Int |}`, is headed by the label
alone:

```stella
handle work with
  cache full | get _ -> resume 0
             | set _ -> resume ()
  counter    | fast get _ -> 0
             | fast set _ -> ()
```

- `::` stands in type positions only, so the group head carries no `::`.
- The effect a labelled group handles is the one its clauses' operations belong to, found by
  ordinary name resolution: an operation is a name in scope. Every clause's operation must
  belong to the same effect; where operations of one name belong to several effects in scope,
  the operation is qualified (`State.get`). The elaborator then confirms that the label names an
  element of that effect in the row of the computation handled.
- A labelled group with no operation clause cannot tell which effect it handles, and is rejected.
- The clause heads carry no `@`. An operation of a labelled instance is performed as
  `get@cache ()`, and `@` in a pattern position remains the as-pattern.

---

#### 4. Implicit Second-Class `resume`

To expose continuations in `full` clauses, we introduce a dedicated keyword **`resume`**, rather
than binding an explicit continuation variable (e.g., `| full get _ k -> ...`).

##### Behavioral Differences between Clauses

| Clause Type | `resume` Availability | Continuation Behavior |
| :--- | :--- | :--- |
| **`fast`** | **Prohibited** (Syntax Error) | Implicitly resumes exactly **once** with the evaluated value of the body. (Does not reify a continuation object). |
| **`full` (0 times)** | Allowed | **Aborts/Discards** the continuation. Evaluates the body as the final result of the whole `handle` expression. |
| **`full` (1 time)** | Allowed | Resumes the continuation exactly once (**Linear/Single-shot**). |
| **`full` (Multiple)** | Allowed | Resumes the continuation multiple times (**Multi-shot**). |

#### 5. Linearity and Escape Prevention via Syntactic Boundaries

To guarantee that continuations are **not first-class values**, `resume` cannot be assigned to
variables, partially applied, or passed as an argument. However, developers could still indirectly
reify and leak a continuation into a closure cell using side-effects, as shown below:

```stella
-- !!! EXPORT / ESCAPE ENCOUNTERED (MUST BE BANNED) !!!
handle ... with
  State
    var s := 0
    var k := \x -> x
    | full set s1 ->
        k := (\x -> let _ = resume () in x); -- Captures 'resume' inside a closure
        s := s1
    | fast get _ ->
        let leaked_k = k! in ...
```

##### The Boundary Restriction Rule

To statically prevent such escapes at the surface language level without modifying the Core
semantics or backend, we enforce the following strict syntactic rule:

> **The `resume` expression can only be used within the immediate lexical body of its introducing `full` clause. It must NOT cross any functional boundaries or evaluation-delay boundaries.**

**The body of a handling expression is such a boundary.** `using h handle e` and
`handle e with …` wrap their body in a thunk, and a handler item `h` is an arbitrary function,
free to keep that thunk; a `resume` inside the body would escape through it.

The rule is deliberately strict for now. Relaxing it later only admits more programs, and breaks
none that it accepts today.

##### ❌ Rejected Examples (Boundary Violations)

```stella
| full set s1 ->
    let f = \x -> resume x in ... -- Error: Crosses a lambda boundary
```

```stella
| full set s1 ->
    k := (\x -> resume x); ...    -- Error: Crosses a lambda boundary
```

```stella
| full op x ->
    withLog (\_ -> resume x)      -- Error: Crosses a lambda boundary
```

```stella
| full op x ->
    using h handle resume x       -- Error: Crosses the boundary of a handling expression
```

##### ✅️ Allowed Examples (Valid Control Flow)

Immediate evaluation paths (including conditional branches and composition) are perfectly valid, allowing for rich multi-shot behaviors:

```stella
| full choose _ ->
    if condition then resume true else resume false -- Valid
```

```stella
| full choose _ ->
    let x = resume true in
    let y = resume false in
    combine x y                                     -- Valid Multi-shot
```

#### Compiler Verification Pipeline

During elaboration (after macro expansion and desugaring), the compiler checks each `full` clause against the following rules:

1. `resume` must only appear inside a `full` clause context.
2. Entering a nested lambda or local function definition **invalidates** the availability of the outer clause's `resume`.
3. Entering the body of a handling expression (`handle … with …`, `using … handle …`) **invalidates** it likewise.
4. Entering a nested handler clause **shadows** the outer clause's `resume` (if the inner clause is `full`, a new local `resume` context is established; if `fast`, `resume` is unavailable).
5. Future extensions involving thunks or lazy expressions will treat them as evaluation-delay boundaries equivalent to function boundaries.

Through this design, the desugared Core language can still treat continuations as regular fresh variables (`k`), while the Surface language cleanly enforces the second-class restriction.

**What the backend may rely on is left open.** Core receives the continuation as an ordinary
variable, and the Core type checker verifies nothing about whether it escapes, so a backend
optimization assuming that it does not has no checked ground yet. A mark that Core or the `.dmo`
carries, and a checker can verify, is to be specified when the optimizer is worked on.
