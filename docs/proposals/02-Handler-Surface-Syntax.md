# Surface Syntax for Effect Handlers and Implicit `resume`

Status: Proposed

## What is This?

### Background

The syntax for handlers has not yet been finalized, and the current documentation
only reflects a provisional design. This proposal outlines a refined syntax to
officially freeze the specification.

### Proposal

This proposal introduces a vertical-bar `|` clausal notation to enhance readability and
defines a group-level syntax to factor out repetitive markers.

Furthermore, to prevent continuations from escaping as first-class values without burdening
the backend with escape analysis, we introduce an implicit, second-class `resume` expression
restricted by syntactical boundaries.

#### Formal Grammar

```plain
handler-group
  ::= effect-name group-marker? handler-clause+

handler-clause
  ::= "|" clause-marker? operation pattern* "->" expression

group-marker  ::= "full" | "fast"
clause-marker ::= "full" | "fast"
```

#### Semantics & Desugaring Rules

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

---

#### 3. Implicit Second-Class `resume`

To expose continuations in `full` clauses, we introduce a dedicated keyword **`resume`**, rather
than binding an explicit continuation variable (e.g., `| full get _ k -> ...`).

##### Behavioral Differences between Clauses

| Clause Type | `resume` Availability | Continuation Behavior |
| :--- | :--- | :--- |
| **`fast`** | **Prohibited** (Syntax Error) | Implicitly resumes exactly **once** with the evaluated value of the body. (Does not reify a continuation object). |
| **`full` (0 times)** | Allowed | **Aborts/Discards** the continuation. Evaluates the body as the final result of the whole `handle` expression. |
| **`full` (1 time)** | Allowed | Resumes the continuation exactly once (**Linear/Single-shot**). |
| **`full` (Multiple)** | Allowed | Resumes the continuation multiple times (**Multi-shot**). |

#### 4. Linearity and Escape Prevention via Syntactic Boundaries

To guarantee that continuations are **not first-class values**, `resume` cannot be assigned to
variables, partially applied, or passed as an argument. However, developers could still indirectly
reify and leak a continuation into a closure cell using side-effects, as shown below:

```stella
-- !!! EXPORT / ESCAPE ENCOUNTERED (MUST BE BANNED) !!!
handle ... with
  var s := 0
  var k := \x -> x
  State
    | full s1 -> 
        k := (\x -> let _ = resume () in x); -- Captures 'resume' inside a closure
        s := s1
    | fast _ ->
        let leaked_k = s! in ...
```

##### The Boundary Restriction Rule

To statically prevent such escapes at the surface language level without modifying the Core
semantics or backend, we enforce the following strict syntactic rule:

> **The `resume` expression can only be used within the immediate lexical body of its introducing `full` clause. It must NOT cross any functional boundaries or evaluation-delay boundaries.**

##### ❌ Rejected Examples (Boundary Violations)

```stella
| full set s1 ->
    let f = \x -> resume x in ... -- Error: Crosses a lambda boundary
```

```stella
| full set s1 ->
    k := (\x -> resume x); ...    -- Error: Crosses a lambda boundary
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
3. Entering a nested handler clause **shadows** the outer clause's `resume` (if the inner clause is `full`, a new local `resume` context is established; if `fast`, `resume` is unavailable).
4. Future extensions involving thunks or lazy expressions will treat them as evaluation-delay boundaries equivalent to function boundaries.

Through this design, the desugared Core language can still treat continuations as regular fresh variables (`k`), while the Surface language cleanly enforces the second-class restriction.
