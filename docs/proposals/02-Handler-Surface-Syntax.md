# Surface Syntax for Effect Handlers and Implicit `resume`

Status: Accepted

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

group-marker  ::= "full" | "fast" | "reifiable" "full"
clause-marker ::= "full" | "fast" | "reifiable" "full"
```

- `full`, `fast`, `reifiable`, and `resume` are reserved keywords.
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

#### 6. Reifiable Continuations

The boundary rule leaves one kind of handler unwritable: a **terminal interpreter**, which hands the
continuation to the host to run later. Interpreting `Console` into `IO` sequences a native action
before the rest of the computation, and the rest is the continuation, stored inside the `IO`
value that `Base.IO.bind` builds:

```stella
handler runConsoleIO :: forall a. (Unit -> a / {| Console |}) -> IO a where
  | return x -> Base.IO.pure x
  reifiable full
    | log s k -> Base.IO.bind (Js.Console.log s) (Continuation.continue k)
```

Here the continuation does leave the clause, and in the present calculus nothing is wrong with
that: it is called by a context that handles what the resumed computation performs, which its type
requires, so **an escaping continuation breaks no soundness**. What the second-class `resume`
promises is a lifetime: a continuation that cannot outlive its clause may be held for the clause's
duration alone. No backend can rely on that yet — `full` and `reifiable full` reach Core as the
same clause, and neither Core nor the `.dmo` keeps the difference (below) — and once a bracket
effect gives a continuation never resumed a finalizer, the same line bears on that lifecycle too.
So the escape is admitted, and written.

##### `reifiable full`

**A `reifiable full` clause takes the continuation as a value.** It is the last parameter of the
clause, after the operation's arguments, and its type is the abstract
`Continuation a b ρ`: resuming with an `a` gives the handler's answer `b`, performing `ρ`. The
clause may capture it in a lambda, pass it as an argument, store it, or return it. `resume` is
not available in such a clause; one name for the continuation is enough.

`reifiable` qualifies a marker, in the same places a marker stands: on a group, as its default,
or on a clause, overriding it. **It qualifies a marker that captures the continuation**, which
today is `full` alone; `reifiable fast` is not a form, a `fast` clause capturing nothing. When
higher-order operations come, a `scoped` clause captures a continuation as well, and
`reifiable scoped` takes the same place.

##### `Continuation`

```stella
module Base.Continuation (Continuation, continue) where

@[elaborationOnly]
newtype Continuation a b (r :: Row Effect) = Continuation (a -> b / {| ...r |})

continue :: forall a b r. Continuation a b r -> a -> b / {| ...r |}
continue (Continuation f) = f
```

**It is abstract outside `Base.Continuation`, and `continue` is its one public eliminator.** A
continuation is resumed by `continue` and by nothing else, as a closure is applied and never split
into its code and its environment. That leaves room for what a continuation may come to carry — whether it is one-shot, a finalizer for
one never resumed, the lifetime of a region or a resource — without any program depending on how
it is represented.

**Its constructor is an elaboration-only entry of `Base.Continuation`.** The module is source the
package implementing the ABI supplies (D26), and it writes the constructor under an ordinary name
with `@[elaborationOnly]`, which the compiler admits there alone; name resolution gives the
constructor the Core identity `Base.Continuation.$Continuation`, which its declaration, its uses
inside the module, the signature, its export, and the `.dmo` all carry, the ordinary name holding in
the module's own source alone. The internal name belongs to no source grammar, so it appears in no source name environment, no import selection,
no re-export, and no completion; a macro, producing source tokens, cannot spell it either, and
`Continuation(..)` does not enumerate it. Its `ExportCtor` is generated apart from the export list,
which writes the type alone. Its type
is part of the signature built from the module, which the Core type checker reads, and a linker
finds it among the constructors a `.dmo` describes
([Modules](../technical-references/06-Modules/01-Modules.md)). **Outside the module,
the desugaring of a `reifiable full` clause alone writes it**, wrapping the Core continuation, `k0`
below, before the clause's body binds `k`:

```text
| reifiable full op x k -> e
  ⟹  full op (x, k0) -> let k = Base.Continuation.$Continuation k0 in e
```

Core gains no form: the constructor is checked as an ordinary newtype's, applied and matched as any
constructor is, and a backend may erase its representation, the newtype flag reaching Mid IR.

**A module with a `reifiable full` clause imports `Base.Continuation`.** The desugaring makes it a
dependency, and a dependency is declared in the header (D22); a clause in a module that does not
import it is an error reported at the clause. The import needs to bring nothing into scope, and
`import lazy Base.Continuation as K` is enough; `continue` is used as any exported name is.

**The restriction is the surface elaboration's trust boundary, and Core does not enforce it.** The
Core type checker checks the reference as an ordinary application of a newtype constructor and
asks nothing of who wrote it, so a hand-written Core module, or a defective elaborator, could build
a `Continuation` from any function. What is guaranteed is that no source program, no macro, and no
synthesizer reaches the constructor: name resolution does not resolve it, and the kernel omits it
from the catalog a synthesizer reads and refuses a global reference to it.

`continue` is not `resume`: `resume` is the keyword reaching the continuation of the clause it
stands in, and `continue` an ordinary function of the value a reifiable clause holds.

What becomes of a continuation that is never resumed is left to the design of a bracket effect,
which is where a finalizer is needed.

##### Three kinds of clause

| Marker | Captures the continuation | May it outlive the clause |
| --- | --- | --- |
| `fast` | no | — |
| `full` | yes, reached by `resume` | no |
| `reifiable full` | yes, as a `Continuation` value | yes |

**The line between the last two is drawn by syntax, and stays there.** The boundary rule above
is the first stage of what `full` admits; analysing escapes may later accept more uses of
`resume` inside a clause — binding it locally, passing it to a function that provably does not
keep it — and accepting more only admits more programs. What is never inferred is that a
continuation outlives its clause: a program that keeps one says so with `reifiable`, so that how
long a continuation lives is read off the text, and no improvement of the analysis changes what a
program means.

An implicit handler has `fast` clauses alone, so it is never reifiable. How the distinction
reaches Core or the `.dmo`, for a backend to rely on, is settled with the optimizer, as above.
