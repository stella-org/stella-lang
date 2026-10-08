# Effects

## Effect rows

An effect row has kind `Row Effect` and shares the row theory of [Rows](02-Rows.md).

```text
Console : Effect
Partial : Effect
State   : Type -> Effect
Exn     : Type -> Effect
```

`IO` is not among them: `IO` is an ordinary monad, not an effect (D20).

**An element's key is derived from the effect at the head of its payload, unless one is written for it** (D16). Writing none is the ordinary case, and nothing is lost by it: the payload already says which effect it is.

```text
()                          pure
( Console )                 key EffectKey Console
( State Int | e )           key EffectKey State, with an unknown remainder
( Console, State Int | e )  two keys and an unknown tail
```

Writing a key is how one effect appears twice.

```text
( cache : State Int, counter : State Int )
  -- keys SymbolKey cache and SymbolKey counter
  -- payloads State Int and State Int, so both offer get and put
```

Effect rows are sharp (D4), so no **key** occurs twice. `( State Int, State String )` is ill-kinded, both elements deriving `EffectKey State`; the labelled form above is well-kinded, and is what distinguishes two instances of one effect.

### The key and the protocol are separate

An element carries two things, and they answer different questions.

| | What it is | What it decides |
| --- | --- | --- |
| the key | `EffectKey E` or `SymbolKey s` | which element of the row this is |
| the payload | `E τ̄` | which operations may be performed, and at what types |

For an unlabelled element the two coincide in appearance, which is why the distinction is easy to miss. A labelled one pulls them apart: `cache : State Int` is identified in the row by `cache` and offers `get` and `put` because its payload is a `State`.

**Nothing but the payload decides the protocol.** A key is a name for a position in a row; it has no operations, no type parameters, and no declaration behind it unless it happens to be an `EffectKey`. This is what lets two instances of `State` behave identically while remaining distinct elements.

## Effects on the arrow

```text
Function : Type -> Row Effect -> Type -> Type
```

`τ1 -{ρ}-> τ2` is a function that takes a `τ1`, may perform effects within `ρ`, and returns a `τ2`.

Making effects a type constructor `Eff ρ τ` would give effectful functions the type `τ1 -> Eff ρ τ2`, distinguishing them from ordinary functions. The FFI boundary, exceptions, and asynchrony would then divide along "is it in the monad or not", and that division would appear throughout every API. On the arrow, a pure function is simply the case `ρ = ()`, and no division arises (D7).

## Declaring effects

```text
effect E (ā : κ̄) where
  op1 : forall (b̄ : κ̄'). σ1 ->* τ1
  ...
```

**An operation signature is not a function type.** To the left of `->*` are the arguments; to the right is the type the continuation resumes with. There is no functional relationship between them (D21).

`->` is unsuitable because in Stella it asserts an empty effect row.

```text
τ1 -> τ2   ≡   Function τ1 () τ2
```

An operation is by definition the one thing that is not pure, so `log : String -> Unit` would, read by Stella's own rules, say the opposite of what is meant. In Haskell or Eff no contradiction arises, because `->` there says nothing about effects; once the effect row sits on the arrow (D7), the notation is no longer available.

### Rules for `->*`

1. Exactly **one** `->*` appears in an operation signature. Neither zero nor two.
2. It has the **same precedence as `->` and is right-associative**.
3. It must lie on the spine. `(a ->* b) -> c` is not admitted.

All three are checked by walking the declared type.

```purescript
effect Console where
  log     :: String ->* Unit
  writeAt :: Int -> String ->* Unit              -- two arguments
  readAll :: Unit ->* String                     -- no arguments

effect Partial where
  abort :: forall b. Unit ->* b
```

`a -> b -> c ->* d -> e` takes three arguments `a`, `b`, `c` and resumes with `d -> e`. That the continuation resumes with a function is **visible in the notation**, which it is not when only `->` is available.

### `->*` marks the arrow that carries the effect

In the generated type of an operation, the arrow at the position of `->*` is the one that carries the effect row.

```purescript
writeAt :: Int -> String ->* Unit                        -- declaration
writeAt :: Int -> String -> Unit / {| Console, ... |}    -- generated type
```

Since `/` attaches to the last arrow, the two correspond directly, and **partial application is pure**.

```purescript
let writeAt0 = writeAt 0      -- pure; nothing happens
writeAt0 "foo"                -- control reaches the handler's clause
```

`->*` is not an ad hoc symbol; it names a structure that D7 and currying already imply.

### Core operations take one argument

A Core operation takes a single argument. An operation written with none takes `Prim.Unit`, one written with one takes it, and one written with several takes a record of them, each under its position — `PositionKey 0`, `PositionKey 1`, and so on; the surface packs the arguments and generates a curried function. Core has no tuple of its own: what source writes as a tuple is such a record.

```text
-- surface: writeAt :: Int -> String ->* Unit
-- Σ:       writeAt : Record ( #0 : Int | ( #1 : String | () ) ) ->* Unit
-- generated function:
writeAt = λ(line : Int). λ(text : String).
            perform Console.writeAt (extend #0 line (extend #1 text {}))
```

`#n` stands for `PositionKey n` here, a key no source writes.

Core requires no change, and destructuring in handler clauses is likewise surface sugar.

## `perform` and `handle`

```text
e ::= ...
    | perform k.op [τ̄] e              invoke an operation of the element keyed k
    | handle e with h                 apply a handler
    | openEff [ρ'] e                  effect widening, erased
    | region [ℓ] ( k1 : σ1, …, kn : σn ) @ ( e1, …, en ) in e
                                      open a region of cells named ℓ, evaluate e in it
    | readCell ℓ.k                    read the cell k of the region named ℓ
    | writeCell ℓ.k e                 write it

h  ::= { handles ent ; return (x : τ) -> e_r ; cl1 ; ... ; cln }

cl ::= full op [b̄] (x : σ, k : τ' -{ρ}-> β) -> e    binds the continuation
     | fast op [b̄] (x : σ)                  -> e    does not

  ρ is the row outside the handle, which is the row a clause stands at
```

- `perform k.op [τ̄] e` invokes operation `op` of the element the ambient row keys with `k`. It requires that row to contain such an element, and the operation is looked up in the effect at the head of that element's **payload**, not in `k`.
- `handle e with h` removes the element `ent` that `h` writes from `e`'s effect row and processes it with the clauses of `h`. The key of `ent` says which element; the effect at the head of its payload says which operations the clauses must exhaust. Handlers are **deep** (D15): after a resumption, control is under the same handler.
- `openEff [ρ'] e` turns `e : τ1 -{ρ}-> τ2` into `τ1 -{ρ ⊎ ρ'}-> τ2`. Effect containment is an explicit term rather than subtyping (D8). At run time it is the identity and disappears during lowering.
- `region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e` opens a region of cells, one per key of the layout, holding the initial values `ē` in the order the layout writes them, and evaluates `e` in it. **A region is a binder of its own and no part of a handler**; a handler carries no cells.
- `readCell ℓ.k` and `writeCell ℓ.k e` reach the cell `k` of the region named `ℓ`. The name says which region is meant, so nothing has to be looked up to decide it.

**A handler writes one element, and a `perform` names one key.** Where the key is an `EffectKey` the two read as they always have — `perform Console.log`, a handler that `handles Console` — and where it is a `SymbolKey` they name the instance instead.

The handler writes the element whole because the row it is removing appears nowhere else in the term: a key does not name an effect, and the arguments of the payload are not recoverable from the clauses ([Typing Rules](05-Typing-Rules.md)). Only the key is consulted at run time.

```text
perform cache.get [] Prim.Unit        -- the element keyed `cache`
handle e with { handles cache : State Int ; … }   -- removes it, leaves `counter`
```

A handler for `cache` and a handler for `counter` have the same clauses, `get` and `put`, because both elements carry a `State` payload. They are nonetheless different handlers removing different elements.

**A handler must cover every operation of the effect its element carries.** Since `handle` removes that element from the row, an operation without a clause would leave its `perform` with nowhere to go. Which operations those are is read from the payload: a handler keyed `cache` over a payload `State Int` owes clauses for `get` and `put`. This is the same requirement as local totality of a decision tree ([Terms and Matching](04-Terms-and-Matching.md)).

Every clause therefore gives its operation a meaning of its own: it resumes the continuation, abandons it, or translates the operation into another effect. **Passing an operation on to an outer handler of the same key is not expressible.** The row `( ent | ρ )` is sharp, so `key(ent) ∉ ρ`, while a clause body is typed at the ambient row `ρ`; a `perform` on that key there would require it to be in `ρ`. Two instances of one effect are a different matter: `cache` and `counter` are different keys, so a handler for one may perform on the other. Forwarding of that kind, and a partial handler that leaves the handled element in the row, each require a construct that v0.1 does not have; the candidates are recorded in [Open Questions](../99-Open-Questions/01-Open-Questions.md).

### `full` and `fast` clauses

A clause takes one of two forms, and what separates them is how much of the handled computation the clause can reach (D28).

A **`full` clause** binds the continuation `k`. Its body has the type of the whole `handle`, so the clause decides what the `handle` returns: it may abandon the computation by never applying `k`, resume it once, or branch it by applying `k` more than once ([Semantics](06-Semantics.md)).

A **`fast` clause** binds the operation's arguments and nothing else. Its body has the type the continuation resumes with, and the value it produces is returned to the point where the operation was performed. Such a clause is **tail-resumptive**: it translates one operation into a computation over the row a clause stands at and, where that computation returns, hands control back there.

```text
effect Console where log : String ->* Unit

full log [] (msg : String, k : Unit -{ρ}-> β) -> …    -- body : β    ! ρ
fast log [] (msg : String)                    -> …    -- body : Unit ! ρ
```

**Core writes the marker on every clause.** There is no default and no unmarked form. A surface language that lets the marker be omitted settles which form it means in its own desugaring, so that the marker is already determined by the time a clause reaches Core.

**The typing rule is what fixes the difference.** A `full` clause's body is checked at the answer type `β`; a `fast` clause's body is checked at the resume type, and `β` appears nowhere in its premise ([Typing Rules](05-Typing-Rules.md)). Naming neither a continuation nor the answer, a `fast` clause cannot bypass the evaluation still to come in order to supply what the `handle` returns, and has no continuation of the handled operation to invoke zero or several times.

**What a `fast` clause guarantees is local to the clause.** Reduction binds its body once and returns the value it produces to the point of the `perform`, from which the original evaluation context continues under the same handler. The clause does select that value, and so influences the result; what it cannot do is skip the rest of the computation and answer in its place.

A body need not return a value. It may diverge, it may fault, or it may perform an operation of the residual row `ρ` whose own handler declines to resume, and then the handled computation does not continue.

**A `fast` clause does not make the program around it one-shot.** Where its body performs an operation of `ρ` and that operation's `full` handler resumes more than once, the continuation that handler built re-enters the evaluation context after the original `perform`, and the rest of the handled computation runs again with it. The duplication comes from that `full` handler, never from this clause. What holds of the clause is only that implementing it calls for no multi-shot continuation, which is what confines D18's question to `full` clauses ([Semantics](06-Semantics.md)).

**A polymorphic resume type does not forbid a `fast` clause.** `Partial`'s `abort : forall (b : Type). Unit ->* b` needs a body of type `b` for the clause's own `b`, and no pure terminating term has that type. Performing an operation that resumes at `b` does.

```text
effect Abort1 where abort1 : forall (b : Type). Unit ->* b
effect Abort2 where abort2 : forall (b : Type). Unit ->* b

fast abort1 [b] (_ : Unit) -> perform Abort2.abort2 [b] Prim.Unit
```

This translates one capability into another, which is what a `fast` clause is for. Interpreting `Partial` into `Maybe` is a different matter and takes a `full` clause — not because `abort` is polymorphic, but because that handler's answer is `Maybe a` where the computation's is `a`, and only a `full` clause supplies an answer ([Examples](08-Examples.md)).

**The property is declared, not inferred.** Whether a `full` clause happens to resume exactly once, in tail position, cannot be read off its syntax. A single occurrence of `k` may sit under a lambda that is applied twice, and two occurrences in separate branches of a `case` may amount to one resumption. Marking the clause is what makes the property available to the type checker, to reduction, and to a backend.

### Regions of cells

A **region** is a finite sequence of mutable cells, each a key with its type, opened by a binder of its own: `region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e` opens one cell per key, holding the initial values `ē`, evaluates `e` in it, and closes when `e` reaches a value (D36). A handler carries no cells. A handler that keeps state across the operations it handles is a `handle` standing in the body of a `region`, and a function applying such a handler opens a region of its own at each application.

```text
counter : forall (e : Row Effect). forall (a : Type).
          Counter ∉ e => ( Unit -{( Counter | e )}-> a ) -{e}-> a
        = Λ (e : Row Effect). Λ (a : Type). Λ (_ : Counter ∉ e).
          λ (thunk : Unit -{( Counter | e )}-> a).
            region [ℓ] ( n : Int ) @ ( 0 ) in
              handle ( ( openEff [( region ℓ )] thunk ) Prim.Unit ) with
                { handles Counter
                ; return (x : a) -> x
                ; fast next (_ : Unit) ->
                    let m : Int = readCell ℓ.n in
                    let _ : Unit = writeCell ℓ.n ( Base.Int.add m 1 ) in
                    m
                }
```

**The layout is written and therefore closed.** It is a sequence of pairs, not a row with a tail, which is what lets the initial values be given one per cell and what makes the region a finite map at run time. The keys are distinct.

**`ℓ` is a region name, bound by `region` and by nothing else.** It is written rather than generated, as every other binder of Core is (D11, D12), and it scopes over the body alone — its type annotations as well as its terms, a `full` clause there writing `region ℓ` in the type of its continuation as readily as its body names a cell. The layout and the initial values lie outside that scope: the layout is kinded without `ℓ`, so no cell holds a value typed by its own region, and the initial values are evaluated before the region opens. A region name is never quantified, so no function abstracts over one ([Kinds and Types](01-Kinds-and-Types.md)).

**A cell is a binder with a lifetime, not a location.** It has no address; `readCell ℓ.k` names it by its region and its key, and no value of the language stands for it that could be held, passed, or stored. A write replaces what the binder holds, so a continuation whose captured segment contains the region carries the values it was captured with, and each of its resumptions proceeds from its own copy; which continuations those are is settled in [Semantics](06-Semantics.md).

**A region is visible wherever `region ℓ` is in the ambient row.** The body stands at `( region ℓ | ρ )`, so a `handle` written in it has its handled computation, its return clause, and its operation clauses all at rows that hold the region, and so does every function whose arrow carries `region ℓ`. **Core decides only where a cell can be reached, not which of those places names one.** The surface opens a handling expression's region outside all of its groups and lets the operation clauses alone name its cells ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)); Core admits a return clause that reads one.

**Regions nest without restriction.** Each region has a key of its own, `RegionKey ℓ`, so a region opened inside another stands beside it in one sharp row, and a reference to a cell says by name which region it means. A row variable bound outside `ℓ` is known to lack `RegionKey ℓ` ([Rows](02-Rows.md)), so `counter` above needs nothing of `e` concerning regions: `openEff [( region ℓ )] thunk` asks for `( Counter | e ) # ( region ℓ )`, that is `RegionKey ℓ ∉ e`, which the binder supplies. `counter` may therefore be applied anywhere, inside another region included.

**What cannot outlive a region is a reference into it.** The rule requires `ℓ` to occur in neither the answer type nor the residual row ([Typing Rules](05-Typing-Rules.md)). A closure built over a `readCell ℓ.k` carries `region ℓ` in its own arrow, so it mentions `ℓ` and can be neither the answer nor anything the residual row admits. Core needs no rank-2 quantifier for this: `region` is a binder, and what a rank-2 `forall` would enforce, a side condition on a binder enforces directly.

**A term carrying the whole `region` is a different matter and is unrestricted.** A closure over it, or a continuation an outer handler captured across it, contains the binder along with everything the binder scopes over; its type mentions no `ℓ`, and it may be stored and applied wherever its type allows. That is not a hole in the discipline but the case the discipline is for: what travels is a region entire, and the cells it carries are the ones it was closed over ([Semantics](06-Semantics.md)).

### This is `ST`, and the state monad is the other handler

**An ordinary return hands back no state, and that is the surface's arrangement.** A surface handling expression lets no return clause name its cells ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)), so what a group's return clause makes of the handled computation's result is all the answer holds. Core is more general here: its return clause stands at a row holding every region open around the `handle`, and may read their cells. **A backend and an optimizer must not assume that a return clause reads no cell.**

Nor is the return path the only one. An operation clause stands in the region and may read a cell and make the value its answer. With a handler whose answer type is `Int`, standing in a region `ℓ` with a cell `n : Int`, and `ρ` the row outside the `handle`, which holds `region ℓ`:

```text
full next (_ : Unit, k : Int -{ρ}-> Int) ->
  let _ : Int = k Prim.Unit in
  readCell ℓ.n
```

The clause resumes, discards what came back, and answers with the cell as it stands afterwards — the state, deliberately copied out. **What a cell-backed handler does not do is return its final state on its own**; a value a cell held is an ordinary value of an ordinary type, and a clause that means to return one may.

That is the reading of a cell, not a gap. Wanting the final state is wanting a state *monad*, which is the parameter-passing handler: `full` clauses, an answer type of `s -{ρ}-> ( α, s )`, and a continuation captured per operation. The two coexist deliberately.

| | Answer type | Clauses | What it buys |
| --- | --- | --- | --- |
| cells | `α` | `fast` | tail resumption; no continuation is built. A `full` clause may still copy a cell into the answer |
| parameter passing | `s -{ρ}-> ( α, s )` | `full` | the final state, in the answer |

The second is written with what Core already has and needs no region. The first is what a region is for, and it composes where the second does not: an answer type of `α` is what the `~>` shorthand of the surface describes ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)).

### `perform` does not require a handler to exist

What `perform k.op` requires is that **the ambient effect row contain an element keyed `k`**, not that a handler be installed. The type system tracks an obligation, not the presence of a handler.

Handlers are installed as a dynamic nesting on the call stack, so whether one exists cannot be asked statically at the `perform` site. What can be asked is which effects a computation may perform, and that is the effect row.

**The absence of a handler anywhere is not in itself a type error.** An unhandled effect is an obligation recorded in a type.

```text
f : Unit -{( E )}-> Unit          -- performs an operation of E internally
```

This is well typed. A library exporting only such functions compiles and ships; installing a handler is the caller's responsibility. If `f` is never called, the obligation is never passed on.

A type error arises exactly where the obligation **cannot propagate further**. There are three such boundaries, all of them existing rules.

| Boundary | Rule |
| --- | --- |
| Function application: the arrow's row must equal the ambient row | [Typing Rules](05-Typing-Rules.md) |
| A top-level declaration's right-hand side, checked at ambient `()` | [Modules](../06-Modules/01-Modules.md) |
| The entry point `main : IO Unit`, which admits no effect row | [Modules](../06-Modules/01-Modules.md) |

Along a call chain reachable from `main`, the effect row propagates upward through types. Since `main` has type `IO Unit`, a `handle` must have removed the effect somewhere along the chain, or one of the boundaries rejects the program. This is a consequence of types propagating, not of reachability analysis.

D8 contributes here: because rows do not widen automatically, an obligation cannot slip through silently, and the diagnostic points at the function that failed to declare the effect.

## Partiality

A non-exhaustive pattern match produces a `Partial` effect (D10).

`Partial` is an ordinary effect declaration of `Prelude`, not a builtin ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

```text
effect Partial where
  abort : forall (b : Type). Unit ->* b
```

`fail τ` is not a separate constructor but **derived notation**.

```text
fail τ   ≡   perform Partial.abort [τ] Prim.Unit
```

A partial function therefore carries `( Partial | e )` in its type. The effect of PureScript's `Partial` class is obtained without a class mechanism and without a dedicated language feature. A handler converting abortion into an exception or a `Maybe` is an ordinary handler.

## Surface syntax

### Set notation

The common spread rules are in [Rows](02-Rows.md); this section covers what is specific to effect rows.

**The brackets are `{|` and `|}`.** What follows covers the **unlabelled form**, where an element is an effect type alone and its key is derived.

```purescript
log :: String -> Unit / {| Console |}
```

```text
{||}                           ⟹  ()
{| Console |}                  ⟹  ( Console )
{| ...e |}                     ⟹  e
{| Console, ...e |}            ⟹  ( Console ) ⊎ e
{| Console, State Int, ...e |} ⟹  ( Console, State Int ) ⊎ e
```

**The surface spelling of a labelled instance is not settled here.** Core has the form — `( cache : State Int )`, keyed `SymbolKey cache` — and what remains is how a signature writes one and how ordinary code says which of `cache` and `counter` it means, given that `perform` never appears in surface syntax (D17). Both belong with the rest of the surface design ([Rows](02-Rows.md)).

**`/` attaches to the last arrow, not to the function type as a whole.**

```purescript
log    :: String -> Unit / {| Console |}
       -- String -{ ( Console ) }-> Unit

logAt  :: Int -> String -> Unit / {| Console |}
       -- Int -{ () }-> ( String -{ ( Console ) }-> Unit )
```

`logAt 0` is pure. Partial application performs nothing, which is the correct reading in a curried language. A function type written without `/` is pure.

### Direct style

Effect sequencing is direct style, and **`perform` does not appear in surface syntax** (D17). Operations are written as ordinary function calls; effects appear in the type but not in the syntax.

```purescript
effect State s where
  get :: Unit ->* s
  put :: s ->* Unit

tick :: Unit -> Int / {| State Int, ... |}
tick _ =
  let n = get ()
  put (Base.Int.add n 1)
  n
```

`get ()` and `put (Base.Int.add n 1)` are ordinary applications; the elaborator turns them into `perform State.get [] Prim.Unit` and `perform State.put [] (…)`. From the author's side, calling an effectful function looks no different from calling a pure one.

Requiring `do` and `bind` for effects would restore at the level of syntax exactly the division that D7 removed from types: whether one passes a pure function or a `do` block to `map` would become a visible distinction, and D7's benefit would be lost.

Because any subexpression may perform an effect, the evaluation order fixed in [Semantics](06-Semantics.md) is **observable from surface syntax**, not merely an internal convention of Core. Strict evaluation together with effect rows on arrows already implies this, independently of the choice of sequencing syntax.

### `handle` does appear in surface syntax

Hiding `perform` while exposing `handle` is not arbitrary. The criterion is **use site versus binder**.

| | Surface | Reason |
| --- | --- | --- |
| `perform` | hidden | A use site. It occurs everywhere in ordinary code and must blend in with ordinary calls (D7) |
| `handle` | **exposed** | A binder. It changes the body's effect row, from `( E τ̄ \| ρ )` to `ρ`, and each clause binds the operation's arguments, a `full` one a continuation `k` besides |

Changing an effect row and introducing names are the work of a binder, like `let`, `λ`, or `case`. Hiding a binder would make it impossible to see where a scope changes.

**Application code nevertheless contains no `handle`.** Thanks to the thunk encoding below, a reusable interpreter is an ordinary function.

```purescript
runConsoleIO (\_ -> body)      -- an ordinary application
```

`handle` appears only inside the definition of an interpreter, of which a library has few.

The details of surface syntax are left to parser design: whether to spell it `handle e with { … }`, whether to place the handler first, and whether sugar such as `with runConsoleIO do …` hides the thunk's `\_ ->`. A syntax macro may provide the spelling. What is fixed here is only that **`handle` exists as a Core construct**.

### Coexistence with classical monads

Direct style does not exclude monads as data structures, such as `Maybe` or a parser. The condition for coexistence is that `bind` be effect-polymorphic, which Core can express.

```text
bind : forall m. … => forall a b. forall (e : Row Effect).
       m a -> ( a -{e}-> m b ) -{e}-> m b
```

Because the continuation `a -{e}-> m b` carries the effect row, a monadic binding and an effectful call may be mixed in the same block. The first arrow is pure, so `bind m1` is a pure partial application, consistent with the currying rule above.

The concrete syntax — whether to use `<-`, and how to spell `do` — is **not decided**. Just as `class` and `instance` need not be primitive keywords, `do` should be a syntax macro supplied by the standard library. The compiler need not know about `do`.

## The end of interpretation

### `IO` is not an effect

Every other effect has a finite declared signature; `IO` admits none.

```text
effect Console where log : String ->* Unit
effect State s  where get : Unit ->* s ; put : s ->* Unit
effect Partial  where abort : forall b. Unit ->* b
effect IO       where ???
```

What `IO` would mean is "anything", which is not an algebraic effect but an escape hatch in the shape of one.

As a symptom, logical containment appears between effects: the operations of `Console` are a subset of what `IO` can do, so `Console ⊂ IO`. Because row keys are constructor names (D16), `( Console, IO )` is two independent keys and cannot express that relationship.

Removing `IO` from the effect world dissolves the question. Effects are mutually independent, which is what sharp rows assume.

### `IO` is an ordinary monad

```text
IO : Type -> Type
```

`IO a` is a **value** denoting a computation that returns an `a` when executed. It is an opaque primitive type: `Prim` supplies the type constructor and `Base.IO` the two operations over it ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

```text
foreign Base.IO.pure : forall a. a -> IO a
foreign Base.IO.bind : forall a b. IO a -> (a -> IO b) -> IO b
```

**`Base.IO.bind`'s continuation is a pure arrow**, unlike the effect-polymorphic `bind` of classical monads above, for two reasons.

First, every arrow in a `foreign` type has an empty effect row (D23), so `( a -{f}-> IO b )` cannot be declared at all.

Second, the semantics would not hold. Deferring `k` until the `IO` is executed would run the residual effect `f` **after leaving the dynamic context of the handler that installed it**, while the result type `IO a` does not carry `f`. The type would fail to describe what execution requires.

### Interpreters that sequence native actions take a closed row

The consequence does not extend to every handler that returns `IO`. A closed row is required only when a **native `IO` action is sequenced before the continuation using `Base.IO.bind`**.

With ambient row `e` and `k : τ -{e}-> IO a`:

```text
k v                     : IO a ! e      resume synchronously, return that IO
Base.IO.pure x               : IO a ! e      abandon the continuation
Base.IO.bind act (\_ -> k v) : ill typed     ← Base.IO.bind's second argument must be pure
```

Only the third fails, because `\_ -> k v` has effect `e`. The requirement is therefore a **library discipline** for terminal interpreters, not a typing restriction on `IO`-returning handlers in general.

```text
Std.runConsoleIO
  : forall (a : Type). ( Unit -{ ( Console ) }-> a ) -> IO a
```

With no `⊎ e`, the clause's `k : Unit -{()}-> IO a` is a pure arrow and composes with the pure `Base.IO.bind`.

Expressiveness is unaffected. Handlers nest, and only the one stage that sequences native actions needs a closed row; in the standard library that stage is the outermost interpreter.

```purescript
-- inner handlers stay effect-polymorphic
runState :: forall a s. (Unit -> a / {| State s, ... |}) -> s -> Tuple a s / {| ... |}

-- only the terminal one is closed
runConsoleIO :: forall a. (Unit -> a / {| Console |}) -> IO a

main = runConsoleIO (\_ -> runState (\_ -> body) 0)
```

A `Monad` instance is placed on `Base.IO.bind` by the standard library. To Core, `IO` is an ordinary type constructor with no special status.

### Uninterpreted effects are not executed

> The runtime can do two things: **compute a pure value**, and **execute an `IO`**. Every effect must be interpreted into `()` or into `IO`; an effect interpreted into neither is never executed.

The type of the entry point enforces this.

```purescript
main :: IO Unit
```

A computation with unhandled effects does not have type `IO Unit` and so cannot reach `main`. The question of what becomes of an uninterpreted effect closes by **never arising**.

What closes here is that such effects are *not executed*, not that code carrying them cannot be written. A function with effects is well typed on its own and can be shipped as a library; installing a handler is the caller's responsibility.

### The type of a handler

An interpreter takes a computation carrying effects and returns an `IO`. Written naively, the effect row appears to fall to the left of an arrow.

```text
forall a. a / {| Console |} -> IO a        -- not expressible
```

Under call-by-value, however, `Unit -{ρ}-> a` **is** a computation of type `a` with effects `ρ`, so thunking suffices; the effect row sits **on** the left-hand arrow rather than to its left.

```purescript
runConsoleIO :: forall a. (Unit -> a / {| Console |}) -> IO a
```

**A `Handler` need not be a separate inhabitant from `->`.** The function type stays `Function` alone.

The target of interpretation need not be `IO`: a handler may interpret `Partial` into `Maybe`, which is the pure side. All that is required is that by the time control reaches `main`, the row is `()` or the result is `IO`.

### `IO` is executed in exactly one place

Operations are **declared without implementations**. Writing `effect Console where log :: String ->* Unit` makes `log : String -> Unit / {| Console |}` available, elaborated to `perform Console.log`. There is nothing to define.

An `IO` value may flow through ordinary code — an operation may take one, and a caller may hand one over — but **executing one happens only in the runtime ABI**, applied to `main` (D25). Interpreters are where such a value is ordinarily built and sequenced; nothing about the type confines it to them.

```purescript
-- Base.Effect.Console declares the capability
effect Console where
  log :: String ->* Unit

-- Js.Console supplies the native leaf for one target
foreign log :: String -> IO Unit

runConsoleIO :: forall a. (Unit -> a / {| Console |}) -> IO a
runConsoleIO thunk =
  handle (thunk ()) with
    { handles Console
    ; return x        -> Base.IO.pure x
    ; log (s, k)      -> Base.IO.bind (Js.Console.log s) (\_ -> k ())
    }
```

The clause's result type is already `IO a`, so `Base.IO.bind` composes there naturally. **No lift of the form `IO a -> a / {| Console |}` is needed.**

### Where the trust boundary lies

The type of `Js.Console.log`, `String -> IO Unit`, says only that some IO occurs. That it performs only console IO is not guaranteed by the type; an implementation that deleted files would still type check.

This is a trust boundary that **should be accepted**. That is what FFI is, and [Modules](../06-Modules/01-Modules.md) already declares it.

What matters is its **location**: at the `foreign` declaration, and nowhere else. An interpreter such as `runConsoleIO` is ordinary safe Stella code and is not a trust boundary. The boundaries do not multiply.

### A lift is sound, and coarse

A lift may be provided, and it is not a hole in the type system.

```purescript
effect LiftIO where
  liftIO :: forall a. IO a ->* a
```

**`perform` does not execute the `IO` value.** It performs the operation — control moves to the matching handler — and the argument travels there as an opaque value. What reaches the outside world does so when the runtime ABI executes `main` (D25), exactly as with any other interpreter.

```purescript
program :: Unit / {| LiftIO |}
program = liftIO (Js.Console.log "Hello")    -- builds an IO value; writes nothing

main :: IO Unit
main =
  handle program with
    { handles LiftIO
    ; return x        -> Base.IO.pure x
    ; liftIO (act, k) -> Base.IO.bind act k
    }
```

That clause keeps `k` and runs it after `act`, and it typechecks for the same reason `runConsoleIO`'s does.

```text
act : IO a
k   : a -> IO r          ← pure, because the residual row is closed
Base.IO.bind act k : IO r
```

**A continuation-preserving interpreter that sequences `act` before `k` requires a closed residual row.** Were the row not closed, `k` would be `a -{ρ}-> IO r`, and `Base.IO.bind` takes a pure arrow, so a native action cannot be deferred behind effects that are still to be interpreted. A clause that abandons `k`, or that resumes it before sequencing anything, is under no such condition. That discipline is what excludes the unsound case, not a restriction on the signature.

D20 keeps `IO` out of the effect world. It does not exclude an effect whose *operation* takes an `IO`: `LiftIO` is an ordinary key in the row, removed by an ordinary handler, and no rule of the type system makes `Console` a part of it.

Nor could a restriction be made to hold. `IO` is opaque, and a newtype hides it.

```purescript
newtype Action a = Action (IO a)

effect Lift where
  lift :: forall a. Action a ->* a
```

A rule rejecting the occurrence of `Prim.IO` in an operation signature would reject the first and admit the second, which makes it a lint rather than a condition on soundness. The Core type checker imposes none ([Modules](../06-Modules/01-Modules.md)).

What a lift costs is **the granularity of what a type says**. Code carrying `LiftIO` asks for "some runtime action" rather than for a capability, so the row no longer tells `Console` from `FileSystem`. That is a real loss and it is the argument for keeping a lift out of ordinary code — a matter of what a library offers rather than of what the checker admits. What is not lost: the row still names `LiftIO`, and passing between the two is an explicit handler.

**Declare a lift with operation polymorphism, never with an effect parameter.**

```purescript
effect LiftIO where liftIO :: forall a. IO a ->* a      -- one key, every a
effect LiftIO (a : Type) where liftIO :: IO a ->* a     -- one a per instance, all sharing one key
```

Rows are sharp, and two unlabelled instances of the second form share the key `EffectKey LiftIO`, so a computation lifting an `IO String` and an `IO Unit` has no well-kinded row. Writing keys for them recovers one — `( stringLift : LiftIO String, unitLift : LiftIO Unit )` is well-kinded ([Rows](02-Rows.md)) — at the price of a key and a handler for every type lifted. Operation polymorphism needs neither.

A standard library providing one puts it in a module named for what it is — `Unsafe` or `Runtime` — so that importing it records the choice.

A pure elimination is a different matter. `foreign unsafePerformIO : forall a. IO a -> a` satisfies D23 and the checker admits the declaration, but **no conforming `δ_f` implements it**: the implementation would have to execute the action, and D25 places execution outside Core ([Semantics](06-Semantics.md)). It is unimplementable rather than ill-typed, which is why Stella does not provide one.

### Confining `IO` is a discipline

Making `IO` a monad gives functions that perform real IO the type `a -> IO b`, which is exactly the monadic division D7 avoids.

Ordinary fine-grained code therefore keeps `IO` inside interpreters and `main`, which requires every real-world capability to be a named effect.

```purescript
effect Console    where log :: String ->* Unit
effect FileSystem where readFile :: Path ->* String ; writeFile :: Path -> String ->* Unit
effect Clock      where now :: Unit ->* Instant
effect Random     where nextInt :: Unit ->* Int
```

Code written this way says "uses `Console` and `FileSystem`", not "does IO", and `IO` is written by interpreters and by `main`.

D7's granularity is lost the moment ordinary code starts writing `-> IO a`. This is a matter of **policy** rather than of types, and the shape of the standard library must support it. Importing an `Unsafe` or `Runtime` lift opts out of the granularity explicitly, and soundness is untouched either way; what a lift costs is what the row tells a reader. So long as the discipline holds, the effect system is used as it is meant to be.
