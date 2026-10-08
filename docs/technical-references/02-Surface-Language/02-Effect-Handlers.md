# Effect Handlers

Core fixes `handle`, the two clause forms, and the region binder of cells, and leaves the spelling to the surface ([Effects](../03-Typed-Core/03-Effects.md)). This document settles that spelling, and settles when the elaborator supplies a handler the author did not write.

Nothing here reaches Core. A handler declaration desugars to an ordinary function, and an inserted handler is an ordinary application; what elaboration produces is application, `openEff`, `handle`, and the region and cell terms of D36, each of which the Core type checker validates as it validates any other term (D29).

## Handler declarations

A **handler declaration** binds a name to an interpreter.

```stella
handler runConsole :: Console ~> ( LiftIO ) where
  fast | log msg -> liftIO (Js.Console.log msg)
```

It desugars to a value declaration whose right-hand side is a `handle` under a thunk, and where it declares cells, the region around that `handle` ([Cells](#cells)).

```text
Js.Effect.Console.runConsole
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

`handler` is a declaration form and not a new kind of entity. The name it binds is an ordinary global, exported by an ordinary export list, applied at an ordinary call site.

### `~>` is a shorthand for one shape

`E ~> ρ` reads "handles `E`, performs `ρ`", and abbreviates the shape every capability translation takes: effect-polymorphic in a residual row, and leaving the answer type alone.

```text
handler h :: E ~> ( t1, …, tn ) where …

  ⟹  h : forall (e : Row Effect). forall (a : Type).
           E ∉ e => t1 ∉ e => … => tn ∉ e =>
           ( Unit -{ ( E, t1, …, tn | e ) }-> a ) -{ ( t1, …, tn | e ) }-> a
```

The left of `~>` is **one element**, because a `handle` names one key. The right is a **row fragment**, which may hold several elements or none; the empty target is written `()`.

**The shape is quantified as a signature is.** A type variable it mentions that nothing binds is quantified implicitly, and a `forall` may stand in front of it, to give a variable its kind: `forall (s :: Type). State s ~> ()`. Its variables are in scope in the handler's parameters and body ([Name Resolution](06-Name-Resolution.md)).

```stella
-- effect Verbosity where level :: Unit ->* Int
handler quiet :: Verbosity ~> () where
  fast | level _ -> 0
```

**The source element appears in the source row together with the target.** A handler declared `Console ~> ( LiftIO )` accepts a computation already performing `LiftIO` and returns one still performing it, which is the shape a hand-written adapter takes as well ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

The narrower shape, taking `( Console | e )`, is a different function and it does not compose: it cannot stand where its target is already in the row, `LiftIO ∉ e` failing there. That is not a corner. It is the position every handler after the first stands in once two of them lower into one target, and the position the insertion below puts them in, since a computation is brought to a row carrying every target before any handler is applied.

### The general form

A handler whose answer type differs from the computation's, or whose residual row must be closed, writes its signature in full instead of using `~>`.

```stella
handler runConsoleIO :: forall a. (Unit -> a / {| Console |}) -> IO a where
  | return x -> Base.IO.pure x
  reifiable full
    | log s k -> Base.IO.bind (Js.Console.log s) (Continuation.continue k)
```

Both properties belong to terminal interpreters, and both follow from what the clauses do rather than from a rule of this form. Sequencing a native action before the continuation requires a closed row, `Base.IO.bind` taking a pure arrow ([Effects](../03-Typed-Core/03-Effects.md)); supplying `IO a` where the computation gives `a` requires a `return` clause, and only a clause capturing the continuation can carry the answer onward. That this one hands the continuation to the host is why it is `reifiable` (below).

A handler interpreting an effect into a pure type is the same case.

```stella
handler toMaybe :: forall a. (Unit -> a / {| Partial, ... |}) -> Maybe a / {| ... |} where
  | return x -> Just x
  | full abort _ -> Nothing
```

**The effect handled is read off the signature.** Past its quantifiers, constraints, and synthesized arguments, the signature is a function from a thunk `Unit -> α / ρ` to a result, `β / ρ'` or a pure `β`, and the effect is the one element `ρ` holds and `ρ'` does not, elements being told apart by their keys: the effect, or the label of an instance.

- **A row is written `{| … |}`, or named by a type synonym without parameters**, which is read through. A spread contributes the elements of the row it names: a synonym's, and none for a variable or `...` left open.
- **Exactly one unlabelled element is removed.** A signature removing none, several, or a labelled instance is rejected, as is one whose rows are read neither way: a handler declaration handles one effect, and a labelled instance is handled in place by a group headed by its label.

```stella
type ProgramEffects = {| FS, Log, DB, LiftIO |}
type RuntimeEffects = {| FS, Log, LiftIO |}

handler runDatabase :: forall a. (Unit -> a / ProgramEffects) -> a / RuntimeEffects where …
```

`runDatabase` handles `DB`, the one element `ProgramEffects` holds and `RuntimeEffects` does not.

### Clause forms

A clause is a `|`, a marker, the operation, a pattern for each of its arguments, and a body after `->`. The marker of a group is the default of its clauses, and a clause's own overrides it ([Syntax](05-Syntax.md)).

```text
clause ::= "|" marker? op binder* "->" expr
         | "|" "return" binder "->" expr
marker ::= "full" | "fast" | "reifiable" "full"
```

**Three markers, by what becomes of the continuation** ([Handler Surface Syntax](../../proposals/02-Handler-Surface-Syntax.md)):

| Marker | The continuation | The body |
| --- | --- | --- |
| `fast` | not captured | has the type the operation resumes with (D28) |
| `full` | captured, reached by `resume` in the clause's immediate body | is the answer |
| `reifiable full` | captured, a `Continuation` value taken as the clause's last parameter | is the answer |

```stella
| fast log msg -> liftIO (Js.Console.log msg)
| full choose _ -> let x = resume true in let y = resume false in x ++ y
| reifiable full log s k -> Base.IO.bind (Js.Console.log s) (Continuation.continue k)
```

**`resume` does not leave the clause it belongs to.** It stands in the clause's immediate body, and not inside a lambda, a local function, or a handling expression, any of which could keep it: the body of a handling expression is a thunk, and every item after the first stands inside the thunk the item before it is applied to. A `full` clause of a group written inside it brings a `resume` of its own, and a `fast` or `reifiable full` one none. **`resume` stands applied**, `resume e`: it is no value, so one bound to a name, passed as an argument, or returned is rejected. Name resolution checks both, from the syntax alone ([Handler Surface Syntax](../../proposals/02-Handler-Surface-Syntax.md)). A clause that keeps its continuation beyond itself — handing it to the host, storing it, returning it — is `reifiable full`, and its continuation is an abstract `Continuation`, resumed by `Continuation.continue`. Both reach Core as the same `full` clause, the continuation an ordinary variable there, wrapped for a `reifiable full` clause by a constructor only that desugaring writes ([Elaboration](01-Elaboration.md)); a module holding such a clause imports `Base.Continuation`, which the examples here import as `Continuation`. The difference between the two is a lifetime the surface promises, which no backend relies on until the distinction is carried into Core or the `.dmo`.

**An unmarked clause is `full`.** Core writes the marker on every clause, so the desugaring settles which form an unmarked one means, and it means the unrestricted one. Nothing in Core falls back on a default.

**A clause names an operation of the effect its handler handles, looked up among that effect's operations**, so a handler of `E` needs `E` in scope and not its operations, and a local value of an operation's name does not hide it. A qualified name is looked up in scope and must name an operation of that effect. A group headed by a label names no effect: its clauses name operations in scope, local values aside, and the effect they all belong to is the one it handles ([Name Resolution](06-Name-Resolution.md)).

**A clause binds one pattern per argument of its operation**, followed for a `reifiable full` clause by its continuation, and the patterns are irrefutable, a clause having no other to fall through to. A handler has one clause per operation and one return clause at most. One for every operation of the effect is what a handler accepted in the end has: name resolution rejects a second clause for an operation, and the Core type checker a handler missing one.

An operation declared with several arguments binds them one by one, the record Core packs them into being surface sugar ([Effects](../03-Typed-Core/03-Effects.md)).

```stella
-- writeAt :: Int -> String ->* Unit
| fast writeAt line text -> liftIO (Js.Console.writeAt line text)
```

The `return` clause is optional. A handler without one returns the computation's own value, which is the identity `return (x : α) -> x` in Core.

### Parameters

A handler declaration may take ordinary value parameters, written before the `::`.

```stella
handler runWithLimit (limit :: Int) :: Fuel ~> () where …
```

They become arguments of the generated function, ahead of the thunk, and require nothing of Core.

## Cells

A handling expression may own **cells**. A cell is a mutable binding local to the prompt the expression installs: its lifetime is the expression's region, and the operation clauses of every group of the expression reach it; nothing else does. This is what `ST` gives and a state monad does not — a `fast` clause reads and writes one without building a continuation, so handling an operation captures nothing (D36).

```stella
-- effect Counter where next :: Unit ->* Int
-- effect Emit where emit :: String ->* Unit
handle program with
  var n := 0
  Counter
    fast | next _ -> n!
  Emit
    fast | emit _ -> n := n! + 1
```

`var x := e` declares a cell together with its initial value, `x!` reads it, and `x := e` writes it. A write evaluates to `Prim.Unit`. Both groups above reach the one `n`: what an `emit` writes is what the next `next` reads.

### Declarations come before the items

Every `var` of a handling expression is an item of it and stands ahead of its first group or handler. One after a group or a handler is rejected. The cells are the expression's and not any one group's, and fixing their place is what makes that readable at a glance: they are declared before anything is installed, and every group below them reaches them.

Each declaration becomes one cell of one region, keyed by the name written. **Two declarations of one name are rejected**, a region's keys being distinct. A handling expression declaring no cell opens no region.

### Cells of a handler declaration

A handler declaration writes its cells in its block, ahead of its clauses. One after a clause is rejected.

```stella
-- effect Counter where next :: Unit ->* Int
handler counter :: Counter ~> () where
  var n := 0
  fast | next _ -> let v = n! in let _ = n := v + 1 in v
```

**The cells belong to the prompt an application of the handler installs, not to the effect it handles.** A handler declaration is a handling expression holding one group, whose effect is the one its signature handles, and its cells are that expression's. Each application opens a region of its own: a handler is an ordinary function value and carries no state between applications, so two computations run under `counter` count separately, a recursive application included.

**Applying a declared handler inside another handling expression joins no layouts.**

```stella
-- effect Emit where emit :: String ->* Unit
handle program with
  var c := 0
  counter
  Emit
    fast | emit _ -> c := c! + 1
```

`counter`'s clause reaches `counter`'s own `n` and nothing else, and the `Emit` group reaches the expression's `c`. `counter` cannot take up the `c` of the expression it is applied in, and the `Emit` group cannot reach `n`. Effects that are to share one cell are written as groups of one handling expression, as in the first example above.

### What an initial value may do

An initial value is evaluated **each time its expression is evaluated** — a handler declaration's at each application — in declaration order, before any item of the expression is installed. It stands outside the region, at the row the expression stands at, so it may perform the effects of that row — reading a clock or a configuration to seed a cell — and an operation it performs is handled outside the expression. It reaches no cell of its own expression, none being open yet; written in an operation clause of another expression, it reaches the outer expression's cells, except those its own expression's cells hide. An **implicit** handler is narrower: its initial values must be value forms, an inserted application standing where the author wrote nothing.

### Reading and writing

**A bare `x` never denotes the cell.** The only ways to mention a cell are `x!` and `x := e`, so no value stands for one and none can be stored in one, returned, or passed to a function. A function written in a clause may read and write a cell, and is called there; one handed out of the region — returned as the answer, or as part of it — carries the region in its type and is rejected by the escape condition of D36. Between the two, nothing an author can write reaches a cell from outside the expression declaring it.

Because the two spellings mention no ordinary variable, a cell name occupies no ordinary scope. A `var x` and a local `x` may stand together, the first reached by `x!` and `x :=` and the second by `x`, and neither shadows the other.

### Where a cell is reached

Cells are visible **in the operation clauses of the expression's groups**, every group alike, and in the functions written there — not in the expression's `return` clauses, not in its initial values, not in the computation it handles, and not in the handlers it applies as items, a handler applied being a function value written elsewhere or inline. A handler declaration's cells are visible in its operation clauses likewise, and not in its `return` clause or its initial values. That a `return` clause cannot read one is what keeps cells from being a state monad in disguise: an ordinary return hands back the computation's value and no state of its own. A handler that wants its final state returned writes the parameter-passing interpreter instead and pays for the continuation.

**A handling expression written inside an operation clause sees the cells of the expression owning that clause, besides its own.** Its clauses reach both; its initial values, `return` clauses, handled computation, and applied handlers reach the outer ones alone, its own not being open there. **Its own cells hide outer ones of the same name throughout the expression**: where its own are closed, such a name reaches neither cell, so `x!` names one cell wherever it stands in the expression.

```stella
handle program with
  var n := 0
  var m := 0
  E
    fast | get _ ->
      handle work with
        var n := m!                 -- the outer m
        Own
          fast | tick _ -> n! + m!  -- the inner n, and the outer m
```

**Nesting is unrestricted.** A handling expression with cells, and an application of a handler declaration with cells, may stand wherever an expression may, a clause of another included: each opens a region of its own, and every reference resolves, where it is written, to the cell of one expression.

### What reaches Core

**The cells become one `region` around the expression's items** ([Effects](../03-Typed-Core/03-Effects.md)): the declarations its layout and its initial values, in the order written.

```text
handle e with var c̄ := ē ; i1 ; … ; in

  ⟹  region [ℓ] ( c̄ : σ̄ ) @ ( ē ) in  i1 (\_ -> … in (\_ -> e))
```

- **`ℓ` is a fresh region name**, the elaborator's and not the author's. A region name is bound by `region` alone and is never quantified, so nothing outside the expression names it.
- **`x!` and `x := e` become `readCell ℓ.x` and `writeCell ℓ.x e`**, `ℓ` being the region of the expression the reference resolves to. A reference names its region and not only a key, so a region inside it declaring the same key does not capture it.
- **A thunk handed to an item stands at a row holding `region ℓ`**, so the groups inside it reach the region, and a handler applied as an item instantiates its residual row with that row.
- **A handling expression with no `var` opens no region.**

A handler declaration desugars to a function whose body is the region around its `handle`.

```text
Main.counter
  : forall (e : Row Effect). forall (a : Type).
    Counter ∉ e =>
    ( Unit -{ ( Counter | e ) }-> a ) -{ e }-> a
  = Λ (e : Row Effect). Λ (a : Type).
      Λ (_ : Counter ∉ e).
        λ (thunk : Unit -{ ( Counter | e ) }-> a).
          region [ℓ] ( n : Int ) @ ( 0 ) in
            handle ( ( openEff [( region ℓ )] thunk ) Prim.Unit ) with
              { handles Counter
              ; return (x : a) -> x
              ; fast next (_ : Unit) ->
                  let v : Int = readCell ℓ.n in
                  let _ : Unit = writeCell ℓ.n
                    ( ( openEff [ρ'] ( ( openEff [ρ'] Base.Int.add ) v ) ) 1 ) in
                  v
              }

  where ρ' = ( region ℓ | e )
```

**The scheme says nothing of regions.** `e` is bound outside `ℓ`, so `RegionKey ℓ ∉ e` holds inside the region, and that is what lets the thunk be widened by `region ℓ`. A handler with cells therefore takes an open residual row with no constraint beyond its effect's own, and may be applied wherever one without cells may.

**A clause body reaching outside the region widens through it, once for each argument it passes.** The clauses stand at `ρ' = ( region ℓ | e )` where a handler without cells leaves them at `e`. `Base.Int.add` is pure and curried, so each stage that consumes an argument is an arrow at the empty row standing where `ρ'` is ambient, and each is widened. Containment is written and never implied (D8); a clause body is where the elaborator must supply it, the author having written none.

### Cells and implicit handlers

A handler with cells may be `implicit`, and one condition is where cells bear on it: **every initial value must elaborate to a value form.** Nothing else about cells enters the eligibility of a declaration, and an inserted application of one opens a region of its own wherever it lands.

**The condition is on the Core the initializer elaborates to, not on how it is written.** A surface expression that looks like a value need not become one: a macro expands to whatever it expands to, and sugar may produce an application. What is required is that the elaborated term satisfy the value-form predicate the value restriction already uses ([Terms and Matching](../03-Typed-Core/04-Terms-and-Matching.md)). That is still a property of the declaration, so it is settled where the declaration is elaborated and reported against the `var` whose initial value failed.

That condition is the `fast` condition applied to the one part of a handler an operation does not guard. `var n := 0` and `var seen := false` are value forms and cost nothing; a handler that wants a cell seeded by a performance is written explicitly, where the author has put the application somewhere and can see what runs there.

### What is not provided

**No function written outside a handling expression reaches its cells.** `region ℓ` has no surface spelling, and a region name is bound by `region` alone and never quantified, so a top-level helper cannot declare the row that would let it read one. A local function in a clause body reaches cells where its type is inferred; one that must be written down does not. How a helper could be written against an expression's cells is left open ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

## Applying a handler

A handler is applied like any other function, to a thunk.

```stella
runConsole (\_ -> program)
```

**A handling expression writes the same application without the thunk.** `handle e with …` and `using … handle e` take a list of handlers and groups written in place, installed from the top down, the first outermost; the list desugars to `item₁ (\_ -> item₂ (\_ -> … (\_ -> e)))`, a group being a handler built where it stands ([Syntax](05-Syntax.md)). Cells the list declares ahead of its items open a region around the whole of it ([Cells](#cells)).

```stella
handle program with
  runConsole
  State full
    | get _ -> resume 0
    | set _ -> resume ()
```

Neither form is a construct of its own: what reaches Core is the application, and the `handle` of Core appears only inside the handlers applied.

**The thunk is what defers the computation.** An argument reaches a value before the function it is applied to, and before anything the callee does (D35), so a handler taking the computation itself would receive one that had already run — outside the `handle` meant to enclose it, with its operations reaching whatever handler was installed there instead. The `λ` is what puts that evaluation inside. This is why every application the desugaring and the insertion below produce has a value in argument position: a thunk, a variable, or `Prim.Unit`, never a computation.

## Implicit handlers

The `implicit` modifier marks a handler the elaborator may supply where the author did not write one.

```stella
implicit
handler runConsole :: Console ~> ( LiftIO ) where
  fast | log msg -> liftIO (Js.Console.log msg)
```

An implicit handler is subject to five conditions, each checked where it is declared.

| Condition | Reason |
| --- | --- |
| Written with `~>` | The row transformation must be readable from the declaration, since the search runs over rows |
| Every clause is `fast` | An inserted handler translates one capability into another. A `full` clause could abandon or duplicate the computation at a site the author did not write, and control flow should not appear where nothing is written |
| Every cell's initial value elaborates to a value form | An initial value is not guarded by an operation: it runs whenever the handler is applied, at the residual row, whether or not the computation ever performs the effect handled. One free to perform could abandon the computation from a site the author did not write, which is what the condition above exists to prevent |
| No `return` clause | The answer type must be unchanged; see below |
| No value parameters | The elaborator has no argument to supply |

The last two are the ones a reader is most likely to want relaxed, and they are not alike. **The parameter restriction is liftable**: a parameter could be a synthesis goal, resolved by the same hook type classes use ([Elaboration](01-Elaboration.md)), and that mechanism exists already. Whether it is wanted is a separate question, since a parameter chosen at the call site — an initial state, a fuel bound — is one the caller means to write, and an implicit handler is exactly the case where nothing is written.

**The `return` restriction is not liftable in this form.** Were an implicit handler allowed to change the answer, insertion would be driven by a mismatch of types rather than by a difference of rows, and the search would no longer be finite or directed: the elaborator would look for a composition of answer-type transformations reconciling two types, which is implicit coercion rather than capability translation. That the keys to remove are determined by the row difference is what makes the search below terminate.

## Insertion

### Where it fires

**Inference never inserts.** An expression is first given its own least effect row, so principal rows and the diagnostics D8 provides are preserved. Insertion is attempted only at a checking position, where an expected row is supplied by an annotation or by an enclosing signature.

### The judgement

```text
Ξ ; Γ ⊢ e : α ! ρ1  ⇝  e' : α ! ρ2
```

`Ξ` is the environment of implicit handlers the module declares itself and the modules its header imports directly declare, and not those of a module reached only through another ([Modules](../06-Modules/01-Modules.md)). `Γ`, `Δ`, `Ω`, and `Ψ` are taken by the contexts of Core and of Core⁺, so the environment takes a letter of its own.

**`Ξ` is checked where it is assembled**, which is where the module's imports are resolved rather than where any one declaration is. Acyclicity is a property of the environment and not of a declaration: two modules declaring `A ~> ( B )` and `B ~> ( A )` are each coherent on their own, and the cycle exists only for a module importing both. Checking it at assembly is early enough that no use site sees it, and late enough to see it at all.

The judgement holds when a **plan** exists, and the elaborator inserts a plan only when it is unique.

### The plan

Let `nf(ρ1) = ⟨ F1 ; T1 ⟩` and `nf(ρ2) = ⟨ F2 ; T2 ⟩`.

```text
1. the handlers, by worklist
     worklist ← dom(F1) ∖ dom(F2)      processed ← ∅      plan ← ∅
     while the worklist is not empty:
       take a key k from it      processed ← processed ∪ { k }
       among the implicit handlers of Ξ whose source key is k:
         none      → failure, naming k
         several   → ambiguity, naming them and the modules they come from
         one, H    → plan ← plan ∪ { H }
                      worklist ← worklist ∪
                        ( keys(target(H)) ∖ dom(F2) ∖ processed )

2. ordering
     H is required inside H' when source(H') ∈ keys(target(H))
     ≺ is the transitive closure of that relation on plan

3. uniqueness
     the plan is unique exactly when ≺ is a total order on plan —
     equivalently, when plan has exactly one topological order
     otherwise → ambiguity, naming the handlers ≺ leaves unordered

4. the row the computation must reach
     W = the compatible union of F2 and every target(H), H ∈ plan —
       a key contributed more than once carries one payload, or failure
     F1 and W agree likewise on dom(F1) ∩ dom(W), or failure
     widen e once by the elements of W whose keys are not in dom(F1)

5. the result
     apply the handlers outward in the order ≺ gives
     the row so obtained must equal ρ2 by ordinary row equality
```

Step 4 adds only what is missing. **A computation already performing a target is left alone**, since widening it again by that element is not well-kinded, sharpness admitting no key twice; and a key that only `ρ2` carries is added, since no handler would otherwise put it there.

**`W` is a union of finite maps and is therefore partial.** `F2` and the targets may each contribute the same key — two handlers ordered one inside the other may both name `cache`, and `F2` may name it too — and a key so contributed must carry one payload throughout. Where it does not, no row is being described and the failure belongs there rather than at the final equality. The same holds between `F1` and `W`: a widening adds elements and reconciles no payload.

Step 1 is a worklist rather than a set comprehension because the target of the handler for `k` can be consulted only once that handler is known to be the one there is, which is a property of `k` and not of the set. **It terminates** because `Ξ` is finite and each target is a finite fragment, so finitely many keys can ever enter the worklist, and `processed` keeps any of them from entering twice. The set of row keys is not itself finite, and the argument does not need it to be.

Step 2 takes the transitive closure rather than the direct edges alone. A chain of three is ordered by `A ≺ B` and `B ≺ C` alone, whose union is not a total order until `A ≺ C` is added.

Requiring a total order is where the design declines to be clever. Two handlers the relation does not order are two nestings of the same term, and whether they mean the same thing is not something the elaborator can settle: a `fast` clause performs an operation of the residual row, and what becomes of the computation then belongs to whichever handler is installed for that row (D28). Rather than classify handlers by whether they resume, which no declaration records, insertion requires that the term be determined.

**The consequence is worth stating plainly.** A single key is always totally ordered, so the common case goes through. A chain does too, its transitive closure being total.

```text
{ Console, ...e }  ⟹  { Logging, ...e }  ⟹  { LiftIO, ...e }
```

Two capabilities lowering independently into one target do not.

```stella
implicit handler lowerConsole :: Console ~> ( LiftIO ) where …
implicit handler lowerFile    :: File    ~> ( LiftIO ) where …

program :: a / {| Console, File |}

-- checked against a / {| LiftIO |}: the relation orders neither handler
-- against the other, so this is an ambiguity rather than an insertion
```

Such a site writes the composition itself, which is an ordinary nesting of two applications and says which order it means. Lifting the restriction is [an open question](../99-Open-Questions/01-Open-Questions.md).

### `IO` is not a node

Every node of the graph is an effect, so the terminal step — interpreting the last capability into `IO` — lies outside it by construction (D20). That step changes the answer type and takes a closed residual row, which the conditions above exclude twice over. A program therefore always writes its terminal interpreter, and only the translations between capabilities are supplied.

### Keys, not constructors

A row element is keyed, and `handles Console` fixes the key `EffectKey Console` (D16). Core has no key polymorphism, so a handler for one key is not a handler for another, and an implicit handler is registered in `Ξ` under **its key** rather than under its effect constructor.

**Implicit insertion therefore reaches unlabelled instances only.** A labelled instance `( logger : Console )` is keyed `SymbolKey logger`, and lowering it needs a handler declared for that key. A labelled instance is written `{| logger :: Console |}` and handled in place by a group headed by its label ([Syntax](05-Syntax.md)). **No handler declaration handles a labelled instance**, so no implicit handler serves one: a declaration handles one unlabelled effect, and an instance is labelled for the needs of one use, which the group written where it is handled meets.

## Scheduling

The search shares the machinery of [Elaboration](01-Elaboration.md) and adds none.

**Ordinary unification is attempted first.** `ρ1 ≡ ρ2` is solved under `transact`, so that an attempt which fails leaves `Ψ`, the constraint set, and the queues as it found them. Insertion is attempted only where that attempt **definitely fails** — a leftover known key or rigid tail in case (a) or (b) of row unification — and never where it merely succeeds by instantiating a metavariable. A row solvable by unification needs no handler.

**Shared tails cancel before anything waits.** Row unification removes the tails the two sides have in common before its case analysis, and the plan is read after the same cancellation. A goal is `Stuck` only where a **flexible tail survives that cancellation**, since assigning one adds keys and can still change `dom(F1)` or `dom(F2)`. It then joins the queue every other goal joins and is resumed when one of the metavariables it awaits is assigned.

The distinction is not a fine point: the ordinary case has a flexible tail on both sides.

```text
a ! ( Console | ?e )   checked against   a ! ( LiftIO | ?e )
```

Cancelling `?e` leaves `{ Console }` against `{ LiftIO }` with no tail on either side, so the key difference is settled and the plan is read off it. Treating an unsolved metavariable as a reason to wait would stall the very shape the mechanism exists for.

**A rigid tail is never a reason to wait.** A row variable bound by a `forall` contributes no key to the normal form, and nothing in the goal being solved can assign it one; a residual row open in that sense is as determined as a closed one.

Distinguishing "no handler for this key" from "not enough information yet" is the same three-way split synthesis goals use, for the same reason.

## Diagnostics

A row problem is reported as a row problem, naming what is missing rather than what was searched.

- A key with no implicit handler names the key and the row it stands in
- A key with several names the candidates and the modules they come from
- An ambiguous order names the handlers that the dependency relation leaves unordered, and says that writing the composition settles it
- A cycle is reported against the import environment that closes it, naming the modules whose declarations form it

A cell problem names the cell and where cells stand.

- `x!` or `x := e` naming no cell in scope names the name, and says that a cell is reached from the operation clauses of the handling expression or handler declaring it
- The same written where a cell of that name is closed — in an initial value, a `return` clause, the computation handled, or a handler applied as an item — names the part it stands in rather than treating the cell as undeclared
- Two `var` declarations of one name are reported where the second is written, as a name bound twice
- A `var` after a group or a handler of a handling expression, or after a clause of a handler declaration, names the cell and says that every `var` stands ahead of them

## What reaches Core

A handler takes a thunk and returns a computation, so handlers do not compose by application alone: **the result of one is thunked again before the next receives it.** Keeping the two apart makes the rule total. With `W'` the elements step 4 widens by, and `H1 … Hn` the plan in the order `≺` gives, innermost first:

```text
q0      = openEff [ W' ] ( λ (_ : Unit). e )      a thunk
di      = Hi ⟨ instantiation ⟩ q(i-1)             a computation
qi      = λ (_ : Unit). di                        a thunk again

e'      = q0 Prim.Unit        when n = 0
e'      = dn                  when n > 0
```

**The plan may be empty.** Where `ρ2` differs from `ρ1` only by keys no handler removes — a capability the expected row carries and the computation does not — step 4 widens and there is nothing to apply, so the thunk is forced at once. Writing `e'` as a nest of applications leaves that case with no term; writing it as `q0 Prim.Unit` gives it one.

Only `q0` is widened. Each later thunk stands at the row the handler below it produced, which already carries every target, so nothing further is owed.

```text
-- program : a ! ( Console | e ),  checked against a ! ( LiftIO | e )
Js.Effect.Console.runConsole [e] [a] [•] [•]
  ( openEff [( LiftIO )] ( λ (_ : Unit). program ) )
```

The widening takes the thunk from `Unit -{ ( Console | e ) }-> a` to the
`Unit -{ ( Console, LiftIO | e ) }-> a` the handler asks for.

The handler is an ordinary global, the thunk an ordinary lambda, the widening an ordinary `openEff`. **No subsumption enters Core**, so D8 holds of an inserted handler exactly as it holds of a written one, and the Core type checker rejects an elaborator that gets any of it wrong.
