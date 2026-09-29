# Implementation Plan

Once this specification is settled, the target of Phase A is determined.

1. **Define the Core AST** ([Kinds and Types](../03-Typed-Core/01-Kinds-and-Types.md), [Terms and Matching](../03-Typed-Core/04-Terms-and-Matching.md), [Modules](../06-Modules/01-Modules.md))
2. **Row normalization `nf`, the entailment decision `Γ ⊨ C`, and row unification** ([Rows](../03-Typed-Core/02-Rows.md), [Elaboration](../02-Surface-Language/01-Elaboration.md)) — the first target for unit tests and property tests
3. **The Core type checker** ([Core Type Checker](../03-Typed-Core/07-Core-Type-Checker.md))
4. **Hand-write the Core module of the vertical slice** ([Examples](../03-Typed-Core/08-Examples.md)) and run it through step 3 — the type checker's first end-to-end test
5. **Lowering to Mid IR**: the erasures of [Semantics](../03-Typed-Core/06-Semantics.md), and the mapping of decision trees and join points
6. **The JavaScript backend**
7. **Parser, name resolution, type inference, and elaboration**, built on top of steps 1 through 4

Steps 2 and 4 precede step 7 because the type checker can run before the parser exists. Being able to write Core by hand is also what demonstrates in practice that Core type checking is self-contained.

## Notes on step 2

Row unification is where subtle errors concentrate, and two properties deserve explicit regression tests.

**Two-sided refinement.** A constraint such as `{ a : A | ?r } ≡ { b : B | ?s }` cannot be solved by substituting into one side; it requires a fresh variable substituted into both. A one-sided substitution either produces an incorrect solution or fails an occurs check and rejects a solvable constraint.

**The rigid/flexible distinction.** A rigid row variable is not assignable but can be absorbed by a flexible tail on the other side. Case analysis that only checks whether a tail is empty gets this wrong.

## Notes on step 5

Two constraints must be respected even though the constructs they concern belong to Phase E.

**Do not assume one-shot continuations** in Mid IR's representation ([Semantics](../03-Typed-Core/06-Semantics.md)). Mid IR is designed in Phase A while effect lowering belongs to Phase E, so the assumption would be baked in before the decision is made.

**Represent partially applied constructors** ([Semantics](../03-Typed-Core/06-Semantics.md)). A constructor application with fewer arguments than its arity is a value and may be passed around. Mid IR should retain constructor application in a form that lowers either to curried functions or to a partial-application object.

**The bytecode and the interpreter that executes it belong to this step**, between it and step 6. Lowering Mid IR to a `.dmo` and executing one is what makes a program runnable before either web backend exists. See [Mid IR](../04-MiddleEnd/01-Mid-IR.md), [Translation](../04-MiddleEnd/02-Translation.md), [Bytecode](../05-Backend/01-Bytecode.md), and [Abstract Machine](../07-Runtime/01-Abstract-Machine.md).

**The interpreter is built in this order**, each step running programs the one before it cannot.

1. The run-time values
2. The pure instructions, with branches and join points
3. Closures, partial applications, calls, and tail calls
4. Globals, and module loading against a persistent registry
5. The handler stack, continuations, and cells
6. The operations, and the host's foreign registry
7. The REPL, whose shell belongs to the CLI and whose evaluator is a session of the interpreter
8. The `IO` runner, once something needs one executed

**The REPL is the interpreter's delivered use**, which is why it stands inside this order rather than after it: the module lifecycle it needs — an entry compiled to a module of its own, a redefinition adding a module rather than replacing one — is settled with the interpreter and not retrofitted to it ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

**The machine does not replace the Core evaluator.** Preservation reduces a Typed Core term one step and re-runs the type checker; erasure compares the typed relation against the erased one. A machine state carries no types, so it serves neither — there is nothing to type check, and no typed side to compare against. The Core evaluator is what those two properties are tested against, and the machine does not stand in for it. It is **a unit of its own** rather than part of step 4, which type checks a hand-written module and runs nothing.

What the machine adds is of two kinds. It is a **second evaluator to compare against**: one program run both ways should give the same value and the same sequence of observable effects, which tests the whole of translation and lowering at once and is what catches a fold that reorders effects or drops one. And it **runs programs a one-shot backend cannot**, a second resumption of a continuation among them (D33), so effect safety and progress can be exercised on terms that D18's gap otherwise puts out of reach.

Anything stronger — asserting preservation over machine states — would need a correspondence between a machine state and the Core term it stands for, and nothing defines one.

## Notes on step 6

The set of FFI the backend must implement is `stella-base-0.1`, the first version of the `Base` ABI surface ([Open Questions](../99-Open-Questions/01-Open-Questions.md)). The longer it is deferred, the more the standard library settles into a shape that depends on FFI, so it should be fixed while writing this backend.

**The backend reads a `.dmo`** (D45, [JavaScript](../05-Backend/05-JavaScript.md)), so its tests start from the bytecode fixtures on disk rather than from a lowered value, which is what keeps it from leaning on anything the file does not carry. It is built in this order, each step settling what the next depends on.

1. **Calls, branches, join points, tail calls, and the operations.** The execution model is chosen here, before any handler exists, since a tail call is already a transfer the host does not provide; the operations come with it, branches needing them to be tested and none of them depending on the model
2. **Handlers and continuations.** A `full` clause resuming twice, each resumption from the captured state, and a continuation captured outside a region carrying its cells: these are the cases that show the model represents a continuation, and D18's record of the backend changes once they pass
3. **The foreign manifest and the drive loop**
4. **Purity**: the per-function record in the format, and a pure entry kept a host call
5. **The lower-IR optimizations**: an evidence environment in place of a search of the stack, and a `fast` clause run in place, each resting on what the model of step 2 already guarantees

**Comparing the backend with the machine tests the backend and not lowering**, both reading what lowering produced. Until a Core evaluator exists, lowering is covered by its own tests and by execution tests whose expected results are fixed independently from hand-written Core. **Building that evaluator is a unit of its own**, and it precedes any claim that lowering preserves meaning broadly; it need not precede the backend's first steps.

## Notes on step 7

**The elaborator's kernel precedes the parser rather than following it.** What a synthesizer needs — the metavariable operations, unification, entailment, observation of the environment, and the construction of Core⁺ terms — depends on no surface syntax, and a goal can be reached from a hand-written Core⁺ term exactly as a Core module is hand-written in step 4. `check`, `infer`, quotation, and hygiene are the part that waits for the Surface AST ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)).

The step therefore divides, and the divisions are ordered by what each is the first thing to make testable.

1. **The execution contract** — the two layers, a pending job's envelope and the three jobs, the three outcomes, the attempt transaction, and `SynthRef` (D39, D40)
2. **Kind and type unification** — `?k`, `unifyKind`, `unifyType`, and the discharge of the payload equations row unification emits
3. **The transaction and the scheduler**, tested first against scripted jobs rather than real goals: registration under an identifier, rollback, wakeup, and the diagnostic at quiescence
4. **Core⁺ terms** — `?m`, the synthesis goal, the typed hole, zonking, and `toCore`
5. **A host runner, and the elaboration vertical slice**
6. **A guest runner**: one small `f` in hand-written Typed Core, run on Steam, through the same scenario
7. **The standard type class resolver** — recursive search, coherence, ambiguity, and search trace diagnostics

Division 3 is testable before any synthesizer exists, which is what makes scripted jobs worth writing: a scheduler exercised only through real goals is one whose failures are attributed to whichever resolver was running.

### The elaboration vertical slice

The counterpart of step 4, and it needs no parser.

```text
a hand-written Core⁺ term carrying one synthesis goal
  → the goal is attempted and postpones, awaiting a metavariable
  → an unrelated part of the term assigns that metavariable
  → the goal is re-run from its beginning and solves
  → the term is zonked, and toCore succeeds
  → the Core type checker accepts the result
```

Passing it exercises the goal record, the three-way outcome, the blocked table, the rollback, type unification, and the boundary invariant at once. The regression cases that belong with it are in [Elaborator API](../02-Surface-Language/03-Elaborator-API.md).

Division 6 is what establishes that the bootstrap cycle is cut, and it does not wait on a complete resolver: one `f` solving one goal is the whole of what is being shown.

## Testing the properties instead of proving them

[Semantics](../03-Typed-Core/06-Semantics.md) states progress, preservation, effect safety, and erasure without proof. Proving them for a calculus with rows, effect rows, and handlers is a substantial undertaking, and most of the confidence it would buy is available more cheaply: **each property can be turned into a property test.**

This requires a Core evaluator, the unit of its own that the notes on step 5 name. Type checking a hand-written module confirms that it is well typed; running it is what confirms that it computes.

**Preservation** is the most directly testable. Generate a well-typed Core term, reduce one step, and re-run the type checker.

```text
assume Σ ⊨ G
assume G is Core-modelled
for each generated e with ·;· ⊢ e : τ ! ρ:
    while e is not a value and fuel remains:
        c = step(G, e)
        if c is a fault:  stop; the run ends, and nothing is asserted
        assert ·;· ⊢ c : τ ! ρ
        e = c
```

A step to a fault ends the run rather than failing the test: a fault carries no type, so there is nothing to re-check.

Both the type and the ambient row are checked for equality. A generator that produces `G` must satisfy **both** premises — `Σ ⊨ G` and `G` Core-modelled — and supplying an ill-typed global definition, a non-conforming `δ_f`, or one whose call does anything beyond returning an outcome its arguments fix invalidates the property rather than testing it.

The type checker is already required for step 3, so the assertion costs nothing to write. What takes work is the generator: producing well-typed terms rather than arbitrary ones. Generating type-directed — choosing a type first, then building a term of it — is the practical approach, and it doubles as a source of test cases for the checker itself.

**Progress** falls out of the same loop: if `e` is not a value and `step` returns nothing, the property has failed.

**Erasure** is a differential test. Run a term under the typed relation and its erasure under the erased relation, and compare the sequences of observable steps; a typed step that only consumes a coercion corresponds to no erased step.

**Effect safety** deserves separate treatment, because it is the property that ordinary tests are least likely to reveal: a violation does not crash, it silently performs an effect.

The test is **not** to reject every `perform`. A term well typed at ambient row `()` may perform operations internally, so long as each is enclosed by a handler for its key; rejecting them outright would fail correct programs. What the evaluator maintains instead is a stack of installed handler keys, and it asserts that **every `perform` it executes finds a handler on that stack**. Reaching a `perform` with no matching handler is the failure.

Generating terms that call effectful functions and wrap them in handlers is what exercises the property; what is being checked is that the wrapping is genuinely exhaustive.

Extending the generator to `foreign` declarations is worthwhile once the FFI surface exists, since D23 together with condition (3) of `Σ ⊨ G` is what keeps effect safety from being violated at that boundary. D23 alone constrains only the declared type.

**Machine-checked or paper proofs are deferred.** They become worth revisiting if the work is to be published, or if one subsystem keeps producing subtle bugs that property testing does not catch.

**Conformance of the global environment** is a premise of every property above, not something they establish. A test harness supplies `G` and must therefore guarantee `Σ ⊨ G` itself: global definitions are well-typed values, and each `δ_f` returns either a value of the instantiated result type — the one the spine judgement gives — or a permitted fault, performs no proper effect and runs no reified computation it constructs, applies no Stella function value, terminates, and has no observational effect — faulting among them — where the declaration asserts `#observ(none)` ([Semantics](../03-Typed-Core/06-Semantics.md)).

**The separate Core-modelled premise is the other thing the generator has to respect, and it is the easier of the two to miss.** It is not a clause of `Σ ⊨ G` and is not implied by it: it asks that returning an outcome the arguments fix be the **whole** of what a saturated call does, so no hidden read, no write, and no identity the arguments do not determine. A harness whose `δ_f` reads a counter or a clock, or writes to a cell the next call reads, invalidates the property rather than testing it, and it does so silently — the run completes and the assertion passes. **Faulting is not what the premise excludes**: a `δ_f` that faults on an argument it always faults on satisfies it, which is what keeps `Base.String.codePointAt` and the fault branch of progress inside the properties. A generator that produces a hidden read or a write is producing a term the relation gives no step to.

For generated `foreign` declarations this is easy, since the harness writes `δ_f` and can make it a pure total function that never faults.

**The two premises are owed by different parties, and a backend test suite should not conflate them.** `Σ ⊨ G` is a conformance obligation on a real backend, and a suite should check it directly rather than relying on the property tests above to expose a violation. Being Core-modelled is **not** such an obligation: it is the condition under which the reference semantics applies, and a backend is expected to supply entries that fail it — `Base.Array.unsafeSet` among them ([Semantics](../03-Typed-Core/06-Semantics.md), D41). What follows for a suite is that those entries are outside what the properties cover and need tests of their own, not that supplying them is a defect.

## A catalogue of regression tests

Each entry below is a case in which a plausible implementation gives the wrong answer. They are worth writing as tests before the corresponding code rather than after, since property testing reaches most of them only by chance: several require a specific combination of features to arise at all.

The heading of each group names the step of the plan that the group belongs to.

### Row normalization and unification (step 2)

| Input | Required outcome |
| --- | --- |
| `{ a : A \| ?r } ≡ { b : B \| ?s }` | Solved with a fresh `?t`: `?r := ( b : B \| ?t )` and `?s := ( a : A \| ?t )`. Substituting into one side alone either yields an unequal pair or fails an occurs check on the symmetric attempt |
| `forall (r : Row Type). Record r ≡ Record ( name : String )` | Fails. A rigid tail cannot absorb a known field |
| `?s ≡ ( a : A \| r )` with `r` rigid | Succeeds. A rigid tail **can** be absorbed by a flexible one on the other side |
| `( name : String \| r ) ≡ ( name : String \| s )`, `r` and `s` distinct rigid variables | Fails. Distinct row variables are not identified |
| `⟨∅;{r,s}⟩ ≡ ⟨∅;{s,r}⟩` | Succeeds. The tail is a set |
| `⟨∅;{?r,?s}⟩ ≡ ⟨{a↦A};∅⟩` | Stuck, not failure. Two solutions exist, so the constraint waits |
| A solved `?r := D ⊎ ?t` where `k ∉ ?r` was required | The obligation that named `?r` names `?t` once its constraint is zonked, and `k ∉ dom(D)` is decided again. Omitting either produces Core that is not well-kinded |
| `r ⊎ r` | Ill-kinded. The disjointness side condition rejects it before normalization |

### Kinds and constraints (step 3)

| Input | Required outcome |
| --- | --- |
| `forall (e : Effect). …` | Rejected. `Effect` is not a quantifiable kind |
| `forall (f : Type -> Effect). …` | Rejected, for the same reason |
| `Proxy [[Effect]]` | Rejected. Instantiation also requires a quantifiable kind |
| `forall (f : Type -> Type). …` | **Accepted.** Higher-kinded types must survive the restriction |
| `forall (r : Row Effect). …` | Accepted |
| `Row (Type -> Type)` | Ill-formed. `Row` takes only a row element kind |
| `#Ok ∉ ( Console )` | Rejected. A tag is not a key of a `Row Effect`; a `SymbolKey` would be admitted, since it may key a labelled instance |
| `ρ1 # ρ2` with `ρ1 : Row Type` and `ρ2 : Row Effect` | Rejected. Both sides share one row element kind |
| `Proxy [[Type]] [Int]` and `Proxy [[Row Type]] [( x : Int )]` | Both accepted. Type and data constructors carry independent kind schemes |
| `forall (f : Row Type -> Type). …` | Accepted. A row may be consumed |
| `forall (f : Row Type -> Row Type). …` | Rejected. Only row syntax produces a row, which is what keeps `nf` total on well-kinded rows |
| `forall (f : Type -> k). …` | Rejected. `k` may be instantiated with a row kind |
| A `Σ` entry `MkRow : Type -> Row Type`, used as `Record (MkRow Int)` | Rejected at the occurrence. Kinding does not trust the table for this |
| `(name ∉ r) => Record ( name : String \| r )` | **Accepted.** The constraint is assumed while the body is kinded; without it the row is not sharp |
| `(name ∉ ( name : String )) => Int` | Rejected. `Γ, C` requires `C` to be satisfiable |

### Row keys (step 3)

| Input | Required outcome |
| --- | --- |
| `( SymbolKey X : Int, TagKey X : Int )` | **Accepted.** The two are different keys; sharing a spelling does not make them collide |
| `( cache : State Int, counter : State Int )` | **Accepted.** One effect, two elements, distinguished by their keys |
| `( cache : State Int, cache : State String )` | Rejected. The same key twice, whatever the payloads |
| `( State Int, State String )` | Rejected. Both derive `EffectKey State` |
| `( PositionKey (-1) : Int )` | Rejected. The grammar gives `PositionKey` a `Nat`, and the AST holds an `Int`, so the bound is a kinding side condition |
| `( EffectKey State : Int )` | Rejected. `Γ ⊢ k key Type` admits the structural keys only |
| A handler keyed `cache` enclosing `perform counter.get` | The `perform` passes through. `Ev_k` matches on the key, and `counter` is not `cache` |
| `perform cache.get` where the row has `cache ↦ State Int` | The operation's type comes from `Σ(State)`, not from `cache`. A checker that looked the key up in `Σ` would fail here and pass on the unlabelled form |
| `handle (handle e with h) with h` at one key | Rejected. The inner one would stand at `( k \| ( k \| ρ ) )`, which is not sharp |
| A pure function handling `E` within itself, called through `openEff [( E )]` under an outer handler of `E` | **Accepted.** No row carries `E` twice; the two handlers meet only in the run-time stack |

### Decision trees and handlers (step 3)

| Input | Required outcome |
| --- | --- |
| `switchCtor` with no default, not exhausting the constructors | Rejected |
| `switchLit` with no default | Rejected. A default is mandatory |
| `switchKey` over a closed variant enumerating only some keys, no default | Rejected. A value would be left with no destination |
| `switchKey` over a row with an unknown tail, no default | Rejected |
| `switchCtor` with a default whose body is ill-typed | Rejected. The default branch is typed like any other |
| `switchKey` default | The occurrence is refined to the residual `Variant r'`, not left at the original type |
| A handler omitting an operation of `E` | Rejected. `handle` removes the keyed element, so an operation without a clause has nowhere to go |
| A handler clause that does not respect an operation's own `forall b̄` | Rejected |
| An interpreter sequencing a native action before resuming a continuation, the residual row not being closed | Rejected. That continuation is `a -{ρ}-> IO r`, which the pure arrow of `Base.IO.bind` does not take. Abandoning the continuation, or resuming it first, is admitted |
| A pure global applied where the ambient row is not empty, as `Base.Int.add n 1` is under `( State Int \| e )` | Rejected without `openEff`. An application requires the arrow to carry the ambient row and containment is never inserted (D8); currying makes it one `openEff` per argument consumed |
| A data constructor applied in a handler clause, the row outside the handle not being empty | Rejected for the same reason. Constructor arrows are pure by declaration, so one is widened like any other pure global. An instantiation such as `Prelude.Nothing [a]` needs no widening, applying nothing |
| `handle (perform E.op v) with h` at ambient row `()` | **Accepted.** Effect safety is not "no operation is performed" |
| A `λ` whose body jumps to a join point bound outside it | Rejected. The join point context is discarded at a lambda |
| A `letjoin` in argument position whose definition jumps to itself | Accepted. The root of a definition is in tail position wherever the `letjoin` stands |
| `switchCtor` whose first branch reaches no leaf and whose second does | Accepted, at the type the second gives. The written order of branches carries no meaning |
| `bind x = o . k` with no dispatch having established `o . k` | Accepted. A record has an element at every key of its row |
| A handler clause whose continuation is typed at the inner row | Rejected. It is `τ' -{ρ}-> β`, the row outside the handle and the result of it (D15) |
| A clause binding `forall b` where the operation declares `forall a` | Accepted. The binders are aligned, a handler respecting the polymorphism rather than the spelling |
| A clause binding a different number of them, or one at another kind | Rejected |
| A `full` clause's body | Checked at the answer type `β`. It is the clause that supplies what the `handle` returns |
| A `fast` clause's body | Checked at the resume type `τ_i'`. `β` appears nowhere in its premise (D28) |
| A `fast` clause whose body has the answer type instead | Rejected by that check |
| A `fast` clause carrying a continuation binder | Not representable. The forms are separate, so no clause has an optional one and no marker is absent |
| A handler mixing a `full` clause with a `fast` one | Accepted. The form is written per clause |
| `fast abort1 [b] (_ : Unit) -> perform Abort2.abort2 [b] Prim.Unit` | Accepted. A polymorphic resume type rules out a pure terminating body, not a translation into another effect |
| The handler interpreting `Partial` into `Maybe` | `full`. Its answer is `Maybe a` where the computation's is `a`, and only a `full` clause supplies an answer |
| `readCell k` in the computation a handler handles | Rejected. The region stands in the row the operation clauses are typed at, not in that computation's (D36) |
| `readCell k` in the return clause | Rejected. The return clause stands at `ρ`, which is what makes an ordinary return hand back no state |
| `full next (_, k) -> let _ : Int = k Prim.Unit in readCell n`, the answer type being `Int` and the cell `Int` | Accepted. A `full` clause stands at `ρ'` and may make a cell's value its answer; what the rules withhold is the automatic return, not the ability |
| `readCell k` for a key the region's layout does not declare | Rejected |
| `writeCell k e` | Typed `Unit`, not the cell's type. The result may be dropped, which is what lets a clause set a cell and carry on |
| A clause returning `λ (_ : Unit). readCell k` as the answer | Rejected. The closure carries `( region r ι \| ρ )` in its arrow, so it mentions `r`, and `r ∉ ftv(β)` |
| A continuation typed to carry the region, where the handle's residual row does not | Rejected by the same condition, `r ∉ ftv(ρ)` |
| A handler whose `cells` binder is already bound where the handler stands | Rejected. `r ∉ dom(Γ)`: the layout is kinded outside the binder and then stands inside it, so a binder shadowing an outer variable would draw that variable under the region |
| An outer type variable standing in the layout and in the answer, beside a region that binds another name | Accepted. The two are different variables and neither condition above reads one for the other |
| A handler owning a region whose residual row is not known to lack one | Rejected. `ρ'` is sharp only under `RegionKey ∉ ρ`, which the rule requires and an effect-polymorphic handler assumes |
| A handler owning a region, installed inside another region's clause body | Rejected by that premise, there being a region in the ambient row already |
| A handler owning a region, installed inside the computation another handler handles | Accepted. The handled computation carries no region, so the two never meet |
| `handles` naming a region, or a `perform` naming one | Rejected. Both rules require the payload to be an effect application, and a region's is not |
| A handler declaring no cells | Takes the rule it always took. **No region is opened and no `RegionKey` enters any row**, so a handler owning one may still be installed within it |
| A layout writing one key twice | Rejected. The initial values are given one per key |
| A `region r ι` type whose `ι` has a tail | Accepted. Only a layout is closed; a type is a row, which is what a helper polymorphic over the rest of a region needs |
| `guard` whose consequent reaches no leaf and whose alternative does | Accepted, at the type the alternative gives |

### FFI and declarations (step 3)

| Input | Required outcome |
| --- | --- |
| `foreign log : String -{( Console )}-> Unit` | Rejected. An effectful result arrow would let the effect bypass a handler |
| `foreign mapImpl : ( a -{e}-> b ) -> …` | Rejected. An effectful argument arrow would leak the calling convention across the boundary |
| `foreign Js.Console.log : String -> IO Unit` | Accepted. This is the shape every real-world leaf takes |
| `foreign use : Record ( cb : Int -{( Console )}-> Int ) -> Unit` | Rejected. An arrow reaches the boundary through the payload of a row as readily as through an argument |
| A `foreign` whose only effectful arrow stands inside a constraint | Accepted. A constraint is an erased proposition and carries no value across the boundary |
| An effect with an operation `liftIO : forall a. IO a ->* a` | **Accepted.** `perform` carries the opaque `IO` to the handler without executing it. What it costs is the granularity of the capability, not soundness |
| `newtype` on a type with two constructors, or with one constructor of two fields | Rejected. The backend erases the representation on the strength of this flag |
| A `nonrec` whose right-hand side refers to a `foreign` declared later in the text | Initializes. Constructors and foreign implementations enter the environment before any value declaration is evaluated |
| A `nonrec` referring to a later `nonrec` | Rejected. Value declarations are in dependency order |
| A top-level `rec` group whose members have different kind schemes | Accepted. Every scheme is registered before any right-hand side is checked |
| A `Σ` entry `T : forall k. k` | Rejected where the signature is built. Every use site instantiating it at `Type` would pass, so an occurrence check alone lets it in |
| A `Σ` entry `T : k -> Type` with nothing binding `k`, or `T : Effect -> Type` | Rejected there too. The whole scheme is checked under the kind variables it binds, not only its result |
| One entry reaching a name through two import paths | Accepted. A name belongs to the module that declares it, so the two are one entry |
| Two different entries under one name | Rejected where the parts are merged, rather than resolved by preferring either |
| A data constructor and a value of one name | Rejected. A constructor is an ordinary global name, so the two share a namespace |

### Reduction (step 4, once an evaluator exists)

| Input | Required outcome |
| --- | --- |
| `let x = (openEff [( E )] f) 0 in perform E.op Prim.Unit` with `f : Int -> Int` | Steps to `let x = openEffC [( E )] (f 0) in …`. Discarding the coercion leaves the two parts of the `let` with no common ambient row |
| `id [Int -> Int] f 0` with `foreign id : forall a. a -> a` | `δ_id(f)` runs and returns `f`, and `0` is applied to the result. Testing the substituted type instead absorbs `0` and calls `δ_id(f, 0)` |
| `foreign clock : IO Time`, an arity-zero foreign | Steps to `δ_clock()`. The spine is saturated as soon as it is formed |
| `M.f v` for a unary foreign | Steps. The final value argument must fire the implementation |
| `Base.IO.pure [Int]` | Steps. A polymorphic foreign accumulates the type argument on its spine |
| `letjoin j (x : Int) : Int = e1 in let y = (λz.z) 1 in jump j y` | The body reduces before the jump fires |
| `letrec { f = λx. … } in e` | Unfolds only in elimination position. No term steps to itself |
| `switchKey` on a value wrapped in `weaken` | Dispatches on the key actually injected. `weaken` is a value form and is looked through |
| `bind x = o in guard (p x) …` | The substitution happens before descending, so the guard's condition has no free `x` |
| That call, once it is evaluated | The innermost handler of the key is chosen: `Ev_k` lets no `handle` of that key stand between it and the hole |
| `H Ev_k[perform k.op v] with h` whose clause for `op` is `fast` | Binds the body with a `let` and rebuilds the handler around `Ev_k` with that binding in the hole. No continuation value is built, and the `let` is what reconciles the clause's row with the handled computation's |
| A `fast` clause body performing an operation that a handler inside `Ev_k` also handles | Answered by a handler outside `h`. The body stands outside `Ev_k`, so a handler a function reached through `openEff` installed there is not in its context |
| A `fast` clause body reading or writing a cell whose key a region inside `Ev_k` also declares | Reaches the region outside `h` declaring the key — `h`'s own where it owns one, that region standing outside `h`. The region inside `Ev_k` is neither read nor written |
| A `perform` reaching a handler whose `key(ent)` differs | Does not arise. Both rules require `key(ent) = k`; `Ev_k` says only that no nearer handler carries it |
| `handle e with h @ ( v̄ )` where `h` declares cells | Steps to `region [r'] (k̄ ↦ v̄) in ( handleO e with h[r := r'] )` for a globally fresh `r'`. The region stands **outside** the handler, which is what a clause body — placed outside it too — needs in order to reach a cell |
| The term after that step | Type checks. `handleO` is a run-time form with a rule of its own, at `ρ'`; without one, preservation fails at the first step |
| The opening step where the handled computation, or an initial value, binds a variable of the region's name within itself | The step renames to a globally fresh `r'`. The region it creates scopes over both, where the handler's `cells` binder scoped over the operation clauses alone, so keeping the name would bring two binders of one name into one scope. The context binding that name is a different matter and does not arise: the typing rule requires the binder fresh for `Γ` |
| `h[r := r']` applied to a `full` clause | Renames the `r` of the continuation's annotation `τ' -{( region r ι \| ρ )}-> β` as well as the one in the body. Renaming bodies alone leaves the installed handler ill-scoped |
| `region [r] θ in ( handleO v with h )` | Steps to `e_r[x := v]` in **one** step. Closing the region and running the return clause are not separable, which is what leaves no moment at which an answer and a cell both exist |
| `handleI v with h`, a reinstatement finishing | Steps to `openEffC [( region r ι )] ( e_r[x := v] )`. The return clause runs and the owner's region is untouched, the widening reconciling the clause's `ρ` with the ambient `ρ'` |
| `region [r] θ in v`, a `full` clause having produced the answer | Steps to `v`, the region closing with no return clause. Without this rule the `full` path reaches no value |
| A continuation applied by any clause | Rebuilds `handleI`, never `handleO`. A region has one owner and it is not what a resumption reinstalls |
| A `fast` clause of a handler owning a region | Its body is bound by a `let` and the value placed in the hole. Placing the body itself there does not typecheck, the body standing at `ρ'` and the hole at the handled computation's row |
| A `full` clause of a handler installed **outside** a region, resuming twice | Each resumption begins from the cell contents at the capture, `Ev_k` containing the region. A write during the first is not seen by the second, which a store would not give |
| A `full` clause of the handler **owning** the region, resuming twice | Both share the region, which stands outside what was captured. The cells stay live across the handler's own resumptions |
| `writeCell k v` | Steps to `Prim.Unit`, the write having no result of its own. Reading back what was just set takes a `readCell` |
| A saturated foreign whose `δ_f` faults | Steps to `fault φ`, which propagates out of every context including `handle`. It is not caught by a handler and is not the `Partial` effect |
| A term at ambient row `()` reaching a `perform` with no enclosing handler | Does not arise. This is what effect safety asserts |

### Erasure (step 5)

| Input | Required outcome |
| --- | --- |
| A term and its erasure | The same sequence of observable steps, modulo steps that only introduce or discharge a coercion |
| A term whose reduction faults | The erased term faults identically |
| The number of run-time arguments a backend passes to `δ_f` | Determined by the arrow count of the **declared** type, not by the instantiated result type |
| A handler carrying a `full` clause and a `fast` clause | Both markers survive erasure, Core having written each of them. They carry no type information, and a backend lowers the two differently |
| A handler owning a region | The keys and the values survive; the region variable and the cells' types do not. Reduction pairs the keys with the initial values and `Ev_c` walks by them, so neither is an annotation (D36) |

### Translation to Mid IR (step 5)

| Input | Required outcome |
| --- | --- |
| A saturated call to a pure global under a non-empty ambient row, wrapped in one `openEff` per argument consumed | One `callk`. Peeling the spine looks through `openEff`, `TyApp`, and `ConstraintApp`; stopping at the first of them emits a chain of `callu`s where one known call belongs |
| `Main.Nil [Int]` | The atom `const Main.Nil`. A saturated constructor of arity 0 allocates nothing |
| A `foreign` of arity 0, referenced bare | `ffi f []`, which **calls the implementation**. The spine is saturated as soon as it is formed, so treating the reference as a value leaves the call unmade |
| A `foreign` of arity `n > 0`, referenced bare | `pap f []`. It is a value, not a call and not an atom |
| A top-level value referenced bare | The atom `global M.x`, which is a load |
| A constructor applied below its arity | `pap`. Over-application does not arise, a constructor's declared result never being an arrow |
| A global whose definitional arity the interface does not publish | `callu`. Correct for every callee; arity buys `callk` and never correctness |
| `o ! Ctor . j` | Materialized inside the branch that selected `Ctor`, and nowhere earlier. Projecting it before the dispatch reads a field that is not there |
| One occurrence used by several nodes | Projected once. An occurrence has no effect, so naming it once is sound |
| A `Case` in argument position | A join point binding the continuation, not the continuation duplicated into each branch. A `Handle` needs none of this, being a computation |
| A `Bind` of an occurrence already materialized | An alias in the translator's environment; no instruction is emitted |
| A handler clause body | A function with an explicit capture list. No join point of the enclosing scope is in scope in it, nor in the body of the `handle` |
| A member of a top-level `rec` group | A closure over an **empty** capture list. Its recursive references are global names, so nothing is evaluated to install it |
| A `nonrec` whose right-hand side diverges, referred to by nothing | Initialization hangs. Evaluation is eager and in declaration order |
| A binding whose Core type is a type variable | `Rep Val`. Sound wherever a type is not to hand, and the cost is precision |
| `f (perform A.x Prim.Unit) (perform B.y Prim.Unit)` | `B.y` is performed first. An application evaluates its argument before its function, so a spine runs right to left (D35) |
| A spine folded into one call, against the same spine as nested applications | The same sequence of observable effects and the same faults, in the same order. This is what makes folding sound and is worth a generated test rather than a written one |
| A global of definitional arity 1 applied to two arguments | `callk` with the first, then `callu` with the second. Both arguments are evaluated before either call, and whatever `f x` performs happens between the two calls |
| `nonrec alias = Main.f` | Arity **absent**, not 0. What it stores is a function of `Main.f`'s arity, so reading 0 makes every call to `alias` an over-application of a nullary function |
| `λx. λy. e` | **One** function table entry of two parameters, so that the entry's arity and the definitional arity agree. Two entries of one parameter each would have `callk f [a, b]` supply two arguments to a function of one |
| `Λa. λx. Λb. λy. e` | The same entry of two parameters. The run of lambdas is taken after erasure, so a type abstraction between two of them does not break it |
| A `Handle` whose value is consumed by a surrounding expression | A `let` binding a `handle` computation. Its body is a function, so the return clause — entered later, and a function itself — has an ordinary call's result to give back rather than a join point it cannot reach |
| `update k e1 e2` where both operands are computations | `e1`, the **record**, is evaluated and passed first. `extend` takes them the other way about, so a translation reading one convention for both reverses the effects of the two operands |
| A right-hand side that is a lambda under `openEff`, `[τ]`, or `[•]` | Its definitional arity is the lambda's. A run of lambdas is taken after erasure, so stopping at a wrapper reads the definition as taking no argument and degrades every call to it to `callu` |
| The locals of two functions | Numbered from zero in each. A `Local` is unique within a function and not beyond one, so numbering across the module would leave a backend renaming before it could use one as a frame slot |
| The `source` of a lifted function | The annotation of the term the function was made from, wrappers included — not that of the body left once the lambdas come off, and not that of the lambda left once the wrappers come off. A lambda annotated 10 over a body annotated 11 records 10; an `openEff` annotated 30 over that lambda records 30 |
| Where the wrappers erasure removes are looked through | Dispatch reads what erasure leaves; the node as it stands is what supplies the type and the annotation. Recursing into the inner term instead loses the span of the whole and narrows the type a `[τ]` had settled |
| `weaken k [τ] (f x)` | One `callk`. Peeling a spine looks through **every** wrapper erasure removes, not only the four that can wrap a function: a peel stopping at `weaken` returns the term it was given with no argument taken off, and naming that head reaches the same term again |
| A saturated call to a `Base` entry the ABI fixes the meaning of | `prim`, not `ffi`. What divides them is what the name means: an entry returning no `IO` is an operation every consumer carries out, and one returning `IO`, or one of a target namespace, names an implementation |
| The same entry applied below its arity | `pap` over the foreign. Only a saturated one is an operation |
| A program using an operation | The entry it realizes is recorded all the same. An operation is how an entry is carried out and not a way of not using it, so target validation still finds it |
| A `tail` of an operation | The instruction followed by `RET`. An operation is not a transfer of control, so it has no `Tail` of its own |
| `let z = y in …`, where `y` is already a local | No local is created and the debug table is untouched. Recording `z` against `y`'s local would rename `y` |
| A local holding a projection, or an intermediate result of a folded spine | Named nowhere. It was created for no name |

### Lowering to bytecode (step 5)

| Input | Required outcome |
| --- | --- |
| A branch of a `BRC` | A `Node` held inline. A decision tree stays a tree, so a branch is not an edge to a block elsewhere (D32) |
| A `jump` | A `JMP` naming the join point. Never an offset |
| Two branches that cannot both run | Distinct register slots. There is no register allocation, so slots are not shared |
| An atom that is a literal | `LOADK` into a slot of its own before the instruction that takes it |
| A Mid IR `tail` of a `ctor` or a `closure` | That instruction followed by `RET`. Only a call has a `Tail` of its own |
| A group of mutually capturing closures | `CLOSN` for every member before any `SETCAP`. Filling one capture list first reads a closure that does not exist yet |
| A continuation applied twice | Two independent runs, each resuming from the state that was captured, so that what the first did does not reach the second. Each application returns to the `CALLU` that made it rather than to the `HNDL` that installed the handler (D33) |
| A `fast` clause | No continuation value is constructed, and the continuation is not split |
| A `PERF`, `CGET`, or `CSET` in a `fast` clause's body, where a handler or a region between the answering marker and the `PERF` holds the key | Passes over them to what stands below the answering marker. What the body installs itself is found as usual, and a `full` operation the body performs, resumed twice, leaves the body where it was each time |
| `perform` under two handlers of one key | The innermost. Handlers of one key nest at run time, `openEff` being what puts a self-handling function under an outer one |
| A faulting `FFI` inside a `handle` | The whole continuation is discarded, handler markers included. A fault is not the `Partial` effect and no clause sees it |
| A `JMP` read from a file | The destination's parameter registers come from the `Join`, which names them. A count alone leaves a consumer unable to perform the transfer |
| A tail call in the body of a `handle` | The marker and the path to the return clause survive it. The marker stands below the body's activation, which is the one a tail call replaces |
| `RET` at the end of a `handle` body | The return clause runs and its own value goes to the `HNDL`. `RET` itself has no case for a handler; where the marker stands is what produces this |
| A `Base` operation applied short of its arity | A `pap` whose callee is the operation, and the operation in `PRIMS`. A callee naming the entry instead would have a backend supply what the ABI never obliged it to |
| A `Base` entry declared at an arity the manifest does not give it | Rejected, wherever it is named — called, partially applied, or referred to bare at no arity |
| A Mid IR module whose locals are not dense from zero, or whose parameters are out of place | Rejected before any lowering. A register is a local's number, so a gap displaces every slot after it |
| A module lowered with its debug table | `DEBUG` keyed by function index and register, holding what translation recorded |
| A function table whose entries do not stand at their own identifiers | Rejected. A consumer reaches a function by index, so an entry out of place is reached under another's name |
| A `nonrec` whose right-hand side is a lambda | Installed as a function, not evaluated. Its definitional arity and its initialization are read off the same term, so a known call reaches a function of the arity it supplied |
| Two join points of one identifier in one function | Rejected. A lowering puts them in one flat table, so the second leaves a jump with two destinations |
| A local read in a branch that does not bind it | Rejected. It passes every check of layout alone, the numbering across a function being dense and unique either way |
| A partial application of an operation, read back from a file | The operation alone. The entry it realizes comes from the ABI version, so no reader can find the two disagreeing |
| `isNewtype` on a constructor | Carried from Core through Mid IR into `CTORS`. A `newtype` and a data type of one constructor with one field have the same shape, so a backend erasing the representation cannot tell them apart without the flag |

### The host's foreign table (step 5, interpreter 6)

These are about the table itself and not about where it came from, so a table written by hand is what a test supplies and nothing here imports anything ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)). **Assembling one from a manifest is a separate group** below (D43): keeping the two apart is what lets a failure in either be read as its own.

| Input | Required outcome |
| --- | --- |
| A module declaring a foreign the table does not hold | Refused at load, and the module is not committed. Whether anything calls it makes no difference |
| The same, where nothing calls that foreign | Refused all the same. A program whose foreigns are incomplete does not start, and reachability is not what decides it |
| A module declaring a foreign the table holds at another arity | Refused, and reported as the disagreement rather than as an absence. A call site is checked against the declaration, and the declaration is what the table was to match |
| The store after any refusal | Unchanged. A failed load leaves the next one nothing of the interpreter's to trip over |
| A body that writes to the host and then refuses during initialization | The module is not committed and the write stands. What is unwound is the interpreter's own state, and host state is outside it ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)) |
| A foreign the interpreter claims as a `Base` operation, with the table holding that name too | The operation is carried out and the table's body is never called. An operation's meaning is the ABI's, not something a host substitutes for |
| `Base.Int.add` declared at an arity the ABI does not give it | Refused. The source is selected by the name, so the arity is checked against the ABI's and against nothing else |
| The same, with the host's table holding that name at exactly the declared arity | Refused all the same, and the body is not called. Selecting the source on the name **together with** an arity is what would let a host implementation stand where the ABI fixes an operation's meaning |
| A saturated `FFI` | The body is called once, with every argument at once, and its value reaches the destination register |
| A body returning an `IO` value | That value reaches the register as it stands. No instruction examines one, so nothing wraps it, unwraps it, or executes it |
| That value passed on to another foreign | It arrives as it was. Carrying an `IO` needs no drive loop, which is what lets the two be built in either order |
| A body that refuses | A fault, which discards the continuation entire — handler markers and region frames included — and ends the run |
| A body that throws where it is applied, rather than where an effect it returned is performed | Caught all the same. The application itself is inside the catch, which is what the host function type is for |
| A body that throws | Caught, and a fault kept apart from a refusal: the same propagation, a different report. An exception escaping would end the run outside the fault path, leaving the stack undiscarded and a session unable to answer the next entry |
| A body that throws, inside a session | The session answers the next input. This is what catching buys, and it is the reason the boundary is not left candid |
| A reference below the arity, then applied to the rest | One `pap`, and the body called once when the last argument arrives |
| `TAILFFI` | The same value and the same fault as `FFI`, and no `Resume` pushed |

### The array operations (step 5, interpreter 6)

Four of the operations of `stella-base-0.1` are `Base.Array` entries, and they are the first that carrying one out cannot do without reaching the payload of a value ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

| Input | Required outcome |
| --- | --- |
| `length` of an array `unsafeNew` produced | The count it was created with, whatever has been written since. A slot count is immutable, which is why this entry is the one of the four carrying `#observ(none)` |
| `unsafeNew n`, for `n` at zero and above | An array value of that many slots. Two calls with one `n` give two arrays, and nothing the interpreter does merges them |
| `unsafeNew` with a negative count | A fault, and not an array of no slots. A count of zero is an array of no slots and is not an error |
| `unsafeSet i x ys` then `unsafeIndex ys i` | `x`. This is the whole of what the pair is for, and it is the case a machine that copied an array on write would pass every other test while failing |
| `unsafeSet` on an index outside the array | A fault, and the array unchanged |
| `unsafeIndex` on an index outside the array | A fault |
| The array a `PRIM` returned, passed to another `PRIM` and to a foreign | Arrives as the same array, writes through one reaching reads through the other. An array is an opaque value and nothing between the two takes it apart |
| A snapshot of an array value | Stops at it, the way it stops at a continuation or an action. Nothing descends into the payload ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)) |
| A `PAP` over an array operation, completed later | The operation is carried out once, when the last argument arrives, as with any other callee |
| A module naming an operation code this interpreter does not implement | Refused at load, which is unchanged by there being more codes |

**What the end-to-end case is, at this stage, is `Base.Array` and a module written over it**, carried from Core to a value: the manifest supplying an `intrinsic opaque`, four `foreign` declarations, a lowering that makes each a `prim` rather than an `ffi`, a loader resolving them to the interpreter, and a program that allocates, writes every slot, and reads one back. That is the chain this step owes, and it needs no library above it.

**`Data.Array.mapArray` is the end-to-end case over the wider surface**, and closes the group below: its loop tests `i < length xs` with `Base.Int.lt` and advances with `Base.Int.add`, so it is written in Core over the ABI as it stands, needing no library above it.

**A function over an array does not reach the ABI as a higher-order entry.** A `foreign` supplies a first-order leaf, and `mapArray` is Stella over the four above ([Modules](../06-Modules/01-Modules.md)).


**Reading a slot `unsafeNew` left unwritten is not in this table, and nothing replaces it.** It violates the precondition of `unsafeIndex` (D42), so a test executing such a read and asserting anything about the result would be fixing what the specification declines to fix, and would fail a backend that chose differently.

**Nor is the converse testable.** A backend that tracks which slots are written and faults on an unwritten read is **conformant**: the ABI obliges no one to detect a violation and equally forbids no one from doing so, and a program that runs there and nowhere else is exactly the difference an unspecified case admits. So "no initialization bit is kept, and no read consults one" is **not** a conformance property and must not be asserted as one. It is a performance decision of this interpreter — the check would stand on the hot path of the operation a portable array library is built out of — and belongs in the interpreter's own notes rather than in a test.

What is testable around the precondition is only what holds on either side of it: an in-range written read gives the element, an out-of-range read faults, and a program that writes every slot before reading gives the same answer whatever the allocation left.

### The scalar and text operations (step 5, interpreter 6)

The rest of the operations compute from their arguments alone, and each case below is one where a host's own operator gives another answer ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

| Input | Required outcome |
| --- | --- |
| `Base.Int.add maxInt 1`, `Base.Int.mul 65536 65536` | `minInt`, and `0`. Arithmetic wraps, whatever the host does on overflow |
| `Base.Int.mul maxInt maxInt` | `1`. The exact product needs more than 53 bits, so a multiplication through binary64 loses the low ones: JavaScript's `(a * b) | 0` gives `0` here where `Math.imul` gives `1` |
| `Base.Int.quot minInt (-1)`, `Base.Int.rem minInt (-1)` | `minInt`, and `0`. The one overflow division has; a host that traps there checks first |
| `Base.Int.quot 7 (-2)`, `Base.Int.rem (-7) 2` | `-3`, and `-1`. Division truncates towards zero and the remainder takes the dividend's sign; Euclidean `div` and `mod` are `Prelude`'s |
| `Base.Int.quot` or `Base.Int.rem` with a zero divisor | A fault. Not `0`, which would make a mistake a value |
| `Base.Int.toString minInt` | `"-2147483648"`. Negating first overflows, so a conversion that did would print a second minus sign or none |
| `Base.Number.negate 0.0` | `-0.0`. `Base.Number.sub 0.0 0.0` gives `0.0`, which is why the entry exists |
| `Base.Number.eq nan nan`, `Base.Number.eq 0.0 (-0.0)` | `false`, and `true`. The opposite of literal identity in both, which a `switchLit` keeps deciding by |
| `Base.Number.lt` with NaN on either side | `false` |
| `Base.Number.toInt nan`, `Base.Number.toInt 1e10`, `Base.Number.toInt (-2.9)` | `0`, `maxInt`, and `-2`. Saturating, and truncating towards zero. A conversion by `\| 0` gives `1410065408` for the second |
| `Base.Number.floor (-0.5)`, `Base.Number.trunc (-0.5)` | `-1.0`, and `-0.0` |
| `Base.Number.toString 1e21`, `1e20`, `1e-7`, `0.1`, `-0.0` | `"1e+21"`, `"100000000000000000000"`, `"1e-7"`, `"0.1"`, and `"0"` |
| `Base.String.lt "\u{E000}" "😀"` | `true`. By scalar value; JavaScript's `<` over UTF-16 code units says `false` |
| `Base.String.lt "ab" "abc"`, `Base.String.lt "abc" "abc"` | `true`, and `false` |
| `Base.String.slice 1 3 "a😀bc"` | `"😀b"`. The indices count scalar values |
| `Base.String.slice 2 1 s`, or an `end` past the length | A fault, not a clamped result |
| `Base.String.slice (-1) 2 s`, `Base.String.slice 0 (-1) s` | A fault each. A negative index is not counted from the end, as a host's own `slice` counts it |
| `Base.Char.fromCodePoint 0xD800`, `0x110000`, `-1` | A fault each |
| `Base.Char.toCodePoint (Base.Char.fromCodePoint 0x1F600)` | `0x1F600` |
| A hand-written Core `mapArray` over an array `unsafeNew` produced, its loop testing `Base.Int.lt` | Every slot written with the function's result, in index order. The chain this step owes, carried over the whole surface a portable array library is written with |

### The drive loop (step 5, interpreter 8)

Executing an `IO` is the one place the host side enters the interpreter, and it is a second entry point rather than a step of evaluation ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

| Input | Required outcome |
| --- | --- |
| `Base.IO.pure` applied to a value | An `IO` value, and **nothing performed**. Reduction halts on it (D25), and a test that only executed the result would not see the difference |
| `Base.IO.bind` applied to an `IO` and a function | The same: an `IO` value holding both, with the function **not applied** |
| A module declaring either at an arity the ABI does not give it | Refused at load. The interpreter claims the name, so the arity is checked against the ABI's and against nothing else |
| The host's table holding `Base.IO.pure` | Never consulted, and the interpreter's own is what carries it out |
| Executing `Pure v` | `v` |
| Executing `Bind (Pure v) k` | Whatever executing `k v` gives, with `k` applied exactly once |
| A `Bind` whose function is a partial application, or a continuation | Applied the way any unknown call applies one. `k` is a function value, not a closure in particular |
| A left-nested chain of a length that would exhaust the host's call stack | The value, and no stack overflow. **This is the case the loop's own pending stack exists for**, and the one a recursive executor passes every other test while failing |
| A native action answering `Produced` | That value, and no waiting. **Nothing here waits at all**, and nothing asks whether the value is thenable |
| A native action answering `Produced` with a promise, where `k` is `opaque` | That promise, as an ordinary opaque value. It is neither awaited nor rejected, and a program may hold it and pass it back |
| A native action answering `Refused` | A fault. A failure the ABI admits needs no exception to report it |
| A native action that throws where it is performed | A fault, and a different report from a refusal |
| A fault inside an applied continuation | Ends the execution. The pending continuations are discarded and nothing after them runs |
| A continuation returning what is not an `IO`, or a `Bind` over one | An interpreter bug and **not** a fault. The culprit is unknown — a lowering, or an adapter in breach — which is what separates this from an action's breach above |
| An `IO` value that reaches a register | Written there and nothing more. No instruction examines one, and evaluation continues past it |

**Order is what most of these are really about.** A loop that applied a continuation before the action it was bound to, or that ran two actions of a chain in the wrong order, gives the right answer for `Pure` and for a chain of length one. A case asserting the **sequence** — actions that record their order in the host, and a chain long enough to distinguish — is what separates a loop that works from one that happens to.

### The `run` command (step 5, interpreter 7)

What the command adds over the pieces below it is the wiring — reading files, loading them in the order given, finding the entry point, executing it, and turning what came back into an exit status ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

| Input | Required outcome |
| --- | --- |
| Modules in dependency order, with an entry point whose `IO` ends in a value | Exit status `0`, and nothing printed of the value |
| The same modules in an order an import does not admit | Status `1`. **Nothing is sorted**: the command has no import graph, and a wrong order is the front end's mistake to hear about |
| A file that is not a `.dmo`, or one the decoder rejects | Status `1`, reported as the decoding failure it is rather than as a missing module |
| No `--entry`, with a module named `Main` among those given | That module's `main` is the entry point |
| No `--entry`, and no module named `Main` | Status `1`, whatever else was loaded |
| `--entry` naming a module that was not given | Status `1`, naming what was asked for |
| `--entry` naming a module that has no `main` | Status `1`. The global is read from the module's own globals and not through its exports |
| `--entry-global` naming another global of the entry module | That global is the entry point, whatever it is called. This is how an `@[entrypoint]` resolved above the interpreter arrives |
| `--entry-global` naming a global the entry module does not have | Status `1` |
| An argument that could read as a module or as a qualified global, such as `A.B` | Not a case: the two halves are separate options, so nothing has to be disambiguated |
| Two modules declaring `main`, one of them the entry module | Loaded and run. **Nothing is searched across modules**, so the other is not a competitor and not an ambiguity |
| A dependency declaring `main`, where the entry module does not | Status `1`. Nothing looks outside the entry module, which is what keeps a runnable library from being picked up |
| An entry point whose global holds something that is not an `IO` | Status `1`, before anything is executed |
| An entry point whose `IO` produced something other than `Prim.Unit` | Status `0`. The value is discarded, and **requiring it would be a type check performed with no types** |
| A program declaring a foreign the interpreter does not claim | Status `1`. The command assembles no table, and this is the limitation to state rather than to work around |
| A module that faults while initializing | Status `1`: the program never started, which is what a caller must act on |
| A fault while the entry point runs | Status `2`, the fault on standard error |
| An interpreter bug while a module initializes | Status `3` and not `1`. The question asked first is whose the defect is, not when it happened |
| An interpreter bug while the entry point runs | Status `3` likewise |
| The `session` command, started without descriptor 3 | Status `1` and a message. **Not a message and status `0`**: printing a failure while reporting success tells a reader one thing and a shell another |

**Totality is the property worth testing here, not any one row.** Two questions decide the status — was it a bug, and had the entry point begun — and a case for each leaf is what shows nothing falls between them. A command that left one path unclassified would exit `0` on it, which is the worst of the four answers.

**A test of this is a test of a process and not of a function**, so what it asserts is the exit status and the streams. Asserting the value `main` produced would be asserting what the command deliberately does not report.

### The session channel (step 7, division 6)

The channel `steam session` speaks on, before any request of a profile uses it ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

| Input | Required outcome |
| --- | --- |
| A frame handed over one byte at a time, several frames in one read, a frame split inside its length and inside its payload | The same frames. A reader that parses per read passes every test written with whole frames |
| A payload holding text outside ASCII | Its length counted in UTF-8 bytes |
| A length above 16 MiB | The session ends, before any of the payload arrives |
| The channel ending inside a length, or inside a payload | The session ends, told apart from an end between frames |
| An empty payload, one that is not UTF-8, not JSON, or not an object | A protocol error as a notification, and the next frame is read |
| A malformed message whose `id` can be read, and one whose cannot | A protocol error as a response to that `id`, and as a notification |
| A response naming no request awaiting one | A protocol error as a notification |
| A protocol error arriving | Not answered. Two sides answering each other's protocol errors never stop |
| A request made by one side while answering a request of the other: A out, B in, B answered, A answered | Both answered, in that order. A request that read the channel itself would never see B |
| Responses arriving in another order than their requests | Each reaches its own request, by number |
| Numbers used up | The side stops rather than wrapping to a number a late response may still carry |
| A request whose number is not above every number received before, a repeat or a step back | Not run, and answered by a protocol error as a notification. Answering it by its number would answer one request twice |
| A malformed request whose number is fresh, then a well-formed one of the same number | The first answered by that number; the second not run |
| A `ready` naming another protocol or profile, leaving out a required capability, or putting in force one not asked for | Not opened, the process ended |
| A protocol error whose payload has no code and detail | The session ended as misbehaving, not the request refused |
| The channel ending with requests outstanding | Each fails, with the same reason the session ended with |
| A request before the handshake, a second handshake, an unknown kind, a lifecycle request with a payload | A protocol error each, and the session answers the next request |
| A handshake offering and requiring nothing | Opened with no capability in force, and `ping` and `close` answered: the lifecycle requests are the protocol itself |
| A handshake offering capabilities this side does not have | Opened with none of them in force |
| A handshake of another protocol, another profile, or a capability not implemented | `refused`, naming the reason and what is supported, written out before the process ends with status `1` |
| `close` | `closed`, written out before the process ends with status `0` |
| The channel ending without `close` | Status `1` |
| Descriptor 3 not open | Status `1` and a message |
| A process that answers `refused` and ends with another status | A session refused. The exit does not override what arrived |
| A process that ends with status `0` and no `closed`, before or after the handshake | A session failed |
| `closed` followed by a status other than `0` | A session failed |
| A process writing megabytes to standard output and standard error before answering | Answered, and every byte drained. A pipe nobody reads stops the process |
| A character of the output split between two chunks | Whole. A chunk decoded on its own turns each half into a replacement character |
| A process killed, then asked something | The session is lost, not a request refused |
| `steam session` with no manifest, loading modules over `Base` alone | Loaded, each answered by its name |
| The same, loading a module declaring a host foreign | `loadFailed` at `refused`, naming the foreign |
| A manifest given at start that does not read, or names another target | Exit `1` before the handshake |
| A path that does not read, bytes that are not a `.dmo`, implementations unreachable, a module the loader refuses, a global that faults initializing | `loadFailed` at `unreadable`, `notBytecode`, `foreigns`, `refused`, and `initialization`, and the next request answered |
| A load failing after its foreign entries were reached | Nothing of it committed: the module is not there to invoke, and its name loads again |
| Two loads of one module sent without waiting | The first loaded, the second refused, the module initialized once |
| A load and an invoke of what it loads, sent without waiting | The invoke sees the module |
| A guest handing back the token it was given | The same JSON |
| A module not loaded, a global it lacks, a global not holding a function, a guest that faults | `noSuchModule`, `noSuchGlobal`, `notCallable`, `fault`, and the next request answered |
| A guest handing back an `Int`, or an array | `notAToken`, with the class `int`, or `opaque`: an opaque value that is not a token is not one |
| `load` or `invoke` where its capability is not in force, whatever the payload | `capabilityNotInForce` |
| `load` or `invoke` of another payload shape, the capability in force | `payloadInvalid`, not a failed load or invocation |
| `load`, `invoke`, `close`, then `load` and `ping`, sent without waiting | The first two answered, then `closed`; the last two refused as `kindUnexpected` |
| The channel lost with loads queued behind a running one | The running one finishes and nothing queued behind it starts: status `1`, and no queued module initialized |
| A defect of the interpreter while a guest runs, or while a module initializes | The session ends with status `3`, answering nothing more |

### The foreign manifest (step 5, interpreter 6)

The table is assembled from the manifest, complete for a module before that module is loaded (D43, [Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)). A run reaches everything before the first load; a session reaches a module's implementations as that module arrives.

**What a failure costs depends on the mode, and the rows below say what fails rather than what it costs.** A run exits, so everything here is a refusal before the entry point ran and exits `1`. A session does not exit: it answers the refusal and waits for the next input, which is the whole of what a session is for.

| | A failure reaching a module's implementations |
| --- | --- |
| **Run** | status `1`, and the process ends |
| **Session** | the module is refused, the refusal is the answer, and the session takes the next input |

**The manifest itself is the exception, and it fails once.** It is read when the command starts, so a manifest that does not parse, names a `formatVersion` this reader does not implement, or names another target is a failure to start — `1` for a run, and for a session a failure to open rather than a refusal it could answer. **Keeping the two apart matters**: one says this program cannot be run here, the other says this module could not be, and a session that ended on the second would lose everything it held for a reason that concerns one input.

| Input | Required outcome |
| --- | --- |
| A manifest covering the foreigns a program declares | The table holds one entry per foreign, and the program runs |
| No manifest, and a program over `Base` alone | Runs. There is nothing for a manifest to say, so its absence is not an error |
| No manifest, and a program declaring a foreign | Refused where that module loads, **naming the foreign** and not the missing file: the declaration is what was unmet |
| A manifest naming a target that is not this runtime's | Rejected, as a `.dmo` rejects an ABI version it does not hold. Not read past, and not read with unfamiliar fields skipped |
| A manifest of a `formatVersion` this reader does not implement | Rejected likewise |
| A relative `specifier`, with the manifest and the working directory in different places | Resolved against the **manifest's** directory. Running the same manifest from elsewhere reaches the same module |
| A bare `specifier` | Resolved as the host resolves one, starting from the manifest's directory |
| A manifest that is not readable as JSON, or lacks a field this document fixes | Rejected, reported as the manifest being wrong rather than as a foreign being absent |
| A module the manifest names that cannot be reached | Rejected, naming the module and what the target said |
| A module reached that has no export of the foreign's name | Refused, naming the module and the export looked for |
| An export that is reached but is not callable | Refused likewise. A `.dmo` carries no type, so this is the one shape that can be checked |
| A manifest entry for a module nothing declares against | Ignored, and nothing is reached for it |
| A manifest naming one module twice | Rejected. First-wins and last-wins both make the meaning depend on the order of writing |
| A session, given modules one at a time | Reaches for a module's implementations as that module arrives, the set not being known at the start. The table is complete for a module before that module loads, which is the obligation both modes meet |
| A session where a host module cannot be reached, or has no such export | The module is refused and **the session continues**, answering the next input. Not an exit |
| A session opened with a manifest that does not parse, or names another target | A failure to open, and not a refusal it could answer: nothing about it is per-module |
| A host module two Stella modules declare against, in a session | Reached once. An import stays imported |
| A host module whose top-level has an effect, where the load then fails | The effect stands. An import is not undone, and it happened before anything the interpreter could refuse on |
| A `foreigns` signature whose `params` are a different length from the declared arity | Rejected. Both came from the same compiler, so a disagreement is a defect in what produced them |
| An `int` result and a `number` result from the same host number | Wrapped by the kind the signature gives, not by the value. **`Number.isInteger` deciding it would turn `2.0 :: Number` into an `Int` silently** |
| A `unit` result | `Prim.Unit` under the identity the registry assigned, whatever the host returned |
| An `opaque` argument or result | Passed through untouched. There is no host shape to convert an `intrinsic opaque` to, and none is needed |
| An `action` result | The host returns the action, and the boundary wraps it as the `IO` value a program halts on. **A target entry constructs no `IO` value itself** |
| An implementation returning `refuse(reason)` | A fault carrying the reason, reported apart from a throw |
| An action returning `refuse(reason)` | The same |
| A host value that merely has a `then`, at any kind | **Not awaited, and nothing tests for one.** At `opaque` it crosses as the value; at any other kind it is a host-contract fault by that kind, as any other object would be |
| An implementation returning a promise where the result is `opaque` | That promise, passed through. The boundary has no waiting to offer and does not pretend to |
| A marker an implementation built without the helper | Not recognised. The brand is the helper's own and cannot be obtained from outside it |
| An implementation that only returns values | Imports nothing |
| A manifest naming a `kind` this reader does not know | Rejected, as an unknown `formatVersion` is. Widening the kinds is what a later version does |
| An `int` result that is not a whole number, or outside an int32 | A host-contract fault naming the entry, and **not** a value written into a register |
| A `char` result of more than one scalar value, or half a surrogate pair | The same |
| A `string` result holding an unpaired surrogate | The same |
| An `{ "action": k }` result that is not callable | The same |
| A `refuse` built by a second copy of the helper, where the result is a scalar | Not read as a refusal. The brand is unknown, so it is a host object where a number was owed, and the check by the kind ends the run |
| The same, where the result is `unit` | **Discarded, and nothing catches it.** Nothing of the host value is read for a `unit` result, so the refusal becomes a success. `IO Unit` is the frequent shape — a console entry — which makes this the principal case of the limit rather than a corner of it |
| The same, where the result is `opaque` | **Passes as the value, and nothing catches it.** Both this and the row above are fixed as cases so that the limit is not mistaken for an oversight |
| A manifest entry for a name the ABI manifest fixes | Never consulted. The interpreter is selected by name, so the entry is dead rather than an override |
| A foreign reached through a manifest, at any arity | The declared arity is adopted, and the refusal for a **supplied** arity that contradicts a declaration cannot fire: nothing on this path supplies one. **A case asserting that it does would be asserting a check that is not there** |

**Coverage is checked twice and the two are not redundant.** A build that omitted a package's mapping is caught where the source is, with the module and the declaration to hand; the loader catches what actually reached it, a `.dmo` being able to arrive from anywhere and a manifest being able to go stale. A test of one is not a test of the other.

**What must not be tested is the payload's meaning.** What a `specifier` is belongs to the target, and a case asserting how one is resolved would be fixing in the compiler what the format exists to keep out of it. **A signature is the other way round**: it is target-independent, derived from a type the compiler holds, and is exactly what a case may assert.

### Declaring a foreign (step 7, and step 3 for the check)

Only what can cross the boundary may be declared (D44), and the declaration is the only place with a type to judge it by ([Modules](../06-Modules/01-Modules.md)).

| Input | Required outcome |
| --- | --- |
| A `foreign` over scalars | Accepted |
| One whose result is `IO τ` | Accepted. This is what a target entry constructing a native action is |
| One over an `intrinsic opaque` | Accepted, in argument and result alike |
| One taking or returning a data type, a record, or a variant | **Refused at the declaration**, naming the type, since nothing downstream holds one to refuse it later |
| One taking a function | Refused likewise. A `δ_f` may carry a function value but may not apply one, so what a host would do with it is not a question the boundary has an answer to |
| `IO τ` in an **argument** | Refused. Only a result may be an action; an argument of one would be a reified computation the host was handed and could not run |
| The signature the compiler derives | The kinds of the declared type, in order, and a `params` length equal to the arity

### Kind and type unification (step 7, division 2)

These need no surface language: an equation is written by hand, as a Core module is in step 4 ([Elaboration](../02-Surface-Language/01-Elaboration.md)).

| Input | Required outcome |
| --- | --- |
| `?k ≡ Effect`, where `?k` is required quantifiable | Rejected. Kind equality solves it, so what refuses it is the requirement the metavariable carries |
| `?k := ?k1 -> ?k2` for a quantifiable `?k`, then `?k2 := Row Type` | Rejected at the second assignment. The requirement propagates into the arrow, and only `Row Type` arriving decides it |
| `?j ≡ ?k`, each carrying a requirement | Both survive. A requirement reaching an unsolved kind attaches itself there, so the two sets merge |
| `forall a. Pair a a ≡ forall b. Pair b b` | Accepted. The correspondence decides it and neither side is renamed |
| `forall a. forall a. Pair a a` against a right-hand side using its **outer** binder | Rejected. A variable is read through the innermost entry of the correspondence mentioning it |
| `forall a. ?m ≡ forall b. b` | Refused with a mismatch of its own rather than the structural one. The equation fails either way; a diagnostic saying the two types disagree misdescribes an equation this judgement declines to solve |
| `forall a. ?m ≡ forall b. a`, where the right-hand `a` is free | Refused likewise. A name the two sides share is not a correspondence, and a difference of name sets cannot tell the two apart |
| `forall r. Record ( a : A \| r ) ≡ forall s. Record ( a : A \| s )` | **Accepted.** A rigid tail cancels the tail it corresponds to rather than the one it shares a name with; comparing the tails as names rejects an ordinary row-polymorphic scheme |
| `{ a : A \| ?r } ≡ { a : B \| ?s }` | Rejected. The tails solve and the payload equation `A ≡ B` is what fails; leaving the equations undischarged accepts it |
| A `Row Effect` element whose two arguments stand at different kinds | Each payload equation stands at a kind of its own. One metavariable shared between them identifies the two |
| `?α : Row Type` met at kind `Type` | Rejected as a kind mismatch. Kind equality decides before any row obligation is read |
| `?α : Type ≡ Int` | **Accepted.** Nothing about a row is read of a solution that is not one |
| A metavariable an obligation names, solved to a type that is not a row | Rejected where that obligation is re-decided, its subject zonking to something with no normal form. Only a row metavariable is named by a row constraint, so this is an invariant of the solver rather than a property of the program |
| `?r ≡ ()` where `?r : Row Effect` and the carried kind is `Row Type` | Rejected. An empty row gives its element kind away nowhere, so a flexible root is what the kind is read against |
| A closed comparison that constrains none of the kind metavariables it created | Leaves none of them in `Ψ`. Each belongs to the equation rather than to the solver's state |
| A kind metavariable that stood in `Ψ` before the equation ran | Left alone, whether or not the equation constrained it |

### The transaction and the scheduler (step 7, division 3)

**The bookkeeping is separable from the transaction and is written first.** The three tables, the envelope, and the context a site snapshots need neither a checkpoint nor anything that runs a job, so what they promise can be settled before either exists ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)).

What the tables promise of one another is checked rather than assumed, each of these being a way for a job to run twice or never.

```text
id ∈ blocked[?α]  ⟺  ?α ∈ pending[id].awaiting     both directions
an identifier on the ready queue awaits nothing
an identifier either queue holds is one pending holds
no identifier is twice on the ready queue
no identifier is at once ready and blocked
```

**Both directions of the first are needed.** The table and the set each name what the other is read through: a job registered under a metavariable its own set does not name is never unregistered, and one awaiting a metavariable it is registered under nowhere is never woken by that assignment.

| Input | Required outcome |
| --- | --- |
| A job registered under `?a` and `?b`, with `?a` assigned | On the ready queue once, and registered under `?b` no longer |
| The same job, with `?b` then assigned in the same attempt | Still once on the queue. A registration left standing enqueues a job that is already on it |
| A job postponing a second time on `?b` alone | Registered under `?b` and nothing else, the set being assigned rather than added to |
| A job woken and not yet postponed again | Awaits nothing, which is what a report at quiescence reads |
| One assignment waking several jobs | Queued in the order they were created |
| A job completed while registered | Held by no table afterwards |
| A job woken, then taken from the ready queue, then attempted | Attempted as any other job is. Just after `takeReady` is one of the two points at which a job may be attempted, the other being just after `create` |
| An attempt of a job still on the ready queue, or still registered under a metavariable | A defect, and the job is not run. The first would run it again when the loop takes it, and the second would register it twice |
| A job submitted and attempted at once | No fuel spent. Fuel bounds the scheduler's retries, and a first attempt is none |
| A job created inside an attempt | Queued for its first attempt and not attempted there, which would open an attempt inside another. Taken from the queue, that attempt spends no fuel either |
| A synthesis job and the term metavariable it fills | Created by one operation: the metavariable exists, stands at the goal's type, and is scoped to the site's context. A rollback removes the two together |
| A synthesis job whose target is absent, solved, at another type once zonked, or scoped wider than its site | A defect of the host, found before the synthesizer runs, and the attempt rolled back. A target scoped narrower than its site passes: one standing in another solution is narrowed with it |
| A type a view takes apart | Every part is a handle whose kind evidence the read-only kinding judgement gave, under the kind variables and type variables the site or the catalog scheme binds, and the binders the view descended under |
| A kind variable no site or scheme binds, standing as a binder's kind or a constructor's kind argument | Refused as unbound, not given a kind. A kind-polymorphic scheme is kinded under the kind variables it declares and under no others |
| A negative `PositionKey`, as an element's key or in a constraint | Refused. Every key is judged by one rule, whichever it keys |
| A goal observed through a handle to a goal other than the one running, or where no goal runs | A defect of the host. The scope a goal's type is read under is the running goal's site |
| The empty row, where its place fixes a row kind, and where nothing does | That row kind, and `AnyRow`: `()` stands at both row kinds and neither is chosen for it |
| A kind metavariable reachable from what a synthesizer observes | A defect of the host. A synthesizer can neither name one nor wait on it |
| An observation | Changes the arena and the generation and nothing else: no metavariable, obligation, job, or fuel |
| A type built in a child build scope, given to a builder in its parent, or in a sibling | A defect of the synthesizer. Two binders alike in name and kind are still two binders, and only the scope a type was built in says which one it mentions |
| A type built in the root, or observed at the site, given to a builder in a child scope | Accepted. A scope may use whatever its ancestors may |
| A part a view takes of a catalog scheme — its head, an argument, a row's payload | In no build scope, as the scheme is, until `instantiateScheme` opens the scheme. A part inheriting the root's scope would let a scheme's variables reach a type without being instantiated |
| The body a view takes of a `forall` or of a constraint | In no build scope. Its binder or its assumption is not the scope's, and `instantiateForall` is how a `forall` body is reached |
| Two binders opened with one hint | Two names. The host draws each from a supply a rollback restores, so a re-run attempt draws the same names |
| A binder closed in a scope other than the one it was opened in | A defect of the synthesizer, and not a `forall` over whatever the binder happens to be named |
| `instantiateForall` over a body one of whose binders the argument mentions free | That binder renamed first. A substitution that walked under it would capture the argument's variable |
| `instantiateForall` at an argument that is a metavariable solved to a variable one of the body's binders is named | That binder renamed. Read before zonking, the argument mentions nothing, no binder is renamed, and the zonk of the result is what captures |
| `instantiateForall` over a body holding an unsolved metavariable whose scope has the binder | Postponed on that metavariable. The substitution stops at it, and its later solution could mention a binder the result no longer has |
| `instantiateForall` at an argument holding an unsolved metavariable whose scope has a binder of the body | Postponed on that metavariable. Its later solution could be captured by a binder nothing renamed |
| `instantiateScheme` of a scheme mentioning a type or kind variable it does not declare, the caller's scope binding one of that name | A defect of the host. Judged only in the caller's scope, after substitution, the caller's variable would vouch for the scheme's |
| `extendRow` over a row already carrying the key, or over a rigid tail the scope does not prove lacks it | A failure, and the handle and the obligation are both gone after a `transact`. Kinding alone admits the row, sharpness being an entailment and not a shape |
| `extendRow` over a flexible tail, the tail then solved to a row carrying the key | The assignment fails. The requirement was introduced with the row and watches the tail |
| `unionRow` of rows sharing a key, or of a row and a rigid tail not proved to lack its keys | A failure |
| A row sharp only under `k ∉ r`, built inside `openConstraint (k ∉ r)` | Built, and usable at the root only once `closeConstraint` has wrapped it in the constraint. The requirement is decided against the build scope's context, which holds the assumption; the site's does not |
| An assignment breaking a constraint opened and not yet closed, and the same once it is closed | Admitted, and refused. The assumption is held from where it is closed, which is where the constrained type exists |
| Closing a constraint that cannot hold | A failure there |
| A synthesizer that opens a binder and ends in success without closing it | A defect, and nothing commits. What was built under the binder — an obligation proved from its assumption, a job — would otherwise commit without the type carrying it |
| The same, where the attempt is run by `runAttempt` directly rather than through a job | The same defect. The check is the attempt root's, not a runner's, so no way of running an attempt commits an open binder |
| A binder closed while one opened inside its body is still open, the inner one then closed | A defect at the outer close, for every pairing of `forall` and constraint. Closing both would leave the ledger empty, and what the inner one built would commit after the type carrying the outer one was fixed |
| Nested binders closed inside out, and siblings closed in either order | Committed |
| A binder closed twice, or a `forall` binder closed as a constraint or the reverse | A defect of the synthesizer |
| A binder opened by a candidate a `transact` discarded | Not held open. The ledger is part of what an attempt owns |
| A region element given to `extendRow` | Refused. Only the handler owning a region introduces one |
| A row view's flexible tail, taken from a row in no build scope | Its `Type` is in no build scope either. A `Meta` turned back into a type without the row's scope would launder it into one |
| `freshMetaType` in a `forall` body's scope, and in the root | Scoped to the body's variables, binder included, and to the site's. The scope is the build scope's; a caller has none to state |
| A metavariable created in the root, equated in a child scope with the child's binder | A failure. The solution would mention a variable its scope does not hold |
| `freshMetaType` at `Effect`, or at an arrow whose final result is a row such as `Type -> Row Type` | Refused. A metavariable a synthesizer holds stands where a type variable would |
| `unify` of two handles whose exact kinds differ, or of a row with a type | A defect of the synthesizer, and nothing unified. Every kind a handle holds is settled, so it is a misuse and not a candidate that does not fit |
| `unify` of two empty rows, and of an empty row with a row metavariable | Equated, at `Row Type` and at the metavariable's kind. The first choice is invisible, neither side having an element or a tail |
| `unify` given a `forall` body, or a type from a sibling scope | Refused. Equated with a site variable of the same name, the body's variable would be taken for it |
| `unify` breaking an obligation, inside a `transact` | Caught as a failure, and the metavariable is unsolved afterwards |
| `entails` of `k ∉ ?t` with `?t` flexible, then with `?t` solved to `()` | `false`, and then `true`. A flexible tail is never a fact |
| `entails` of `k ∉ r` at the root, and inside `openConstraint (k ∉ r)` | `false`, and `true`. The assumptions are the build scope's |
| `entails` of a constraint the facts refute, or under assumptions that contradict each other | `false`, and not a defect. Only a row with no normal form is one |
| `entails` | Changes nothing: no metavariable, and no obligation |
| `require` of a constraint already broken, or unproved at the scope | A failure where it is introduced |
| `subgoal` in a `forall` body's scope | A job whose site binds the body's variable, queued for a first attempt, and an `Expr` built in that scope whose claimed type is built there too |
| `subgoal` at a type not standing at `Type`, or at one the scope may not use | A defect of the synthesizer |
| `subgoal` inside a `transact` that fails | The job and its target are both gone |
| `localVariable` of a name the scope does not bind | Refused. Only the scope's bindings can be referred to by name, so none is made up |
| `globalRef` of an absent entry, at the wrong number of kinds, at a kind that is not quantifiable, or of a scheme mentioning a variable it does not declare | What `instantiateScheme` does for each, by the one procedure the two share |
| A leaf's `typeOf` | The type the host claimed it at, with the scope it was built in and the variables that scope binds |
| A term built in a child scope, used in the child's descendant, in its parent, and in its sibling | Used, refused, and refused. A term built in no build scope is refused everywhere |
| A fresh name whose first candidate the context already binds, for a value and for a type variable | The next number, and the skipped one is spent. `#` keeps a name only from what an author wrote |
| A fresh name drawn inside a `transact` that fails, and drawn again | The same name. The supply is part of what an attempt owns |
| A lambda's variable given to `termApply`, to `openLet`, or as the body of a sibling lambda, outside the lambda | Refused. A term built in a body's scope stays under its binder, through every builder that takes a term |
| A lambda closed with a row built in its body's scope, or with a row at `Row Type` | Refused. The row is the synthesizer's to give, from the scope the lambda was opened in, at `Row Effect` |
| `termApply` of a function whose claim is `?f τ`, or `?m`, with the metavariable unsolved | Postponed on `?f`, or on `?m`. A spine headed by a metavariable may become a function type |
| `termApply` of a function whose claim is `?g ()` with `?g : Row Type -> Type`, or a metavariable applied to four arguments | A defect of the synthesizer, and nothing waited on. No solution of the head makes the spine a function type, so a job registered under it would wait forever |
| `termApply` of a function claimed at `?a -{()}-> Int` | Claimed at `Int`, without waiting. The head is `Function` already, and what the arrow holds decides nothing about the shape |
| `termApply` of a term claimed at `Int` | A defect of the synthesizer. No solution makes it a function |
| `termApply` of `λ(x : Int). x` to a `Boolean` literal | Built, claimed at `Int`, and refused by the Core type checker. A derived claim reads the syntax and proves nothing |
| `typeApply` of a type abstraction at a type of another kind, and of a term claimed at no `forall` | Refused |
| `constraintApply` of a term claimed at `k ∉ r => τ`, at the root and inside `openConstraint (k ∉ r)` | A failure, and claimed at `τ`. The requirement is introduced with the term, against the scope's assumptions |
| A constraint abstraction closed over a constraint that cannot hold | A failure there |
| A `letrec` of two names whose right-hand sides refer to each other, closed with one right-hand side, or with one built outside the group | Built; refused for the count; refused for the scope |
| A binder of any sort closed by the operation for another, or left open when the attempt succeeds | A defect of the synthesizer |
| `λ(x#0 : Int). x#0` built by the kernel and handed to the Core type checker | Accepted. The names the host binds pass it |
| A `letjoin` whose definition jumps to itself, and whose body jumps to it | Built, and accepted by the Core type checker. The join point is in both scopes |
| A `letjoin` closed with a parameter as its body, or with the body and the definition exchanged | Refused. The definition and the continuation are sibling scopes, the parameters bound in the first alone |
| A `jump` outside its `letjoin`, or with another number of arguments | Refused |
| A `jump` inside a `λ`, a `Λ(a)`, or a `Λ(_ : C)` in the continuation, and inside a `let` or a type's `forall` there | Refused, and built. Only an abstraction empties `Δ`: `Λ(a)` binds what `forall` does and empties it where the type's binder does not |
| A term that jumps, given to `closeLambda` as its body, or to `termApply` inside a `λ` | Refused. It is visible there, built in an ancestor, and would carry the jump under the abstraction |
| The same term as a `let`'s body in the continuation | Built. A `let` inherits `Δ` |
| Two join points opened one inside the other | `j#0` and `j#1`, from a supply apart from values' |
| A join point opened inside a `transact` that fails, and opened again | `j#0` both times. The supply is part of what an attempt owns |
| A switch on `Nil` and `Cons` over an occurrence at `List Int` | `Cons`'s fields at `Int` and `List Int`: the declaration's fields, the kind variables and then the parameters instantiated, read from the session's constructor table and not recovered from the constructor's scheme |
| A switch naming a constructor the table lacks, constructors of two data types, or one constructor twice | A defect of the synthesizer |
| A switch naming what the catalog calls a constructor and the table lacks | A defect of the host. The two come from one signature |
| A switch on constructors over an occurrence at `?f Int`, `?f : Type -> Type`; at `?g ()`, `?g : Row Type -> Type`; and at `Int` | Postponed on `?f`; refused; refused. Only a head that could become the data type is waited on |
| A `case` over a list, taken apart by the kernel under a lambda | Claimed at its first leaf's type, and accepted by the Core type checker |
| A switch whose first branch reaches no leaf | Reaches the type of the first branch that does. A `case` over a tree reaching none is refused without a result type and claimed at it with one |
| A guard whose first tree reaches no leaf | Reaches what its second does |
| An occurrence of `Cons`'s branch read in `Nil`'s, and an occurrence of an enclosing `case` read in an inner one | Refused, both. An occurrence is in `Ω` only under the dispatch that established it, and `Ω` is the `case`'s own |
| A tree node asked for in a scope standing in no tree | Refused |
| `recordField` at a key the record's row carries, at one it does not, and on a list | The payload's type; refused; refused |
| A switch on the key `n` of `Variant ( n : Int, m : Int )` with a default | The payload at `Int`, and the default's occurrence at `Variant ( m : Int )`. The residual keeps the tails and is not waited on |
| A switch on a key a variant lacks, where its tail is flexible, closed, or rigid | Postponed on the tail; refused; refused. A rigid tail says nothing of what it carries |
| A switch closed with fewer trees than branches, without the default a switch on literals has, or with one branch's tree in another's place | Refused |
| A `case` left open when the attempt succeeds, or a switch closed as a `bind` | A defect of the synthesizer |
| A field `forall b. a` of `data Wrap a b`, over an occurrence at `Wrap b Int` where `b` is the site's | `forall b#0. b`. The substitution is simultaneous and renames the field's binder, which is named like a parameter and would capture what the other parameter is replaced by |
| A tree of an enclosing `case`, given as an inner `case`'s tree or to a guard in it | Refused. Its occurrences are paths from the enclosing `case`'s scrutinees |
| A switch on the constructor of `data Same (a : k) (b : k)` over `?h Int Int`, with `?h : Type -> Type -> Type`, and with `?h : Type -> Row Type -> Type` | Postponed on `?h`, and refused. A kind variable of the data type stands for one kind wherever it occurs |
| `extend n 1 {}`, and `extend` of a key the rest carries, or over a rigid tail not proved to lack it | `Record ( n : Int )`; a failure; a failure. The requirement comes with the term |
| `select`, `restrict`, and `update` at a key of a closed record | The field's type; the record without it; the record with it replaced, its type free to change. One procedure reads the row for all three |
| `select` at a key a record lacks, its tail flexible, closed, or rigid | Postponed on the tail; refused; refused |
| `select`, `recordField`, or a switch on keys at `PositionKey (-1)`, over a row with a flexible tail | Refused, and not waited on. No solution puts an ill-formed key in a row |
| `merge` of records apart, and of records sharing a key | Claimed at the union; a failure |
| `inject n 1`, then `weaken m [Boolean]` of it, and `weaken n` of it | `Variant ( n : Int )`, with no row given; `Variant ( m : Boolean, n : Int )`; a failure |
| `absurd [Int]` of the empty variant, and of an `Int` | `Int`; refused. That the variant is empty is the Core type checker's |
| `openEff` of a pure function at `()`, at a row of `Row Type`, and of an `Int` | The arrow at `() ⊎ ()`; refused; refused |
| Records and variants the kernel built, declared at what they are claimed at | Accepted by the Core type checker |
| `perform` of `State.get` at the element `State Int`, unlabelled and labelled | Claimed at `Int`, the effect's parameter instantiated. The element is an annotation; that it is in the ambient row is the Core type checker's |
| `perform` of `Poly.ident [Boolean]` | Claimed at `Boolean`, the operation's own binder instantiated with the effect's parameters, simultaneously |
| `perform` of an operation the effect lacks, with type arguments it does not bind, at a key that does not make the element, or at an ill-kinded element | Refused |
| `perform` of an effect the kinding environment declares and the effect table lacks | A defect of the host. The two come from one signature |
| A handler owning cells, closed with a body reading a cell | Claimed at its answer; the region variable fresh; the return clause binding the computation's result |
| A `full` clause of a handler without cells | Its continuation at `τ -{ρ}-> β`, the resumption into the answer over the clauses' row |
| A handler naming an operation twice, or missing one, or whose computation jumps to a join point | Refused |
| A handler owning cells over a residual row `e` nothing proves lacks a region | A failure. `RegionKey ∉ ρ` is required with the term |
| A handler closed with fewer bodies than clauses, fewer initial values than cells, or the return clause's variable as an operation clause's body | Refused |
| `readCell` and `writeCell` in an operation clause of a handler owning the cell, and inside a lambda there | Built: the cell's type, and `Unit`. A region is lexical and not reset by an abstraction |
| `readCell` at the root, in the return clause, or at a key the layout lacks | Refused. The return clause stands outside the region |
| A goal asked for in an operation clause of a handler owning cells, attempted with a runner reading a cell at its root | Committed. The goal carries its region, and the attempt's root stands in it |
| A term metavariable created outside any region, assigned `readCell n` | A failure: the solution reads a cell the metavariable's region does not hold |
| `readCell n` built in a clause of a handler owning `n`, placed in the same clause, and in a clause of a handler inside it that owns an `n` too | Built, and refused. The inner handler's `n` would capture it |
| A goal asked for in the outer clause, placed in the inner one | Refused. A solution may read a cell of the region it was asked for in |
| A literal built in the outer clause, and a handler there reading only its own cells, placed in the inner one | Built, both. Neither depends on a region |
| A handler built in the outer clause whose own clause is a goal asked for there, unsolved, and solved to `readCell n`, placed in the inner one | Built, both. The goal is filled in the handler's own region, so neither depends on the outer one, and the scheduler's progress changes nothing |
| A handler owning cells, built by the kernel and declared at its answer | Accepted by the Core type checker |
| Every form of Core⁺ — term, decision tree, occurrence, and operation clause — built by the kernel's requests alone | Every form reached but `EHole`, which is the Surface elaborator's alone; `ETermMeta` by `subgoal` only. The forms are named by a function matching every constructor, so a new one is placed before anything compiles |
| The target of a goal not yet run, crossing the boundary | Reported as a residue |
| A kernel-built term committed as a goal's solution, zonked, crossed, and walked for references | Accepted by the Core type checker, its references the committed term's |
| The same, after a candidate that opened a lambda and assigned the target a reference to another global, then failed inside a `transact` | The same term, and none of the candidate's references. The assignment, the names, and the handles went with the rollback |
| `(λ(x : Int). x) true`, kernel-built and claimed at the goal's `Int`, committed as its solution | Committed, and refused by the Core type checker. A derived claim reads the syntax and proves nothing |
| A `throw` of text, a type, a term, and a name | A failure holding the message frozen — the type zonked with its kind evidence, the term with its claim, the text as written — and the goal it is about: its origin, its job, its synthesizer, and its expected type |
| A `throw` or a `warn` where the frame runs no goal | A defect of the host. A report is a synthesizer's |
| A message naming a type observed under a binder, and one naming a scope as a type | Frozen, and refused. A message's handle is shown and not built with, so only its validity and its class are checked |
| A `warn` of a metavariable's type, the metavariable solved later in the attempt | The report still shows the metavariable. It was frozen where it was made |
| A `warn` inside a `transact` that fails, and one after it | Only the second is reported |
| A `warn` in an attempt that postpones, fails, or breaks | Not kept |
| A goal that warns and postpones, woken, then warns and commits | Its warning reported once, by the run that commits |
| A loop's report, and the state after it | The warnings committed, drained into the report and out of the state. A driver reads them once |
| A job submitted that warns and commits, then one submitted that fails, or one that breaks | The second submission stops with the report a loop would make, the first job's warning drained into it and out of the state. No loop has to run to read it |
| A request inside a transaction, then the transaction committed and the attempt finished | Committed, with what the request did and the warning it raised. A committed transaction keeps its work |
| A failure inside a transaction, after a handle issued outside it and one issued inside it | Answered `CandidateFailed`, naming that transaction, which is closed; its assignment and its warning are gone, the outer handle still resolves, and the inner one is stale. The synthesizer goes on outside it |
| A failure inside two nested transactions | Only the inner one is closed, and the outer one commits after. Rolling back further discards a candidate the synthesizer did not give up |
| A transaction opened after one a failure closed | A token never issued before |
| A failure outside every transaction | Rejected, rolled back, and the job gone |
| A metavariable solved inside a transaction, then postponed on | Registered under it, the attempt rolled back past the transaction to its checkpoint. Refusing a metavariable because it is solved when the request is made rejects a postponement its rollback makes sound |
| A `postpone` on a metavariable solved before the attempt | A defect |
| A defect inside a transaction | Rolled back to the attempt's checkpoint, past the transaction |
| An attempt of a job still queued, or of one whose target is solved | Not opened, and the state left as it was |
| An attempt opened again after one rolled back | Another conversation identifier. One restored with the rollback lets a late request of the first attempt name the second |
| A request naming another conversation, or a transaction a failure has closed | A defect of the synthesizer |
| A commit with no transaction open | A defect of its own, and not a mismatch: nothing is named that differs from what the host holds |
| An attempt opened where every conversation identifier has been issued | A defect, and the state left as it was. Wrapping around issues an identifier a late request may still carry |
| A transaction opened where its conversation has issued every token | A defect, rolled back to the attempt's checkpoint, for the same reason |
| Every public kernel operation, called once as a host script's operation | Each makes the request of its own name, and the requests are the 77 operations. The requests are named by a function matching every constructor, so a request added does not compile until it is named |
| Every operation, given an answer of every shape | It takes back the one shape `expectedAnswerShape` gives its request, and none for `throw` and `postpone`. The table and the operations agree by test, and the interpreter holds every answer to the table, on the wire as for a script |
| A script taking back an answer of another shape | A defect of the host, and the attempt rolled back |
| A synthesizer reading its goal's type through the Goal handle it is given, and returning a literal built at the root | Committed, the literal assigned to the goal's target and the job gone |
| A goal at `?a`, and a result claimed at `Int` | `?a := Int`, and the result assigned. The claim is unified before the term is assigned |
| A result whose claim the goal's type refutes | Rejected, the target unassigned and the job gone |
| A goal at `Record (?r ∪ ?s)`, and a result at `Record (n : Int)` | Registered under `?r` and `?s`, and nothing assigned. The claim's equation waits, and acceptance waits with it |
| A job standing where `x : Int` is bound, its target where nothing is, its goal at `?a`, and a result `x` | Rejected at the assignment, and `?a` unsolved: the claim's equation is rolled back with the attempt |
| A result built in a lambda's body, the lambda closed | A defect of the synthesizer, and nothing assigned |
| A candidate that warns and throws inside `transact`, then a warning and a result after it | `Left` with the failure, only the second warning kept, and the result committed |
| A failure inside two nested `transact`s | Caught by the inner one alone; the outer one commits |
| A synthesizer postponing on the metavariable its goal's type shows | Registered under it |
| A synthesizer postponing on nothing | A defect |
| The same attempt driven by commands — a transaction begun, the root and a literal requested, the transaction committed, the attempt finished | Each command answered in its shape, and the literal committed as the goal's solution |
| A failure requested inside a transaction by command | Answered with the failure and the transaction it closed |
| A synthesizer run on an equality job | A defect: the job has no goal to give it |
| One synthesizer run twice from one state | The same trace, outcome, and final state |
| The commands a traced attempt recorded, with their envelopes, sent again from the state it started from | The same trace, outcome, and final state, identifiers and handles included. The script and the commands are answered by one dispatcher |
| An attempt run where the session does not trace | Nothing recorded |
| A candidate that warns and fails inside `transact`, then a result | Every command recorded, the undone among them: the candidate's rolled back, the rest kept |
| A transaction committed inside one that then fails | Rolled back, with the one around it |
| An attempt that postpones | Every event rolled back, and the attempt's end recording what it waits on |
| A conversation driven by commands and not yet finished | Every event pending |
| An attempt of a job still queued | Recorded as not opened, naming no conversation, and not run |
| A misuse after a failed candidate | The conversation ends with the defect, told apart from the failure answered before it |
| A goal that postpones on its type's metavariable, the host solving it between two conversations, and the retry | The retry sends the same commands as the first attempt up to the first reply that differs, compared with handles renamed by first appearance: the reply to `viewType` shows the metavariable, then the constructor, and the commands part after it. What is reproduced is that common prefix, not the first attempt's commands entire |
| The same goal carried on: after the retry, a candidate its type refutes, then `Main.one` | Committed, zonked, crossed, and accepted by the Core type checker, its only reference `Main.one` |
| A synthesis submitted from outside every attempt, its synthesizer, held in the registry — a `Map` from the goal's name to a host script — answering | Committed on submission, the target assigned and the job gone |
| The same, the synthesizer failing | The submission stops with the failure, the target held unsolved, and no job left in any table |
| A queued goal, run by the loop with the registry | Completed, the target assigned |
| A queued goal whose synthesizer fails | The loop stops with the failure, no job left in any table, and the target held unsolved |
| A goal whose synthesizer misuses the kernel, queued before one that would answer | The loop stops with the defect; the second job is still first on the ready queue, and both targets are held unsolved |
| A goal at `?a` that waits while `?a` is unsolved, then an equation `?a ≡ Int` submitted through the same attempter, then the loop again | Blocked, then the equation committed by the host's runner, then Completed with the target assigned |
| A synthesizer asking a subgoal of another in the registry | The loop runs the subgoal with the same registry, and the goal that asked zonks to its answer |
| The same, the asking attempt then failing | The subgoal is rolled back with it: no job is left in any table, on a queue or off one |
| An attempt of a job the scheduler does not hold, in a session that traces | Reported by the host's runner, and nothing traced: a job whose kind is not known is not a synthesis attempt |
| A goal naming a synthesizer the registry does not hold | A defect of the session. The trace holds the attempt opened and abandoned, and no command |
| The same goal, its target solved before it is attempted | The malformed target is reported, and the trace holds the attempt as not opened: the target is checked before the synthesizer is resolved |
| `λ(x : Int). ?m`, `?m` a goal at `Int` asked where `x : Int` is bound, queued, and answered by the reference synthesizer — a host script using the facade alone — run by the loop | Completed, and `?m` zonks to `x`, carrying the hole's annotation |
| The same with `x : Boolean`, the synthesizer given the monomorphic global `Main.one : Int` | `?m` zonks to `Main.one`, carrying the hole's annotation. A global is referred to only once its scheme has no kind variable to instantiate |
| Two goals queued together, each where a different variable is bound at `Int` | Each zonks to its own site's variable: a goal is answered from the site it was created at, however late the loop runs it |
| A goal at `Boolean` where nothing is bound, the synthesizer given only `Main.one` | The loop stops with the synthesizer's failure, and the hole is left unsolved. Types are compared as constructor views only, a candidate test and not type equality |
| A goal at `?a`, where `x : Int` is bound, queued and run by the loop, its synthesizer building a metavariable, a constraint on it that stays open, a term, and a warning before it waits on `?a` | Blocked, fuel untouched. Measured against the attempt's checkpoint — nothing written, no handle, no warning before it — `Ψ`, the obligations, the name supplies, and the open binders are as they were; nothing written, no handle, no warning, and none reported; the job is the one created, awaiting `?a` alone, off the ready queue; the target unsolved. The generation and conversation counters have moved, and the session has not |
| The host submits `?a ≡ Int` through the same attempter | Committed, fuel untouched, and the goal on the ready queue for a retry |
| The loop run again | Completed, one unit of fuel spent, `?m` zonks to `x` from the same site, and no job is left. The synthesizer builds nothing while it answers |
| The constraint the waiting synthesizer requires, requested alone by command | It stays in the obligation store: a constraint proved at once would not show what the rollback discards |
| A guest keeping the Type handle a waiting attempt was given, and presenting it when the goal is retried | A defect naming the handle as stale |
| The fixture's declarations — `one : Int`; `cand0 : forall k. forall (t : k). Int`, `cand1 : Record (a : Int, z : Boolean)`, and `cand2 : Record (a : Boolean, z : Int)` marked `candidate`; and `decoy : Int` marked by another key — declared to the Core checker | Accepted, each at the scheme the catalog gives it |
| `declsWithAttr "candidate"`, asked in an attempt that then waits, and again in the retry | `[cand0, cand1, cand2]` both times: ascending, by the key alone, the decoy left out |
| A goal at `Record (a : ?t, z : Int)`, searched by the reference synthesizer — each candidate read and, where it has no kind variable, referred to and its claim unified with the goal's type, all inside a transaction of its own — `cand1` building a metavariable, an open constraint, and a warning, and equating the goal's field `a` with `Int` on its own, before its claim fails at `z` | Completed with `cand2`. A failed equation assigns nothing, so the assignment is made by an equation that succeeds; the rollback takes `?t := Int` back, so `?t` is `Boolean`. No warning is reported, `Ψ` holds no metavariable it did not hold before, and the obligations are as they were |
| The same work done in `cand2`, which fits | Kept: the warning is reported, and the obligation stays. The case before is not passing for want of work done |
| The same assignment made in `cand2` | No candidate fits, and `?t` is unsolved: the case before is not passing for want of the assignment made |
| `cand0`, first and with a kind variable, marked to build what a candidate can leave | Passed over with nothing done for it: no warning, no metavariable, no obligation, and `cand2` answers |
| A goal at `Record (?r ∪ ?s)`, whose first candidate cannot be equated with it yet, and whose second would misuse the kernel | Blocked on `?r` and `?s`: the transaction does not catch the postponement, and the second candidate is never tried |
| A candidate that misuses the kernel, in a goal queued before another | The loop stops with the defect; the transaction does not hide it, and the second goal is still first on the ready queue, both targets unsolved |
| A handle built inside a candidate that failed, presented after the transaction closed, by command | A defect naming the handle as stale |
| `answer = let y : ?g = ?m in y`, `?m` a goal at `?g` submitted and waiting on `?g`, then `?g ≡ Record (a : Boolean, z : Int)` submitted through the same attempter, then the loop | The first attempt Registered on `?g`, the equation Committed, and the loop Completed, the retry passing over `cand0` and rolling back `cand1`. `?g` is the record type, the `let`'s annotation zonks to it, and `?m` to `Main.cand2`; the term crosses the boundary with nothing unsolved, refers to `Main.cand2` alone, and the Core checker accepts `Main` with `answer` declared after it |
| `(λ(x : Int). x) true`, returned for a goal at `Int` | Committed, its claim derived from its parts; the Core checker refuses the declaration it completes |
| A goal left unsolved, its target zonked and taken to the boundary | Reported as a residual term metavariable, and not crossed |
| The scenario above, run twice from one input in a session that traces | The same submissions, report, term, state, and trace. The attempt that waited is rolled back whole; in the retry, the transaction passing over `cand0` commits, `cand1`'s is rolled back, and `cand2`'s and the attempt's finish are kept |
| An attempt finished with a transaction open | A defect naming the transaction, and nothing committed |
| An attempt finished with a binder open, and an acceptance that would fail | The binder defect. The binders are checked before anything is accepted |
| An attempt whose requests assigned and warned, finished with an acceptance that fails | Rejected, and neither kept. The acceptance runs inside the attempt, before it commits |
| A retry, whatever it comes to | One unit spent, whether the job solves, postpones again, fails, or ends in a defect |
| No fuel left with a job on the ready queue | The loop stops naming that job, which stays at the front of the queue. Taking it first would leave it on no queue, where nothing reaches it again |
| No fuel left and the ready queue empty | Quiescence as usual. Fuel is checked where a job would be taken, and none is |
| A retry that fails, with other jobs still ready | The loop stops at that diagnostic. The jobs after it would be retried without what the failed equation would have told them |
| A retry that fails | Reported at the site of the job that failed, not at the site of the equation whose assignment woke it |
| Quiescence, with a job awaiting a metavariable it is not registered under | A defect, not a report of insufficient information. That assignment would never wake it, which says nothing about the program |
| Quiescence, with a job awaiting nothing and on no queue | A defect likewise, checked before anything is reported as waiting |
| Quiescence, with several jobs waiting | Each is reported with its site, its job, and what it awaits, in the order the jobs were created |
| A `Lacks` assumed of a flexible tail | Yields no atomic fact, and yields one at the attempt after that tail is solved to a row with a rigid one |
| The same assumption, where the solution carries the key | Rejected. Which store rejects it is the obligation's and not the context's, the facts derived from a site being silent about a metavariable |
| A `Disjoint` between two flexible tails | Watched under both. A record per metavariable cannot hold one, there being no one metavariable it belongs to |
| An obligation whose site proves the rigid tail a solution introduced, and the same obligation carried from a site that does not | Admitted, and refused. The two differ in nothing but which context the obligation carries |
| A requirement solved to a rigid tail nothing proves anything about | Refused. What holds of a rigid variable is what its own context gives |
| An assumption whose tail is solved to a rigid one | Admitted with nothing proved, and refused only where the solution carries the key. Held to a requirement's rule it would prove itself, zonking it being how its own site's facts grow |
| A closed obligation that is unproved, or already contradicted | Refused where it is introduced. Watching nothing, it would otherwise never be re-decided |
| A unification that assigns and then meets a sub-equation it cannot decide | Reports both the dependency and what it assigned. Reporting the dependency alone has an equation that has broken a constraint read as one short of information |
| A context handed to a unification with assignments nobody has acted on | Refused. Emptying it instead makes losing a wake, and a re-deciding, the quiet default |
| The fresh tail of a two-sided refinement | Carries its kind and the scope both sides had, and no constraint. What it owes is what the two tails it replaces owed, which zonking their constraints says |
| What a metavariable's own record holds | Its kind and its scope. A row constraint may relate two metavariables and must be decided against its own site, so neither fits in a record one metavariable owns |
| What a rollback restores | Everything an attempt owns, and nothing besides. Which half of the session's state a field stands in is the whole of what decides its fate, so no rollback has to remember to save one or to skip one |

**The catalog's entries come from the module's own declarations and from the interfaces of its imports, and the second is not yet possible.** A `.dmi` carries arities and no scheme or attribute ([Interface](../05-Backend/03-Interface.md)), so until it does, a resolver finds an instance a module declares itself and none an import declares. The kernel reads a catalog however it was assembled, so nothing above waits on it; what waits is an imported instance working in practice.

### Handler declarations and implicit insertion (step 7)

These belong with elaboration and are written once a surface language exists ([Effect Handlers](../02-Surface-Language/02-Effect-Handlers.md)).

| Input | Required outcome |
| --- | --- |
| `handler h : E ~> ρ where …` | Desugars to a value declaration whose scheme is effect-polymorphic and whose source row holds the target beside `E`. The narrower source row does not compose |
| A clause written with neither marker | Desugars to `full`. Core has no unmarked form to fall back on (D28) |
| A handler declaration with a `return` clause and an answer type of its own | Accepted, written with a full signature rather than `~>` |
| `implicit` on a handler with a `full` clause, a `return` clause, or a value parameter | Rejected where it is declared |
| An expression at `a ! ( Console \| e )` inferred, with no expected row | No insertion. Inference gives an expression its own least row |
| The same expression checked against `a ! ( LiftIO \| e )`, one implicit handler for `Console` | The handler is applied to a thunk of it, under one `openEff`. What reaches Core is application, `openEff`, and `handle`, and nothing else |
| `ρ1 ≡ ρ2` solvable by instantiating a metavariable | Solved by unification. Insertion is attempted only on a definite failure |
| `( Console \| ?e )` checked against `( LiftIO \| ?e )` | Accepted. The shared flexible tail cancels first, leaving a settled key difference. Waiting on it would stall the ordinary case |
| A flexible tail surviving the cancellation of shared tails | Stuck on the metavariables awaited, in the queue synthesis goals use. Not a failure |
| A rigid tail shared by both rows | Not a reason to wait. It cancels, and nothing in the goal can assign it a key |
| A computation already performing the target, `( Console, LiftIO \| e )` checked against `( LiftIO \| e )` | Accepted, and widened by nothing. Adding an element the row already carries is not well-kinded |
| A key carried only by the expected row, with an empty plan | Accepted. Step 4 widens, and the term is the widened thunk forced at once rather than a nest of applications |
| A key on both sides whose payloads differ | Failure. A widening adds elements and reconciles no payload |
| One key contributed to `W` twice with different payloads, by two targets or by a target and the expected row | Failure where `W` is formed. It is a union of finite maps and is partial |
| `{ Console, File }` checked against `{ LiftIO }`, with an implicit handler for each | Ambiguity. The dependency relation orders neither, so the plan is not unique (D29) |
| `{ Console }` checked against `{ LiftIO }` through `Console ~> Logging` and `Logging ~> LiftIO` | Accepted. The order is unique under the **transitive closure**, which the direct edges alone do not make total for a chain of three |
| Two handlers nested by one plan | The inner result is thunked again before the outer receives it, a handler taking a thunk and returning a computation |
| A plan of no handlers at all | The term is `q0 Prim.Unit`, the widened thunk forced. A rule written as a nest of applications has no term here |
| Two implicit handlers for one key | Ambiguity, naming both and the modules they come from |
| Implicit declarations forming a cycle across two modules | Rejected where `Ξ` is assembled from the imports. Neither declaration is wrong on its own, so checking one at a time does not see it |
| An implicit handler for a labelled instance's key | Out of scope for v0.1, `Ξ` being keyed and the spelling of labelled instances unsettled |

### A handler's cells (step 7)

| Input | Expected |
| --- | --- |
| A handler declaration with `var` declarations | The declarations become its `cells` layout and the `@ ( ē )` of its `handle`, keys and initial values in the order written |
| `x!` and `x := e` | `readCell` and `writeCell` on the key the name gives. The write is `Unit`, which a clause binds as it binds any other result |
| Two `var` declarations of one name | Rejected where they are written. A region's keys are distinct |
| `x!` or `x := e` in a `return` clause, in an initial value, or outside the handler | Rejected. A cell stands in the operation clauses alone |
| `x` alone, where `x` names a cell | Never denotes the cell; it denotes a local `x` where one stands and is unbound otherwise. No value stands for a cell, which is what keeps one from being stored or returned |
| The region variable the declarations generate | Fresh for the context the `handle` stands in, the layout being kinded outside the binder and then standing inside it |
| The generated scheme | Carries `RegionKey ∉ e` beside the effect's own `Lacks`. That is what discharges the region premise where the residual row is a variable |
| A handler with cells applied in a clause of another handler with cells | Rejected by that constraint, and reported against the clause the application stands in |
| A handler with cells applied in the thunk of another | Accepted. The computation a handler handles carries no region, so the two never meet |
| An implicit handler with cells, inserted into a clause of a handler with cells | Rejected the same way. The constraint is discharged where the handler is applied, not where it is declared |
| A clause body of a handler with cells reaching a global | Widened through the region, the clauses standing at `ρ' = ( region r ι \| e )` where a handler without cells leaves them at `e`. A curried function is widened **once for each argument it is passed**, every stage being an arrow at the empty row standing where `ρ'` is ambient (D8) |
| `implicit` on a handler one of whose initial values does not elaborate to a value form | Rejected where it is declared. An initial value runs whenever the handler is applied, and an inserted application stands where nothing is written |
