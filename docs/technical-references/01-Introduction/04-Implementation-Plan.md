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

**The machine does not replace the Core evaluator.** Preservation reduces a Typed Core term one step and re-runs the type checker; erasure compares the typed relation against the erased one. A machine state carries no types, so it serves neither — there is nothing to type check, and no typed side to compare against. The Core evaluator of step 4 is what those two properties are tested against, and it stays.

What the machine adds is of two kinds. It is a **second evaluator to compare against**: one program run both ways should give the same value and the same sequence of observable effects, which tests the whole of translation and lowering at once and is what catches a fold that reorders effects or drops one. And it **runs programs the web backends cannot**, a second resumption of a continuation among them (D33), so effect safety and progress can be exercised on terms that D18's gap otherwise puts out of reach.

Anything stronger — asserting preservation over machine states — would need a correspondence between a machine state and the Core term it stands for, and nothing defines one.

## Notes on step 6

The set of FFI the backend must implement is `stella-base-0.1`, the first version of the `Base` ABI surface ([Open Questions](../99-Open-Questions/01-Open-Questions.md)). The longer it is deferred, the more the standard library settles into a shape that depends on FFI, so it should be fixed while writing this backend.

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

This requires a Core evaluator, which step 4 needs regardless. Type checking a hand-written module confirms that it is well typed; running it is what confirms that it computes.

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
| A pure global applied where the ambient row is not empty, as `Base.Int.add n 1` is under `( State Int | e )` | Rejected without `openEff`. An application requires the arrow to carry the ambient row and containment is never inserted (D8); currying makes it one `openEff` per argument consumed |
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

The interpreter is handed a table already assembled, so these need no host that imports anything: a table written by hand is what a test supplies ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

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

Four of the eight operations of `stella-base-0.1` are `Base.Array` entries, and they are the first that carrying one out cannot do without reaching the payload of a value ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

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

**`Data.Array.mapArray` is not that case and does not belong to this step.** The loop it is written as tests `i < length xs`, and `stella-base-0.1` holds no comparison: `Base.Int` has `add` and `sub`, so nothing decides an ordering on `Int`. The writes are unrolled instead, which reaches the same entries by the same route. **The surface is what is unfinished here, not the interpreter** — the entries settled so far were chosen by what the machine needed, and what a program needs is a different list, which is the ABI's own work and follows this one ([Prim and Base](../06-Modules/02-Prim-and-Base.md), [Open Questions](../99-Open-Questions/01-Open-Questions.md)).

**Reading a slot `unsafeNew` left unwritten is not in this table, and nothing replaces it.** It violates the precondition of `unsafeIndex` (D42), so a test executing such a read and asserting anything about the result would be fixing what the specification declines to fix, and would fail a backend that chose differently.

**Nor is the converse testable.** A backend that tracks which slots are written and faults on an unwritten read is **conformant**: the ABI obliges no one to detect a violation and equally forbids no one from doing so, and a program that runs there and nowhere else is exactly the difference an unspecified case admits. So "no initialization bit is kept, and no read consults one" is **not** a conformance property and must not be asserted as one. It is a performance decision of this interpreter — the check would stand on the hot path of the operation a portable array library is built out of — and belongs in the interpreter's own notes rather than in a test.

What is testable around the precondition is only what holds on either side of it: an in-range written read gives the element, an out-of-range read faults, and a program that writes every slot before reading gives the same answer whatever the allocation left.

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
