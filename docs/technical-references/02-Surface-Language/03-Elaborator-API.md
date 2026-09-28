# The Elaborator API

[Elaboration](01-Elaboration.md) gives the representation elaborators work with — Core⁺, the metavariable context `Ψ`, the constraint forms, and row unification. This document fixes **who runs what**: which part of elaboration is a library the standard library owns, which part is the compiler's, and what the two say to each other.

The subject is the mechanism a synthesizer runs under, not any one synthesizer. The standard type class resolver is the first user of it and settles none of it.

## Two layers

Elaboration is split into **policy**, which is guest Stella code, and **mechanism**, which is the compiler's (D39).

| | Owns | Which is |
| --- | --- | --- |
| guest | policy | the search for a candidate, which candidate is taken, coherence, ambiguity, and the diagnostic a failure produces |
| host | mechanism | `Ψ`, the metavariables of types and of terms, unification, scope checking, the transaction, the ready and blocked queues, and fuel |

`Elab` is the boundary. A synthesizer asks the host to unify, to create a metavariable, to look a declaration up, or to abandon the attempt, and the host answers; nothing of the solver's state is the guest's.

**The split is what makes resolution policy replaceable**, which is one of the properties the design claims ([Overview](../01-Introduction/01-Overview.md)). A policy living in the compiler would be replaceable only by editing the compiler, and library-defined type classes would be a description of an arrangement rather than the arrangement itself.

**What must not move to the guest is the solver's state.** Rollback has to be exact, and a guest holding a copy of `Ψ` would give two answers to one question — the host's, and whatever survived the guest's own restart. The same argument settles every other piece of mechanism above: each is something an attempt must be able to undo.

**A host synthesizer is a reference implementation and not a provisional standard resolver.** One is worth having, for testing the scheduler and for the bootstrap below. Writing the standard type class resolver as one is not: the claim the design most needs evidence for is that a library can carry that resolver, and a host implementation postpones the evidence indefinitely.

### The compiler is the host of a compile-time session

`f` runs on Steam, in a session the compiler opens for elaboration. The compiler is that session's **host** in the sense [Abstract Machine](../07-Runtime/01-Abstract-Machine.md) gives the word: what the interpreter runs on, and what it reaches anything outside itself through. An `Elab` operation is a capability the host supplies, as a native leaf action is on Node.

## What a synthesis goal carries

`⟨ τ by f ⟩` becomes the constraint `Synth ?m τ f`, and `f` is a **`SynthRef`**: a resolved, fully qualified global name.

```text
SynthRef = Qualified Ident        the synthesizer, as name resolution settled it
```

It is not a pointer to a host function. Three things follow. The compiler holds no algorithm, only a name to call. The name is resolved where every other global name is, against `Σ`, so a synthesizer that does not exist is reported there rather than at the goal. And one Core⁺ term means one thing however it travels, a name being stable where an address is not.

## What a pending job carries

Everything the scheduler can postpone has two parts: an **envelope**, which is the same for all of them, and a **job**, which is not.

```text
Pending =
  { id        PendingId, which the blocked table registers
  , site      the envelope below
  , awaiting  the metavariables it last postponed on
  , job       one of the three below
  }

Site =
  { context   Γ as it stood where the job was created, the row constraints
              assumed there among it, as they were written
  , origin    where it came from, for diagnostics
  }

job = JobUnify           EqualityGoal    { kind, τ1, τ2 }
    | JobSynthesis       GoalRecord      { target, expectedType, synthesizer }
    | JobImplicitHandler HandlerGoal     { sourceRow, targetRow, thunk, Ξ }
```

**The envelope is shared because every one of the three is decided against its site**, though what each takes from one differs. A synthesis goal reaches the bindings and the assumptions through `localContext` and `localConstraints`. An **equality** takes two things: the kind variables in scope where it was written, which a kind metavariable created while solving it may mention, and where a failure is reported. One woken far from where it was written and creating a kind metavariable under whatever elaboration has since reached would admit a kind variable that is out of scope at the equation, or refuse one that is in it.

**What decides a substitution is not the site of the equation that made it.** Deciding `?s := D ⊎ R` requires the row constraints naming `?s` to survive it, and each of those is an obligation holding on the assumptions of the site **it** came from — several different sites, in general, and not necessarily this equation's ([Elaboration](01-Elaboration.md), [Rows](../03-Typed-Core/02-Rows.md)). The facts a substitution is judged by therefore travel with the obligations rather than with the equality, and an obligation decided against the facts at hand would be proved from assumptions that do not hold where it arose, or refused where the ones that do hold prove it.

**An equality job is one type equation, carrying the kind both sides stand at.** Unification is directed by that kind rather than synthesizing it ([Elaboration](01-Elaboration.md)), so the kind travels with the equation instead of being recovered when the job is woken. A **row** equality is an equation of this form at a row kind, its payload equations being type unification's to discharge, so nothing separate is queued for one. A **kind** equality is never queued at all: kind equality is syntactic (D2), so it is decided where it is met and has no third outcome to wait for.

**The context is a snapshot and not a reference.** A job is created deep inside a term and woken much later, when elaboration stands somewhere else entirely; `localContext` answering with whatever is current at that moment would answer about another part of the program. The snapshot is what makes an attempt a function of its job rather than of the schedule.

**What is snapshotted is lexical belonging and not solutions.** The types in `context`, and the rows its assumptions mention, may contain metavariables, and those are read against `Ψ` as it stands — zonked afresh at each attempt. Freezing their solutions instead would have a later attempt reason about a `Ψ` the rest of elaboration has moved past, which is the error the snapshot exists to prevent, met from the other side.

**`Γ*` is derived at each attempt and is stored nowhere.** The atomic facts entailment decides from come from decomposing the assumptions over their normal forms ([Rows](../03-Typed-Core/02-Rows.md)), and what a normal form is depends on what `Ψ` has solved: a decomposition frozen at the site would answer about a row that has since been refined. The site therefore keeps the assumptions as they were written, and each attempt decomposes them afresh. This is the paragraph above applied to the one part of a context that is not syntax.

**Only a rigid tail yields an atomic fact.** A fact is about a row variable `Γ` binds, and an assumption whose tail is still a metavariable says nothing about one — it is a condition on the assignments that metavariable admits. Every fact derived is a consequence of the assumption it came from, so the derivation is sound and incomplete in one direction only: an assumption silent at one attempt contributes once its tail is solved to a row with a rigid one, which is what deriving it afresh buys.

**Such an assumption is held as an obligation, and holding it is not the site's.** `k ∉ ?r` forbids `?r := ( k : A | () )`, and nothing a context does refuses that: the facts derived from the site are silent about `?r`. The obligation belongs to the constraint set the session owns, is recorded in the same act that introduces the assumption, and is re-decided at every assignment to a metavariable it names. It is part of what an attempt owns, so a rollback restores it with everything else.

**Every obligation carries the context it came from, and is decided against that one.** The assignment to be judged may be made anywhere, under assumptions that have nothing to do with the constraint being preserved; deciding it against the site the assignment happened at would prove it from assumptions that do not hold where it came from, and refuse it where the ones that do hold prove it.

### What it takes to hold depends on why it must

An obligation holds on one of two **bases**, and the rule is not the same for the two.

| | Why it must hold | What an assignment must not do | What a rigid tail entering it needs |
| --- | --- | --- | --- |
| **assumed** | the site assumes it, and the final Core context carries it | make it unsatisfiable | nothing; what a site assumes is the authority its facts are derived from |
| **required** | the solver imposed it on a row it is building — that a record row not repeat a key, that two rows joined by `⊎` stay apart | the same | to be **proved** from the facts of the site the requirement arose at |

**Deciding one by the other's rule is a hole either way.** An assumption held to the second rule proves itself: `k ∉ ?r` assumed and then `?r := t` makes `k ∉ t` a fact of that very site, since zonking the assumption is how its facts grow, so nothing is ever refused. A requirement held to the first admits a rigid tail that nothing says anything about, and the Core that results is not well-kinded.

**Nothing is held undecided.** An obligation is decided where it is introduced and not only when something assigns into it. One whose constraint carries no metavariable watches nothing and so is never re-decided, and a closed requirement that is unproved, or an assumption already contradicted, would stand in the store unread. What the store holds therefore means "holds so far, and these are the metavariables that could still break it"; what is settled on arrival is not kept at all.

**`localContext` and `localConstraints` are two views of one field.** A context carries its assumptions with it, as written, and the two operations project the bindings and the assumptions of the same snapshot rather than reading two stores that could disagree. The decomposed facts are neither view: they are derived from the second and kept nowhere.

What the **guest** sees of a synthesis job is the expected type, with its site reached through `localContext` and `localConstraints`. None of the record above is specific to type classes: every field is a fact about a job, and none is a fact about a class, an instance, or a dictionary.

### The module environment is built once, before any job exists

**What `lookupGlobal` and `declsWithAttr` read is assembled before the first job is created, and its domain does not grow.** It holds two things: the entries the interfaces of the imported modules publish, immutable throughout, and every top-level name this module declares, with that declaration's attributes and its scheme — the written one where a signature is given, and one carrying metavariables where the scheme is to be inferred. `Ξ`, the implicit handlers the imports make visible, is assembled at the same point ([Effect Handlers](02-Effect-Handlers.md)).

**Both halves are there because `declsWithAttr` reaches across modules.** An attribute is persisted in a compiled interface exactly so that a resolver can find an instance another module declares ([Modules](../06-Modules/01-Modules.md)); a catalog of local declarations alone would answer half of every question put to it.

**Were it to grow, a synthesizer's candidates would depend on when its goal was attempted.** A goal created while one binding group is being elaborated and woken while a later one is would see declarations the first attempt could not. This is not a corner: an instance is an ordinary declaration carrying an attribute ([Modules](../06-Modules/01-Modules.md)), so a growing environment is one in which coherence turns on the schedule — the thing the restart contract exists to rule out.

**Neither half needs anything elaborated, and that is what lets the catalog precede everything.** This module's top-level names and the attributes written on them are read off its text, and a scheme is the one written at the declaration or a provisional one carrying metavariables where none is; the imported entries are read off interfaces compiled already. No right-hand side of this module has to have been elaborated, and the dependency graph does not have to exist.

**The domain is fixed and the schemes sharpen.** A provisional scheme carries metavariables, and those are read against `Ψ` as it stands — zonked at each attempt, exactly as a site's context is. What is frozen is which names exist and what each is called, never what has been solved about them.

**The catalog is not in the envelope**, having nothing to do with a site. Only what varies from one site to another is snapshotted per job.

### The dependency graph is settled after elaboration, not before it

**The catalog and the graph are different things and are fixed at different times.** A synthesizer inserts a reference to the dictionary `declsWithAttr` found for it, and that edge stands in no surface right-hand side; an implicit handler the elaborator supplies is another such reference ([Effect Handlers](02-Effect-Handlers.md)). An order computed before elaboration would have seen neither.

```text
1. before any job exists, and so before the first right-hand side is elaborated
   the visible catalog:
   immutable imported entries plus every local name, attribute, and scheme

2. during elaboration
   references are written into tentative Core⁺ terms;
   attempts may commit or discard those terms

3. after all jobs solve and the right-hand sides are zonked
   collect local-to-local edges from the committed terms,
   then compute SCCs, rec groups, and the Core order
```

**The graph is read off the terms rather than recorded as elaboration goes.** A candidate search builds a reference to a dictionary and then throws or postpones; the term is rolled back, but an edge recorded beside it would not be — what a rollback restores is `Ψ`, the constraints, the constructed terms, the queues, the warnings, and the names, and an edge set is none of those. An edge a failed candidate left behind points at a declaration nothing refers to, and it can close a cycle that does not exist or force two declarations into a `rec` group neither belongs in.

Reading the graph from the committed right-hand sides dissolves the question instead of answering it, and it buys three things besides. Nothing is added to what a rollback must restore. Every kind of reference is taken in one pass, a dictionary a synthesizer inserted, a handler the elaborator supplied, and one the author wrote being occurrences of `Global` in the same term. And the order is reproducible from the module's own output, which is what makes it checkable.

**The nodes are the local value declarations.** A reference to an imported global is a sink rather than an edge: another module's declarations are settled before this one is elaborated, nothing about them can be reordered, and they take part in no cycle here. The catalog and the graph therefore have different domains, and the catalog's is the wider of the two.

**A synthesizer adds edges and never nodes.** What it produces is a term for `?m` and not a declaration, so the catalog's domain is settled while the graph does not yet exist. That is what lets the environment a woken goal reads be immutable even though the order the module is emitted in is not yet known.

**Stage 3 is what owes Core its condition**, that a `nonrec` refer to no later declaration and that every cycle sit in a `rec` group ([Modules](../06-Modules/01-Modules.md)). A cycle a generated reference closes is subject to it exactly as a written one is, and guardedness is what decides whether such a group is admissible (D14); two dictionaries referring to one another are the case recorded with the open questions ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

**Stage 3 runs only where elaboration reaches quiescence with everything solved.** Where a pending job remains, or one has failed, there is no committed term to scan and no order to compute, and what is reported is the diagnostic the scheduler's quiescence rule below gives.

**How inference and generalization interleave with stages 2 and 3 belongs with the design of inference** and is not fixed here. What is fixed is that the order Core sees is read off the terms elaboration finally committed, and never off the surface alone.

## An attempt is a transaction

Running one pending job is one attempt, and an attempt over the host's mechanism state commits or leaves nothing behind (D40).

```text
attempt(pending):
  empty the write set, then checkpoint

  Solved x       commit, empty the write set, and record the result
  Stuck cause    rollback, derive the durable dependencies from cause,
                 admit them, and register this pending under each
  Failed d       rollback, and report d
  Defect         rollback, report it, and run nothing further
```

**A defect rolls the attempt back as the other two do, and then the session stops.** An attempt leaves nothing behind but a commit, whatever ended it, and that holds for the outcome that ends the run as much as for the ones it recovers from — one exit rule rather than one per outcome. What follows differs: no dependency is derived, nothing is registered, and no further job is attempted, a defect saying that the mechanism and not the program is at fault.

**`cause` is the postponement with its provenance**, which is what decides how the dependencies are derived: one a synthesizer raised is admitted as it named it, and one the mechanism's own unification raised has them extracted. Both are below.

**The guest's heap is not part of that.** It is not the host's to restore, so the contract has two sides: the host restores what the lists below give, and the guest owes **observational restartability**, defined after them. Neither side alone is enough, and the second is the one nothing checks.

**What a rollback restores:**

- the assignments in `Ψ`, and the metavariables the attempt created
- the constraint set
- the Core⁺ terms the attempt constructed
- the attempt's changes to the ready and blocked queues
- the warnings it raised
- the fresh terms and identifiers it took, so that a name does not depend on how many times a goal has run

**What a rollback does not restore:**

- the resource counters — fuel, a deadline, and cancellation — which bound the loop, and one that rolled back would let an attempt restart forever
- **the generation counter handles are stamped from**, for the reason below

**The two supplies are governed oppositely, and each rule is what its guarantee rests on.** The supply of fresh names — metavariables, build scopes, and the names a builder binds — **is** restored, so that a name a goal takes does not depend on how many times the goal has run: two runs against the same state take the same names. The supply of generations is **not**, so that a handle issued before a rollback can never be mistaken for one issued after it: were the counter restored, the next attempt would allocate into the freed slot and stamp it with the generation just given back, and a handle the rollback invalidated would validate against an object it never named. Restoring one and not the other is deliberate, and an implementation that draws both from one counter has neither property.

The two halves say different things, and both are needed. What is restored is what would otherwise **accumulate** across attempts: a duplicate metavariable, a constraint emitted twice, a warning reported once per try. What is not restored is what must **not** be undone, or the loop would not terminate and a stale handle would not be detectable.

### Observational restartability

> Run against the same job and the same observable host state, a synthesizer issues the same sequence of `Elab` requests and reaches the same outcome.

**It does not say that two attempts of one goal agree.** The reason a postponed goal is woken at all is that `Ψ` has moved, so the second attempt is expected to reach further than the first; and an attempt that was `Stuck` had no result to repeat. Nor does it put the counters outside the picture: fuel spent is spent, and an attempt may fail on exhaustion where its predecessor did not.

**What those two have in common is that they are inputs.** `Ψ` and the resource counters are things the host shows the guest, and a run that differs because they differ is one function applied to different arguments. What the property forbids is a difference with **no input behind it** — a mutable global of the guest session, a candidate cached between attempts, a handle held across a rollback. There the two runs differ for a reason nothing records, and the term that reaches Core is the last run's.

### A dependency must survive the rollback

A rollback deletes the metavariables the attempt created, so the set a postponement names cannot be taken as given: what a job waits under has to be something `Ψ` still holds and something an assignment can still reach. It is **admitted against `Ψ` as the rollback leaves it**, and **how it is admitted depends on where the postponement came from**. The two provenances are kept apart because a rule loose enough for one hides a defect in the other.

**A postponement a synthesizer raises is admitted as it stands**, and three conditions decide it.

```text
admit(ms):
  ms is not empty
  every ?α ∈ ms existed before the checkpoint
  every ?α ∈ ms is unsolved in Ψ
```

**A metavariable the attempt created is gone.** Registering a job under one blocks it on an assignment that can never happen: nothing holds that metavariable any longer, so nothing will assign it, and the loop reaches quiescence reporting insufficient information about a name `Ψ` does not have. An empty set is the same job with nothing even to name.

**A metavariable already solved would not wake it either**, `assign` having run for it before the attempt began. A synthesizer reaching one has read a type it did not zonk, which is a defect worth reporting where it happens rather than one to wait out.

**A `postpone` failing any of the three is a contract violation, and a contract violation is a defect rather than one of the three outcomes.** It is reported at the session, naming the synthesizer, and nothing catches it. Nothing the author wrote is wrong — the program may well be solvable by the goal the synthesizer meant to wait on — so a diagnostic would blame the program for a defect in a synthesizer, and a `transact` around the candidate that raised it would read the whole thing as "not this candidate" and take the next.

**Dropping the inadmissible part silently instead would hide that defect.** A synthesizer that names one metavariable it created among several it did not would be registered and woken, and the reading that produced the bad name — a type it did not zonk, a metavariable it held across an attempt — would never be reported. Refusing the whole postponement is what makes such a reading visible where it happens.

**A postponement the mechanism's own unification raises carries its provenance, and its dependencies are extracted rather than taken.** The mechanism has no defect to hide and cannot name a metavariable a synthesizer misread; what it can do is get stuck on a metavariable it created itself, and that case is reachable rather than hypothetical.

```text
SolverStuck { blockedOn, written }

durable = (blockedOn ∪ written) ∩ { ?α | Ψ holds ?α unsolved after the rollback }
```

`blockedOn` is what the equation could not decide between. `written` is **every metavariable the attempt has assigned**, recorded as each assignment is made, which is what makes the extraction possible. Nothing filters it as it is collected: a metavariable the attempt created is one `Ψ` no longer holds once the rollback has run, so the intersection above is what removes it, and what the attempt carries is the plain record of what it wrote.

```text
Pair { a : A | ?r } { c : C | ?r }  ≡  Pair { b : B | ?s } (?v ⊎ ?w)

  the first argument refines both tails      ?r := ( b : B | ?t ),  ?s := ( a : A | ?t )
  the second is then  { c : C, b : B | ?t } ≡ ?v ⊎ ?w,  stuck on { ?t, ?v, ?w }
```

**`?t` is gone after the rollback and `?r` is not.** Registering under `?t` blocks the job on an assignment nothing can make; refusing the postponement rejects an equation that `?v` or `?w` being solved would decide. What changes the outcome of the re-run is a solution for one of the metavariables whose refinement produced `?t` — and the write set names those without anyone having to say which fresh tail arose from which, since a fresh row tail stands for what two sides share and not for either of them ([Elaboration](01-Elaboration.md)). It is an over-approximation: a wake it causes needlessly costs one attempt, which fuel already bounds.

**Attempt-local is a responsibility and not a shape.** One session holds one write set, and the attempt root empties it where an attempt begins and again where one commits. Left standing, the assignments of a job that has already committed would stand among the dependencies the next job's postponement is derived from, and a goal would be woken by work that has nothing to do with it.

**It is emptied before the checkpoint is taken and not after.** A rollback restores whatever the checkpoint saw, so an attempt that emptied the set afterwards would have the previous job's assignments put back into it by its own rollback — at exactly the moment a postponement is about to read them. The abandoning outcomes need no emptying of their own for the same reason: what the rollback restores is already the empty set.

**The write set is attempt-local, cumulative, and rolled back with an inner `transact`.** A candidate the search tried and discarded assigned what it assigned, and those assignments are not the goal's dependencies: waking the goal because a rejected candidate once touched a metavariable would have the discarded work decide when it runs. It is therefore part of what an attempt owns and not a counter the rollback leaves alone, and it is kept apart from the record of assignments the scheduler drains to wake jobs, which is emptied at each wake where this accumulates until the attempt ends.

**A postponement with nothing durable is still a contract violation**, whatever its provenance. Nothing would ever wake the job, and the loop would reach quiescence naming a metavariable no table holds.

**Correctness does not rest on a re-run producing the same fresh tail.** Another attempt may commit between the two, so the metavariable a second run creates need not be the one the first did; what the restart contract asks is that the same inputs rebuild an equivalent one, and not that a number be held across other work.

### `transact` catches a failure and not a postponement

`transact` is this same checkpoint made available to a synthesizer for trying candidates ([Elaboration](01-Elaboration.md)); an attempt is the outermost one and is not written anywhere.

**What it catches is a diagnostic**, which its result type says: `Either Diagnostic a` holds what `throw` produces and what `Failed` is. A `postpone` inside a `transact` rolls that checkpoint back and **propagates outward**, to be caught at the attempt root and nowhere before it.

The two outcomes mean opposite things where `transact` is used, and that is the whole of the reason. `Failed` says the candidate under trial is not the one, so the search takes the next. `Stuck` says nothing about the candidate: it says the goal cannot be decided yet. A `transact` returning `Left` for both would have a resolver discard a candidate a later assignment would have accepted and commit to whatever came after it — the three-way split the scheduler rests on, lost inside one attempt.

A propagated postponement is admitted at the attempt root, against that checkpoint rather than the `transact`'s, every inner checkpoint having been rolled back with it.

### A defect in the mechanism is outside the three outcomes

**Not everything that goes wrong is a statement about the program.** The solver driven against its own contract — a dependency named that `Ψ` does not hold, a metavariable it holds solved already, a record of assignments nobody has acted on — and an invariant of its own found broken, such as a row constraint whose subject zonks to something that is not a row, are **defects**. They are reported as what they are, and `transact` does not catch one.

**A defect caught as a failure would be reported nowhere.** `Left` is what a search reads as "not this candidate", so a resolver would pass over the defect on its way to the next one, and what finally reached the author would be a diagnostic about some later candidate, or a successful compilation of a program the mechanism mis-solved. The alternative failure is as bad: reported as a type error, it names a program nothing is wrong with.

**A synthesizer's contract violation is one of these.** A `postpone` naming nothing that can wake the job is admitted nowhere and caught nowhere, for the reason above: the program is not what is wrong with it.

**The two kinds are told apart once per error and never by a default.** Every error a judgement can report is classified explicitly, so that an error added later does not join the ones a search may catch by falling through a wildcard — which is the side of the distinction that hides a defect rather than the side that over-reports one.

## `postpone` restarts, and saves no continuation

`postpone` abandons the current attempt. When the metavariables it named are assigned, the goal runs **again from its beginning**, against the state the host has by then (D40).

**What is not needed is a continuation saved across a wait for a metavariable.** Within one attempt the guest **is** held, and holding it is an obligation rather than a liberty: the guest issues an `Elab` request and its execution stands while the host answers, then continues. What nothing has to hold is a guest computation **between attempts** — from a `postpone` until the metavariables it named are assigned — because `postpone` discards it along with everything else the attempt did.

The blocked table therefore holds **descriptions of work rather than machine states**. Three things follow. A compile-time session holds a suspended guest computation for the length of one request and never **while a job is blocked**, which is the difference between a protocol Steam can be given and a second continuation mechanism beside the one it has. A blocked entry can be compared, counted, and reported on. And a synthesizer is re-entered at a point its author wrote rather than at one the scheduler chose.

**A synthesizer is therefore a function of its job and of what the host shows it.** This is observational restartability read as a property of the code rather than of a run, and it is the guest's half of the contract. The host restores no guest heap, so nothing but the author of a synthesizer keeps it.

**A stale handle is the one consequence the host does catch.** A handle names a host object and a rollback may delete what it names, so a guest cache outliving the attempt would hand such a handle back and read whatever stands there now. Handles carry a generation for that reason, below.

## The scheduler

### What is queued

The three jobs arrive here for the same reason. Row unification's case (d) waits on two flexible tails ([Elaboration](01-Elaboration.md)), a synthesis goal waits on what its type mentions, and the search for an implicit handler waits on a flexible tail that survives cancellation ([Effect Handlers](02-Effect-Handlers.md)). One queue serves all three, and the resumption mechanism is written once.

**What is shared is the envelope, and what differs is the job.** Scheduling, the site, the dependency set, the transaction, and fuel are the same machinery whichever job is inside; the payloads are not, and pressing them into one record buys nothing. Which fields each holds is above.

**Not every deferred condition is queued.** A kind metavariable carries the requirements its site imposed — that its solution be quantifiable, or produce `Type` — and each is re-applied at every assignment rather than registered here ([Elaboration](01-Elaboration.md)). The difference is what the thing is: a `Pending` is work that cannot proceed until something is known, while a requirement is a condition on the assignments a metavariable admits. One is woken; the other is consulted.

### The blocked table registers an id

```text
ready   : [PendingId]
blocked : Meta ⇀ Set PendingId
pending : PendingId ⇀ Pending
```

**A pending waits on several metavariables at once**, so it is registered under each of them. Waking it removes its id from **every** dependency it was registered under, not only from the one that woke it. A stale entry left behind runs a job that is already running, or one that has already been solved.

Registering the id rather than the job is what makes that removal possible: two entries of one job would otherwise have to be recognized as one.

**`awaiting` is what the removal reads**, so that waking a job costs no scan of the blocked table. Its lifecycle is three steps and nothing else touches it.

```text
on admitting Stuck ms      pending[id].awaiting := ms
                           blocked[?α] gains id, for each ?α ∈ ms

on waking id               blocked[?α] loses id, for each ?α ∈ pending[id].awaiting
                           pending[id].awaiting := ∅
                           id is pushed onto the ready queue

on Solved or Failed        id is removed from pending
```

**`awaiting` is assigned and never accumulated.** A second postponement names whatever set it names then, which need not contain what the job waited on before: one stuck on `?a` and `?b`, woken by `?a`, and stuck again on `?b` alone is registered under `?b` and under nothing else. Adding to the set instead would wake it on assignments it no longer cares about.

**Quiescence reports from `awaiting`**, which is why it is emptied at the wake rather than at the next postponement. A diagnostic reading a set the job has already been woken past would name a metavariable that is no longer the reason anything is waiting.

### `assign` enqueues, and runs nothing

```text
assign(?α := τ):
  record the substitution in the current transactional Ψ
  re-decide the obligations ?α is watched by, each against its own site
  for each id in blocked[?α]:
    remove id from every dependency it is registered under
    push id onto the ready queue
```

**What an assignment owes is that list**, and a unification that assigns several metavariables owes it for each of them. Re-deciding may refuse the assignment, and the equation then **fails** rather than waiting.

**The list is owed by the operation that installs the substitution and not by whoever asked for one.** An equation is put through a single entry, and installing what the unification reached, re-deciding the obligations, refusing on a breach, waking the jobs, and adding to the write set happen there together. An entry that handed its caller a substitution and the set it assigned would be one every caller has to complete correctly, and a caller that completed it partly would accept a solution a row constraint forbids, or leave a job asleep on an assignment already made.

**A unification therefore reports what it assigned whether it solved or became stuck.** It assigns as it descends, so it can refine one metavariable and then meet a sub-equation it cannot decide; an outcome that reported the dependency alone would have an equation that has already broken a constraint read as one that is merely short of information. What is committed is another matter, and only a success is.

A **failure** reports the diagnostic and nothing else. The whole equation is rolled back, so there is no assignment left for an obligation to be re-decided against and no wake to perform.

**Recording is not publishing.** An `assign` happens inside an attempt, and the substitution together with every queue change above is part of that attempt: where it goes on to postpone or to fail, the assignment is rolled back and the jobs it woke go back to waiting where they were. What makes an assignment visible to anything else is the enclosing attempt committing.

**Nothing is executed here.** Running a job from within `assign` would start an attempt while another is open — a nested checkpoint whose rollback would have to undo part of the outer one — and a job reachable from two assignments of one attempt would start twice. Leaving the loop as the only thing that runs a job removes both, and it is what makes the paragraph above simple to hold to: a woken job is an entry on a queue, which a rollback restores like any other.

### The loop

```text
submit(job), outside any attempt:
    create it, and attempt it at once              no fuel is spent

create(job), inside an attempt:
    create it, and queue it for its first attempt   owned by the attempt

while the ready queue is not empty:
    a retry at the front, and no fuel left
                                stop, naming that job; it stays there
    take an id, spend a unit of fuel if it is a retry, and attempt it
        solved, or postponed    go on
        failed                  stop, and report that diagnostic
        defect                  stop, and report the defect

on quiescence:
    the tables disagree         a defect: a registration and an awaiting set
                                that do not match leave a job no assignment wakes
    a job that awaits nothing   a defect: no assignment can reach it
    no job left                 zonk, and hand the term to the Core type checker
    jobs remain                 report insufficient information, naming each
                                job and the metavariables it awaits
```

The three-way outcome is what separates "unsolvable" from "not enough information yet", and it is the same split at each of the three job kinds.

**The loop stops at the first failure.** A failed attempt is rolled back, so the jobs retried after it would be retried without what the failed equation would have told them, and nothing yet tells a failure of their own from one that follows from it. Collecting several diagnostics waits on a rule for recovering from one, and where it arrives, what the mechanism reports keeps the jobs still waiting beside the diagnostics; which of them an author is shown is the presentation's to decide.

**Fuel is spent by a retry and by nothing else.** A first attempt spends none, whether it is made where a job is submitted or taken from the ready queue a job created inside an attempt was put on; the queue marks each entry as a first attempt or a retry, and a wake is what queues a retry. A retry the fuel does not reach stays on the ready queue and is named where the loop stops, and one that has been attempted has spent its unit whatever it came to.

### Which job may be attempted

**A job is attempted only while no queue holds it**: `pending` holds it, it awaits nothing, and it is not on the ready queue. There are two points at which a job is in that state, and they are the only two entries to an attempt.

```text
just after create        a job submitted outside any attempt, attempted at once
just after takeReady     a job queued for its first attempt by the attempt that
                         created it, or queued for a retry by a wake
```

**Attempting a job the scheduler still holds is a defect.** One still on the ready queue would run again when the loop takes it, and one still registered under a metavariable would be registered a second time by the postponement its attempt admits. Neither is a statement about the program, so neither is a diagnostic.

What is checked directly is `awaiting` and the ready queue. That the blocked table does not hold the job either is not read off the table: it follows from the invariant the scheduler keeps between its tables, `id ∈ blocked[?α] ⟺ ?α ∈ pending[id].awaiting` ([Implementation Plan](../01-Introduction/04-Implementation-Plan.md)), an empty `awaiting` leaving no metavariable the job can be registered under.

**Termination rests on fuel rather than on a measure.** The number of unsolved metavariables is not decreasing: refining two flexible tails introduces a fresh one ([Elaboration](01-Elaboration.md)), so a loop of assignments can create as much work as it discharges. Fuel is what bounds it, which is why it is the one thing a rollback leaves alone.

**What fuel bounds is the scheduler's retries, and not a guest computation.** A synthesizer that loops inside one attempt returns no outcome for fuel to count, so stopping it is Steam's — an instruction budget, or a cancellation the host raises. The two answer separate questions and neither stands in for the other.

## The kernel API

What the host offers the guest is divided by what it depends on.

**The kernel** is what a synthesizer needs and a parser is not required for: the metavariable operations, unification and entailment, the observation of types and of the environment, the construction of Core⁺ terms, and control.

**The syntax API** — `quote`, `check`, `infer`, and hygiene — requires a Surface AST and is separate. The first guest synthesizer uses the kernel alone, which is what lets it run before a parser exists.

### Types and terms cross as handles

A `Type`, an `Expr`, and a `Goal` reach the guest as **session-local opaque handles**, and what the guest does with one it does through a view.

```text
goalType : Goal -> Elab Type
viewType : Type -> Elab TypeView
```

**Fixing the compiler's own representation of a type in the Steam ABI is what this avoids.** An internal representation published as an interface is one the compiler can no longer change, and Core⁺'s types are a representation that row unification and the solver are still shaping. A view is a projection with a shape of its own, which the guest pattern-matches; the handle behind it stays the host's.

A handle is session-local: it means nothing outside the compile-time session that issued it, and nothing serializes one.

**A handle is generation-tagged, and a rollback invalidates the handles to what it deleted.** Presenting an invalid one is reported as a defect in the synthesizer and is never resolved to whatever occupies that place now. This is what keeps the guest's half of the contract from failing silently: a synthesizer is obliged to hold nothing across an attempt, and a cache that does so anyway is caught at the first handle it reuses rather than by the wrong term reaching Core.

**The generation is drawn from a counter no rollback restores**, which is the whole of what makes that true: a slot freed by a rollback and filled again by the next attempt receives a generation that has never been issued, so the old handle matches nothing. A counter restored with everything else would hand the new object the number the old handle carries. It is a safety counter and not part of the state an attempt owns, and it is kept apart from the supply of fresh names for that reason.

**A generation is never issued twice in a session**, which is the premise of all of the above. A session that has issued every generation it can stops rather than wrap around to one a handle may still carry.

**The arena lives for one attempt, and what it holds is transactional.** An attempt begins with it empty and commits with it emptied again; an attempt that fails, postpones, or breaks is rolled back to the checkpoint's, which is empty. Inside the attempt an inner `transact` is an ordinary checkpoint: a handle issued before it survives its rollback, and one issued inside it is gone. Nothing needs a handle to outlive its attempt — what a synthesizer returns, the message it throws, and the metavariables it postpones on are resolved into the host's own values before the attempt ends — and a slot is free to be reused by the next attempt, the generation being what tells an old handle from a new one.

**A session is identified once for the life of the process running the guest.** A long-lived interpreter serves session after session, and a handle held over from an earlier one must be refused rather than resolved against a later session's arena.

**Every field of a presented handle is untrusted**, a handle crossing the boundary as a token. Resolving one checks, in order:

```text
issued by another session                      foreign
a generation this session never issued         unknown
no object in its slot, or one of another
  generation                                   stale
a class other than the one expected, whether
  as the handle states it or as the object is  class mismatch
```

The generation is read before the slot, so a forged generation is reported as unknown rather than as stale; and the class the handle states is compared as well as the class of the object its slot holds, so rewriting a valid handle's class does not turn one kind of object into another. All four are defects of whoever presented the handle, and none is a statement about the program.

### What a handle holds

**A `Type` holds the kind evidence it stands at**, and an `Expr` holds the type it is claimed to have.

```text
Type  =  { type : τ⁺ , kind : KindEvidence , scope : the rigid kind variables and
                                              the type variables, with their kinds,
                                              it may mention free
         , builtIn : the build scope it was built in, if any }
Expr  =  { term : e⁺ , claimed : τ⁺ ,        the term held without annotations
           scope : what the claimed type is kinded under ,
           builtIn : the build scope it was built in }
Goal  =  the goal the current attempt runs

KindEvidence = ExactKind κ⁺  |  AnyRow
```

**`AnyRow` is what the empty row stands at**, `()` being a `Row Type` and a `Row Effect` alike; it is a statement of all that is true of such a row rather than a kind left undecided, and where the place a row stands at fixes its kind — the argument of `Record`, the tail of a row with an element — the handle carries that kind instead. An `ExactKind` holds a kind that is zonked and mentions no kind metavariable.

**The evidence is given when the handle is issued, by a read-only kinding judgement.**

```text
Σκ ; Γ ; Ψ ⊢ τ⁺ ⇒ KindEvidence
```

`Σκ` is the type-level environment of the session — the kind scheme of each type constructor and the parameter kinds of each effect — and `Γ` is the scope the handle records: for a type from a site, the site's kind variables and type variables; for one a view reached under a binder, that binder besides; for a catalog scheme, the kind variables the scheme declares. The judgement checks as well as synthesizes: every kind it reads mentions only kind variables `Γ` binds, an argument stands at the kind its head's arrow asks, a binder at a quantifiable kind, a body at `Type`, an effect's arguments at its declared parameter kinds, a row's tail and a union's sides at one row kind, and every key — an element's or a constraint's, by one rule — is well-formed for the row it keys: a position non-negative, an effect declared. **It changes nothing and creates nothing**, which is what separates it from unification; a type it refuses is one no synthesizer is shown, and meeting one is a defect of the host.

**What a synthesizer is shown holds no unsettled kind.** A kind metavariable reachable from a type, a constraint, or a declaration a synthesizer observes — a variable's kind, a constructor's kind argument, a binder, a kind being synthesized — is refused as not settled. A synthesis job runs after the kinds of what it reads are decided, and a kind metavariable is nothing a synthesizer could name, solve, or wait on.

**`kindOf` and `typeOf` read what the handle holds; neither infers anything anew.** Unification is directed by a kind it is given rather than one it synthesizes ([Elaboration](01-Elaboration.md)), so `unify` takes the two handles' kind evidence, refuses as a misuse evidence that cannot meet, and hands the kind to type unification. A term's claimed type is what the operation that built the term said of it. **A claim the term does not bear out is not caught here**: an elaborator may construct an ill-typed term, and the Core type checker rejects it once the term is zonked. Rechecking Core⁺ in the kernel would be a second checker, and the trusted one is the only one there needs to be.

A term is held without annotations for the reason a term metavariable's solution is: where it lands, it takes the annotation of the place it lands in ([Elaboration](01-Elaboration.md)).

**What a goal's expected type is called is settled once.** `expectedType` is a field of the goal record below, and `goalType` is the operation that reads it; there is no second observation of the same thing.

### What a synthesis job holds

```text
GoalRecord =
  { target     ?m, the term metavariable the result is assigned to
  , expectedType  τ⁺, the type the goal is written at; its kind is Type
  , synthesizer  SynthRef
  }

Job = JobUnify EqualityGoal | JobSynthesis GoalRecord
```

**The record holds what is particular to the goal, and the envelope holds where it stands.** The context and the origin are the `Site` every job carries, so the record repeats neither. **One operation is the supported way to make a record, its `?m`, and its job**: it creates `?m` at `expectedType` under the site's context, registers the job naming it, and queues that job for its first attempt, all in one act. **The runner checks the target independently**, inside the attempt and before any synthesizer runs: `?m` is held unsolved, stands at `expectedType` once both are zonked against the current `Ψ`, and has a scope within what the site binds — within rather than equal, a target standing in another solution being narrowed with it. A job failing the check is a defect of the host: no synthesizer runs, and the attempt rolls back.

**A synthesizer's result is assigned by the runner, not by the synthesizer.** It returns an `Expr`; the runner unifies that term's claimed type with `expectedType` at `Type` and then assigns the term to `?m`, both inside the attempt, so a result that fails either is the attempt failing and rolls back with it. Unifying the claim is what lets a goal's type be learned from the candidate chosen, and what refuses a candidate claiming a type the goal does not have before its term reaches anything.

### The frame an attempt runs in

**The runner sets the current site and goal before the attempt begins, and nothing inside the attempt changes them.** Every kernel operation that depends on where it stands reads them from there.

```text
SessionEnv = { catalog, kinding, constructors, effects }      fixed for the session, before the first job
Frame      = { site, goal }            read-only for the length of the attempt
```

**Both are read and never written.** The session environment is assembled once and every attempt of a loop reads the one it was given; the frame is set for one attempt, and an action running under it ends with the frame outside as it was, whichever way it ends. Neither is part of what a rollback restores, there being nothing in either to restore.

| Reads the frame | For |
| --- | --- |
| `goalType`, the `Goal` a synthesizer is applied to | the goal: the handle must name the goal the frame is running, and a frame with no goal has none to observe |
| `localContext`, `localConstraints` | the site's context, as its two views |
| `unify`, `require`, `subgoal` | the origin a failure, an obligation, or a job carries |
| `lookupGlobal`, `declsWithAttr` | the catalog, which the session environment holds rather than the frame |

**No kernel operation takes a context or a scope from its caller.** A caller that could state one could state a wider one than it stands in, and admit a solution the site has no variable for. **A build scope is not one**: it is a handle the host issued for the site, or for a binder opened inside it, so a caller can name one and cannot state one. Every request over metavariables and constraints takes one, since what it decides against inside a binder's body is the site's variables and assumptions together with the ones opened around it:

```text
freshMetaType : Scope -> KindView -> Elab Type              under the scope's variables
isAssigned    : Meta -> Elab Boolean                        whether the current `Ψ` has solved it
unify         : Scope -> Type -> Type -> Elab Unit          an equation standing at the scope's context
entails       : Scope -> ConstraintView -> Elab Boolean     the scope's facts, against the current `Ψ`
require       : Scope -> ConstraintView -> Elab Unit        a `Required` obligation carrying the scope's context
subgoal       : Scope -> Type -> SynthRef -> Elab Expr      a job at the scope's site
```

**Every type a request is given is one the scope may use** ([below](#types-are-built-in-a-build-scope)), so nothing observed in no build scope reaches the solver: a `forall` body's variable is never equated with, or required of, a site variable that happens to share its name. Each goes through the mechanism's own operation, so an assignment is never made except where its obligations are rechecked, its wakes queued, and its write recorded.

**`freshMetaType` asks for a kind a type variable could stand at** — settled, well-formed in the scope, and quantifiable — since a metavariable a synthesizer holds stands where a type variable would; `Effect`, and an arrow whose final result is a row, such as `Type -> Row Type`, are refused as `openForall` refuses them, a row kind itself not being. The metavariables the mechanism creates for itself are not held to this: a synthesizer cannot create one, but may observe one — in a goal's type, as a row's flexible tail — and wait on it.

**`unify` equates at the kind the two handles' evidence gives.** Two exact kinds must agree; a row standing at any row kind meets a row at an exact one at that one; and two rows standing at any row kind are equated at **`Row Type`**, the one representative chosen for them — each is closed and empty, with no element and no tail, so no substitution can observe the choice. Evidence that cannot meet is a defect of the synthesizer and not a candidate that does not fit: every kind a handle holds is settled, and `kindOf` would have said so.

**`entails` answers `true` only for a proof.** A constraint waiting on a flexible tail is not proved, and neither is one the facts refute or fail to prove, so a flexible tail is never taken for a fact; a synthesizer that would rather wait reads the row's flexible tails from its view and postpones on them. Assumptions that contradict each other prove nothing here. A row with no normal form is a broken invariant of the solver, the constraint having been judged well-formed, and is a defect rather than an answer of `false`. It reads and changes nothing.

`entails` reads and `require` introduces; both, and `openConstraint`, judge the constraint by the one well-formedness judgement every constraint is judged by. The mechanism's own operations — what the elaborator walking a term uses as it enters binders — do take one; they are not the kernel, and no synthesizer reaches them.

An equality job runs under a frame with no goal, and it runs no synthesizer, so nothing in it asks for one. A kernel operation reading a goal where the frame holds none is a defect of the host that called it.

### Who fills a term metavariable

**The kernel creates no term metavariable without saying what fills it.** A bare `?m` handed to a synthesizer could be filled by nothing the synthesizer can reach — the kernel offers no assignment of a term — so it would stand in the result until the boundary refused it.

```text
subgoal : Scope -> Type -> SynthRef -> Elab Expr
```

`subgoal s τ f` is `⟨ τ by f ⟩` asked from inside an attempt: it creates `?m` under the context of the build scope `s` — the site's, with every binder opened around `s` — and a synthesis job for it at that site with the running job's origin, and returns the `Expr` `?m` claimed at `τ`, built in `s`. `τ` must be one `s` may use, standing at `Type`. **An `Expr` carries the build scope it was built in, as a `Type` does**: a term solved under a binder's assumptions or variables may be placed only under the corresponding term binder, and a synthesizer's result is accepted only where it was built in the root. **The job is queued and not attempted.** Attempting it at once would open an attempt inside the one that asked for it; it is placed on the ready queue for its first attempt, which spends no fuel ([above](#the-loop)), and like everything else the attempt did, it goes if the attempt rolls back. A synthesizer composing a dictionary from another is the ordinary case: `dictShowArray [?a] (subgoal root (Show ?a) resolve)`.

A synthesizer that wants a candidate's sub-result now rather than later calls itself, as any function does; `subgoal` is for what is to be decided by the scheduler. **The bare term metavariable remains the mechanism's**, where the elaborator knows what will fill it, and what fills one the elaborator creates is always written down beside it.

### What an observation shows

A view is one level of a thing, and each part that is itself a type is handed out as a `Type` handle carrying its own evidence.

```text
TypeView        = VarType a | MetaType Meta | ConType T [KindView]
                | AppType Type Type | ForallType a KindView Type
                | ConstrainedType ConstraintView Type | NormalRow RowView
RowView         = { elementKind : Maybe (Type | Effect)
                  , known : [ (RowKey, PayloadView) ], rigid : [a]
                  , flexible : [ { meta : Meta, type : Type } ] }
PayloadView     = TypePayload Type | EffectPayload E [Type] | RegionPayload Type Type
KindView        = KindType | KindEffect | KindRow ε | KindFun KindView KindView
                | KindVar k | KindAnyRow
ConstraintView  = LacksView RowKey Type | DisjointView Type Type
```

**A row is shown as its normal form**, `elementKind` being `Nothing` for one that stands at any row kind. Two rows are one row exactly when their normal forms agree, so how a row was written is nothing a synthesizer can rely on; `known`, `rigid`, and `flexible` come in ascending order of key, of name, and of metavariable, so one row has one view.

**An unsolved type metavariable is shown as a `Meta` handle**, which is the only way to come by one: it names a metavariable a type actually stands for, and it is what `postpone` is given. **Each observation zonks against the current `Ψ` first**, so one `Type` handle shows `MetaType` before its metavariable is solved and the solution after. **A `Meta` is what `postpone` and `isAssigned` take, and nothing else**: no request turns one into a type, the `Type` it stands for always being handed out beside it — the handle viewed as `MetaType`, a row's flexible tail, and what `freshMetaType` returns — with the build scope it came from.

**A row's flexible tail is shown twice over**: as the `Meta`, which is what `postpone` is given, and as the `Type` standing for it, in the row's build scope and at the row's kind, which is what the row is rebuilt from. A `Meta` alone says nothing of where it was observed, so turning one back into a type would let a tail observed in no build scope — a catalog scheme's, a `forall` body's — into one.

**An observation changes the arena and nothing else.** It issues handles for the parts it shows; no metavariable, obligation, job, or unit of fuel is touched, so reading is never what makes two runs of one goal differ.

### Types are built in a build scope

```text
rootScope         : Elab Scope
typeVariable      : Scope -> a -> Elab Type
typeConstructor   : Scope -> T -> [KindView] -> Elab Type
applyType         : Scope -> Type -> Type -> Elab Type
emptyRow          : Scope -> Elab Type
extendRow         : Scope -> RowKey -> PayloadView -> Type -> Elab Type
unionRow          : Scope -> Type -> Type -> Elab Type
openForall        : Scope -> String -> KindView
                      -> Elab { binder : Binder, variable : Type, bodyScope : Scope }
closeForall       : Scope -> Binder -> Type -> Elab Type
openConstraint    : Scope -> ConstraintView
                      -> Elab { assumption : Binder, bodyScope : Scope }
closeConstraint   : Scope -> Binder -> Type -> Elab Type
instantiateForall : Scope -> Type -> Type -> Elab Type
instantiateScheme : Scope -> QIdent -> [KindView] -> Elab Type
```

**A `Scope` is an opaque handle naming what a type built in it may mention.** The root is the running site's context; `openForall` gives a child scope binding one variable more, and `openConstraint` one assuming one constraint more. `Scope` and `Binder` are handle classes like the others, attempt-scoped and resolved by the same checks. Every `Type` records the build scope it was built in, and **a builder uses a type only where it was built in the scope given or in one of its ancestors** — never in a descendant, where a variable the type mentions is not bound, and never in a sibling.

**No builder merges the scopes of the types it is given.** Two binders opened alike, with one kind and one hint, are still two binders, and only the scope a type was built in says which one it mentions; a builder that merged scopes would let a type from one `forall` body be closed under the other.

**A type observed rather than built carries the scope it came from.**

| Observed | Build scope |
| --- | --- |
| `goalType`, `localContext`, `localConstraints` | the root |
| `typeOf` of an `Expr` | the build scope the term was built in |
| a catalog scheme, from `lookupGlobal` | none |
| `whnf` of a type | the type's |
| a part a view takes — a head, an argument, a row's payload, a constraint's row | the whole's |
| the body of a `forall`, or of a constraint | none |

A type in no build scope reaches a builder only through the operation that opens it: **`instantiateForall`** for a `forall`, and **`instantiateScheme`** for a scheme, which reads the entry from the catalog by name and judges it in its own scope — at `Type`, under the kind variables it declares and no type variable, as `lookupGlobal` does — before the caller's scope is involved. A variable free in the scheme would otherwise be taken for one of the caller's sharing its name, and a scheme failing that judgement is a defect of the host, whose catalog it is. A scheme's parts inheriting the root's scope would let its kind variables reach a type without being instantiated, and a `forall` body inheriting its parent's would let its binder escape.

**The host ABI is first order.** Opening a `forall` hands back a binder, the variable it binds, and the scope its body is built in, and closing it takes the three back, in the scope it was opened in; no request of the host waits on a guest closure. The variable is named after the hint and drawn from a supply of fresh names that is part of what an attempt owns, so a rolled-back attempt returns the names and scopes it drew, and a re-run draws the same ones. **A name is fresh where it is bound**: the hint, `#`, and the first number whose name the scope does not already bind. That no source identifier holds `#` keeps a name apart from what an author wrote and nothing more, since a context may hold one another operation of the host generated; a number skipped is spent. Value variables and type variables are drawn from supplies of their own.

**Every binder opened is closed exactly once, by the operation for its sort and inside out, before the attempt succeeds.** An attempt holds the binders it has open, each with the ancestors of its body's scope, as part of what it owns, so a rollback releases the ones a discarded candidate opened. One still open when an attempt ends in success — checked at the attempt root, whoever runs the attempt — one closed while a binder opened inside its body is still open, one closed twice, and one closed by the operation for another sort are defects of the synthesizer. Siblings may be closed in either order. What is built under an open binder is not only types — an obligation proved from its assumption, a job, a metavariable — and without the check those would commit without the type that carries the assumption.

**A row is sharp by construction.** Kinding judges a row's shape and not that its keys are distinct, so `extendRow` requires `key ∉ rest` and `unionRow` requires `left # right`, each introducing the requirement together with the row it builds. The requirement carries the build scope's context — the site's, with every assumption opened around it — and the running job's origin, so a row sharp only under an assumption `openConstraint` opened is built inside that constraint's body and nowhere else. A row the requirement refuses, a key it already has included, is a **failure** and not a defect: it is a candidate that does not hold, and a `transact` around it takes the next.

The key says what element a payload makes: a structural key over a `TypePayload` a field, `EffectKey E` over `EffectPayload E` an unlabelled effect, and a `SymbolKey` over an `EffectPayload` a labelled one. **A region element is refused by every builder**, `RegionPayload` being shown by a view and never accepted: a region is introduced and removed by the handler that owns it, and by nothing else (D36).

**A constraint is judged well-formed where it is opened, and whether it can hold is decided where it is closed.** Closing holds the assumption as an `Assumed` obligation, so an assignment making it unsatisfiable is refused from then on, and one that cannot hold already is a failure there. One that cannot hold makes every requirement built under it fail on the facts of its scope in the meantime, and the binder has to be closed before anything built under it commits.

**`instantiateForall` zonks both sides, then substitutes capture-avoidingly**: a binder of the body that the argument mentions free is renamed, to a name drawn from the same supply of fresh binder names, before the substitution passes it. Zonking the argument first is what lets a binder named only by a solved metavariable's solution be seen. **An unsolved metavariable that could come to mention a variable the substitution treats specially postpones the instantiation until it is solved** — one in the body whose scope has the binder or a binder being renamed, and one in the argument whose scope has a binder of the body. The substitution stops at an unsolved metavariable, so the first's later solution could mention a binder the result no longer has, and the second's could be captured by a binder that was not renamed. This is waiting for information and not a defect: which substitution is safe is decided by a solution not yet made.

**Every result is kinded by the read-only kinding judgement under its scope**, and a kind a builder is given must be settled there: `KindAnyRow` is evidence rather than a kind, and cannot be written. A builder asked for what cannot be built — a kind that does not fit, a type from another scope, a binder closed where it was not opened, a scheme the catalog lacks or given the wrong number of kinds — refuses it as a defect of the synthesizer. Whether a candidate fits a goal is `unify`'s to decide, and a candidate a builder refuses is not one.

### Terms are built in a build scope

```text
localVariable : Scope -> Ident -> Elab Expr
globalRef     : Scope -> QIdent -> [KindView] -> Elab Expr
literal       : Scope -> Literal -> Elab Expr

termApply       : Scope -> Expr -> Expr -> Elab Expr
typeApply       : Scope -> Expr -> Type -> Elab Expr
constraintApply : Scope -> Expr -> Elab Expr

openLambda         : Scope -> String -> Type -> Elab { binder, variable : Expr, bodyScope }
closeLambda        : Scope -> Binder -> Expr -> Type -> Elab Expr         the last is the row
openTypeAbs        : Scope -> String -> KindView -> Elab { binder, variable : Type, bodyScope }
closeTypeAbs       : Scope -> Binder -> Expr -> Elab Expr
openConstraintAbs  : Scope -> ConstraintView -> Elab { binder, bodyScope }
closeConstraintAbs : Scope -> Binder -> Expr -> Elab Expr
openLet            : Scope -> String -> Expr -> Elab { binder, variable : Expr, bodyScope }
closeLet           : Scope -> Binder -> Expr -> Elab Expr
openLetRec         : Scope -> [ { hint : String, type : Type } ]
                       -> Elab { binder, variables : [Expr], bodyScope }
closeLetRec        : Scope -> Binder -> [Expr] -> Expr -> Elab Expr
openJoin           : Scope -> String -> [ { hint : String, type : Type } ] -> Type
                       -> Elab { binder, join : Join, params : [Expr], definitionScope, bodyScope }
closeJoin          : Scope -> Binder -> Expr -> Expr -> Elab Expr         the definition, then the body
jump               : Scope -> Join -> [Expr] -> Elab Expr
```

**A term is built in a build scope, as a type is, and is used by the same rule**: only where it was built in the scope given or in one of its ancestors. A term built under a binder mentions what the binder binds or assumes, so it may stand only under the term binder that corresponds.

**A builder is not a type checker.** Each `Expr` holds the type it is claimed at, zonked and kinded at `Type` under its scope; the kernel checks the scope, the class of each handle, and how a binder is used, and whether a claim is borne out is the Core type checker's to decide once the term is zonked. **A leaf is claimed at the one type it can have, and the host computes it**: a variable at the type the scope binds it at, a global at its scheme instantiated at the kinds given — judged as `instantiateScheme` judges it, by the one procedure — and a literal at its literal type. `localVariable` accepts only a name the scope binds, so no name can be made up; the names a term binder binds are the host's to draw, and a synthesizer receives the variable as an `Expr` rather than a name.

**Two forms have no builder.** `?m` is made by `subgoal` alone, which creates the job that fills it. A typed hole is the Surface elaborator's, for reporting and recovery: a synthesizer that cannot build a candidate throws, where a hole would succeed here and fail only at the Core boundary, after the search had stopped.

**A binder of a term is opened and closed as a binder of a type is**: first order, exactly once, inside out, in the scope it was opened in, by the operation for its sort. Its body's scope binds what it binds — a value, a type variable, an assumption — and the name is the host's, fresh where it is bound; the variable comes back as an `Expr` or a `Type` built in the body's scope, so a term that mentions it stays under the binder. A `let`'s right-hand side is given where the `let` is opened, as a term the outer scope may use, and its variable is bound at what that term is claimed at; every name of a `letrec` is bound in each right-hand side and in the body, each declared type is one the outer scope may use at `Type`, and the group is closed with one right-hand side for each name.

**A compound term is claimed at the type the Core rule gives it, read off the claims of its parts**: an application at the result of its function's claim, a type application at the substitution `instantiateForall` makes, a constraint application at the body of its term's `C => τ`, an abstraction at the `forall`, the `C =>`, or the arrow over its body's claim, and a `let` or `letrec` at its body's. **Only a lambda's effect row is the synthesizer's to give**, no claim recording one; it is a type the scope the lambda was opened in may use, at `Row Effect`, so a row built inside the body does not leave it this way, and an effect metavariable the row needs is created before the lambda is opened.

**Where the shape a claim needs is not there yet, the builder waits on what decides it.** A function type is an application spine headed by `Function`, so a claim headed by an unsolved metavariable may become one **where the metavariable's kind and the spine's arguments are compatible with `Function` partially applied** — at most three arguments, and the kind that of `Function` with the arguments the spine does not supply already given — and only then is that metavariable waited on: `?f : Type -> Type` applied to one argument can be solved to `Function τ ρ`, and `?f : Row Type -> Type` applied to one can be solved to nothing that makes an arrow. Waiting on an incompatible head would register a job under a metavariable whose solution could never give it the shape. Once the head is `Function`, nothing inside the arrow is waited on. A `forall` or a `C =>` is waited on only where the whole claim is an unsolved metavariable. A claim no solution can give the shape is a defect of the synthesizer, the claim being observable through `typeOf`.

**`constraintApply` requires the constraint of the scope it is applied in, together with the term**: proved now, watched where a flexible tail leaves it open, and a failure where it is already broken. A constraint abstraction holds its assumption from where it is closed, as `closeConstraint` does.

**A claim the kernel derives is the type the term's syntax has under the Core rule, and no proof that the term satisfies the rule.** What the rules ask beyond the shape of the parts — that an argument stands at the parameter's type, that an abstraction's body is a value and pure, that a `letrec`'s right-hand sides are function values, that an application's arrow row is the ambient row — is the Core type checker's to decide once the term is zonked. A term whose parts disagree is built here and refused there.

**A build scope holds `Δ`, the join points a term built in it may jump to.** The root's is empty: a term standing at a site jumps to no join point around it. A binder's body inherits its scope's `Δ` — a `let`, a `letrec`, a branch, a `letjoin`, and the binder of a type alike — except the body of an abstraction, `λ`, `Λ(a)`, or `Λ(_ : C)`, whose `Δ` is empty: a join point continues the evaluation it stands in, and a body the abstraction delays runs where that continuation is gone. **A term is used, and issued, only where every join point it jumps to is in `Δ`**, so a jump built outside an abstraction does not reach inside it by any builder, and an abstraction is closed only over a body that jumps to none.

**`openJoin` opens two scopes under one binder**: the definition's, binding the parameters and the join point, and the continuation's, binding the join point alone; the definition is closed from the first and the body from the second. The parameter and result types are the synthesizer's, as Core writes them, each one the scope may use at `Type`, and the `letjoin` is claimed at the result. The join point is a handle of its own class, named by the host from a supply apart from values'. **`jump` checks that the join point is in scope and takes as many arguments as it has parameters**, and is claimed at its result; what the arguments are claimed at, and whether the jump is in tail position, are the Core type checker's.

### Cases and decision trees

```text
openCase       : Scope -> [Expr] -> Elab { binder, scrutinees : [Occurrence], treeScope : Scope }
closeCase      : Scope -> Binder -> Maybe Type -> Tree -> Elab Expr
leaf           : Scope -> Expr -> Elab Tree
guard          : Scope -> Expr -> Tree -> Tree -> Elab Tree
openBind       : Scope -> Occurrence -> String -> Elab { binder, variable : Expr, bodyScope }
closeBind      : Scope -> Binder -> Tree -> Elab Tree
recordField    : Scope -> Occurrence -> RowKey -> Elab Occurrence
openSwitchCtor : Scope -> Occurrence -> [QIdent] -> Boolean
                   -> Elab { binder, branches : [ { scope, fields : [Occurrence] } ], fallback : Maybe Scope }
openSwitchLit  : Scope -> Occurrence -> [Literal]
                   -> Elab { binder, branches : [Scope], fallback : Scope }
openSwitchKey  : Scope -> Occurrence -> [RowKey] -> Boolean
                   -> Elab { binder, branches : [ { scope, payload : Occurrence } ]
                           , fallback : Maybe { scope, residual : Occurrence } }
closeSwitch    : Scope -> Binder -> [Tree] -> Maybe Tree -> Elab Tree
```

**A decision tree is built in scopes of its own, and a `Tree` and an `Occurrence` are handles of their own classes.** Opening a `case` gives the scope its tree is built in, which names the `case`, and an occurrence for each scrutinee; a `bind` and a switch open scopes below it, a switch one per branch and one for the default, all under one binder, in the order given. A tree node is built only in such a scope, and a scope a term binder opens inside one stands in no tree. **An occurrence is read only in the tree of its own `case`, under the branch that established it** — a constructor's fields under that constructor's branch, a variant's payload under its key's, the residual under the default — which is the occurrence typing of the Core type checker: an occurrence of an enclosing `case` is refused in an inner one, whose paths are read from other scrutinees. **A `Tree` carries its `case` likewise**, and is used only in that `case`'s tree: a tree of an enclosing `case`, visible from an inner one built under it, would have its occurrences read from the inner one's scrutinees. A switch is closed with a tree for each branch, each visible under its own, and with a default exactly where it was opened with one; a switch on literals always has one. Constructors, literals, and keys are each given once.

**What an occurrence stands at is the host's to say**, so a synthesizer is given occurrences and never states one, and cannot project what no branch established: a scrutinee at what it is claimed at; a constructor's field at the field of its data type's declaration, instantiated at the kinds and then the arguments of the type the occurrence stands at, simultaneously and without capture, a binder of the field renamed where it would capture what another argument brings; `o . k`, which needs no dispatch, at the payload the record's row carries at `k`; a variant's payload likewise; and the default of a switch on keys at the residual, the row with the keys taken out of its known part and its tails kept. **The constructors are read from a table the session holds**, built once from the signature its kinding comes from, and not recovered from a constructor's scheme, which says what the constructor is as a function and not which of its arrows are fields. The constructors of one switch build one data type, the one the occurrence stands at. Where the occurrence's type is headed by an unsolved metavariable compatible with that data type partially applied — a kind variable of the data type standing for one kind wherever it occurs in the parameters the head would supply — or a row does not carry a key and a flexible tail could, those metavariables are waited on; a rigid tail says nothing of what it carries, and a head no solution makes the data type is a misuse. Whether the constructors exhaust the data type, whether it is one rather than an intrinsic type, and whether the keys exhaust the row are the Core type checker's.

**A tree is claimed at nothing, and carries the type of the first leaf it reaches**: a leaf reaches what its term is claimed at, a `bind` what its tree reaches, a guard the first of its two trees that reaches a leaf, and a switch the first branch that does, then its default. A `case` is claimed at the result type it is closed with, where one is given, and otherwise at what its tree reaches; a tree reaching no leaf needs the type given. That every leaf agrees is the Core type checker's.

A constructor the table does not hold is a misuse, and one the catalog calls a constructor while the table does not hold it is a defect of the host, the two being assembled from one signature.

### Records, variants, and `openEff`

```text
recordEmpty    : Scope -> Elab Expr
recordExtend   : Scope -> RowKey -> Expr -> Expr -> Elab Expr          value, then the rest
recordSelect   : Scope -> RowKey -> Expr -> Elab Expr
recordRestrict : Scope -> RowKey -> Expr -> Elab Expr
recordUpdate   : Scope -> RowKey -> Expr -> Expr -> Elab Expr          the record, then the value
recordMerge    : Scope -> Expr -> Expr -> Elab Expr
variantInject  : Scope -> RowKey -> Expr -> Elab Expr
variantWeaken  : Scope -> RowKey -> Type -> Expr -> Elab Expr
variantAbsurd  : Scope -> Type -> Expr -> Elab Expr
openEff        : Scope -> Type -> Expr -> Elab Expr                    the row added
```

**Each is claimed at the type its Core rule gives it, read off its parts**: `{}` at `Record ()`, an extension at the rest's record with the field added, a selection at the field, a restriction and an update at the record without the field or with it replaced, a merge at the union of the two rows, an injection at `Variant ( k : τ )` — a variant of one element, widened by `weaken` and by nothing written in `inject` — a weakening at the variant with the element added, an `absurd` at the type it writes, and an `openEff` at the arrow with the row added. **A type the term writes is the synthesizer's to give** — the payload of a `weaken`, the result of an `absurd`, the row of an `openEff` — as a type the scope may use, at `Type` or at `Row Effect`; nothing else is. A key is well-formed for a `Row Type`.

**A row is read at a key by one procedure**, which `select`, `restrict`, `update`, `recordField`, and a switch on keys share: the key is judged well-formed for a `Row Type` first, no solution putting an ill-formed one in a row, so none is waited on; then known with a type as its payload, the key is there, and the row without it is the rest; known with another payload, or absent from a row whose tails are all rigid, it is a misuse; absent from a row with a flexible tail, every flexible tail is waited on.

**A row a term builds is sharp by construction**: `extend` and `weaken` require the key absent from the rest, and `merge` and `openEff` the two rows apart, each introducing the requirement together with the term, a failure where it is already broken. That an `absurd`'s variant is empty is the Core type checker's.

### Effects, handlers, and cells

```text
perform     : Scope -> RowKey -> PayloadView -> OpName -> [Type] -> Expr -> Elab Expr
openHandle  : Scope -> Expr -> RowKey -> PayloadView -> Maybe [ { key, type } ]
                -> Type -> Type -> [ { op, full : Boolean } ]
                -> Elab { binder, returnClause : { variable : Expr, scope }
                        , clauses : [ { typeVariables : [Type], argument : Expr
                                      , continuation : Maybe Expr, scope } ] }
closeHandle : Scope -> Binder -> Expr -> [Expr] -> [Expr] -> Elab Expr     return body, clause bodies, initial values
readCell    : Scope -> RowKey -> Elab Expr
writeCell   : Scope -> RowKey -> Expr -> Elab Expr
```

**The kernel does not follow the ambient row.** A `perform` is given the element it performs on — its key and its payload, `E τ̄` — as a protocol annotation from which the operation's types are read: it is claimed at what the operation resumes with, the effect's parameters and the operation's own type binders instantiated at `τ̄` and at the type arguments given, simultaneously. The element is judged as a row element is, the operation must be one `E` declares, and the type arguments as many as it binds, each at its kind. **That the element is in the row the term stands at is the Core type checker's**, as are the argument's type and, for a handler, the handled computation's row. The operations are read from a table of effects the session holds, built once from the signature its kinding comes from; an effect the kinding knows and the table lacks is a defect of the host.

**A handler is opened with its answer type `β` and its residual row `ρ`**, both types the scope may use, at `Type` and at `Row Effect`, which the types of its continuations need before any clause is built. It is opened with a clause for every operation its effect declares, once each, and closed with a body for each and one initial value per cell, all under one binder. The return clause's scope binds the handled computation's result at what the computation is claimed at; each operation clause's binds the operation's type variables, fresh, its argument, and for a `full` clause its continuation at `τ -{ρ}-> β`, or at `τ -{ρ'}-> β` where the handler owns cells. **Every clause, and the handled computation, jumps to no join point outside**, as an abstraction's body does not; the initial values stand under the handler's `Δ`. A handler owning cells binds a fresh region variable `r`, its operation clauses stand at `ρ' = ( region r ι | ρ )`, and it requires `RegionKey ∉ ρ` together with the term; that neither `β` nor `ρ` mentions `r` is checked where it is closed, both having been given outside the region.

**A region of cells is lexical, and apart from `Δ`.** A scope stands in the region its parent stands in — an abstraction's body included — and only the operation clauses of a handler owning cells stand in that handler's own; its return clause, its handled computation, and its initial values stand outside it. `readCell` and `writeCell` read a cell's type from the region the scope stands in; that the region is in the row the term stands at is the Core type checker's. **A goal asked for in a region carries it**, apart from its site, which an equation or an obligation reads: the root scope of the attempt that runs it stands in the same region, and its target, like every term metavariable, records the region it was created in, so a solution reading or writing a cell that region does not hold is a failure. A term metavariable standing in another's solution is narrowed to the cells the two have in common.

**A term that depends on its region stands only in the region it was built in.** A cell is named by its key alone and means the innermost region's, so a `readCell n` built in one handler's clause and placed in a clause of another handler holding an `n` would read the other's cell. An `Expr` records the region its scope stands in, and a term depends on it where it reads or writes a cell outside every handler owning cells it binds, or holds, outside those handlers' clauses, an unsolved term metavariable created in a region — a goal asked for there, which a solution reading a cell may fill. **A goal asked for in a clause of a handler inside the term is filled in that handler's region, which the term binds itself**, so it is no dependence, solved or not: whether a term may be placed does not turn on how far the scheduler has got. Such a term is refused wherever it is used, and wherever a binder is closed over it, in another region. A term depending on none — pure, or a handler whose cells are all its own — stands anywhere its scope allows.

### Every form of Core⁺, and the request that builds it

| Form | Request |
| --- | --- |
| `EVar`, `EGlobal`, `ELit` | `localVariable`, `globalRef`, `literal` |
| `ELam`, `EApp` | `openLambda` and `closeLambda`, `termApply` |
| `ETyLam`, `ETyApp` | `openTypeAbs` and `closeTypeAbs`, `typeApply` |
| `EConstraintLam`, `EConstraintApp` | `openConstraintAbs` and `closeConstraintAbs`, `constraintApply` |
| `ELet`, `ELetRec` | `openLet` and `closeLet`, `openLetRec` and `closeLetRec` |
| `ELetJoin`, `EJump` | `openJoin` and `closeJoin`, `jump` |
| `ECase` | `openCase` and `closeCase` |
| `XLeaf`, `XGuard`, `XBind` | `leaf`, `guard`, `openBind` and `closeBind` |
| `XSwitchCtor`, `XSwitchLit`, `XSwitchKey` | `openSwitchCtor`, `openSwitchLit`, `openSwitchKey`, each closed by `closeSwitch` |
| `OccScrutinee`, `OccField`, `OccVariantPayload`, `OccRecordField` | `openCase`'s scrutinees, `openSwitchCtor`'s fields, `openSwitchKey`'s payloads, `recordField`; an occurrence is never written by a synthesizer |
| `ERecordEmpty`, `ERecordExtend`, `ERecordSelect`, `ERecordRestrict`, `ERecordUpdate`, `ERecordMerge` | `recordEmpty`, `recordExtend`, `recordSelect`, `recordRestrict`, `recordUpdate`, `recordMerge` |
| `EVariantInject`, `EVariantWeaken`, `EVariantAbsurd` | `variantInject`, `variantWeaken`, `variantAbsurd` |
| `EOpenEff` | `openEff` |
| `EPerform` | `perform` |
| `EHandle`, `XFullClause`, `XFastClause` | `openHandle` and `closeHandle`, a clause `full` or not |
| `EReadCell`, `EWriteCell` | `readCell`, `writeCell` |
| `ETermMeta` | `subgoal`, and nothing else: a term metavariable is made together with the job that fills it |
| `EHole` | none. A typed hole is the Surface elaborator's, for reporting and recovery |

The table is complete, and a test holds it so: it builds every form but `EHole` by these requests alone — a term, a decision tree, an occurrence, and an operation clause — and names the forms by functions matching every constructor, so a form added to Core⁺ is placed on one side or the other before anything compiles. **What a request builds reaches the Core type checker only through the target it is committed to**: a candidate a `transact` discarded leaves no term, name, or reference behind, what does not resolve is reported as a residue, and a term in scope whose claim it does not bear out is built and committed here and refused there.

### The catalog

`lookupGlobal` and `declsWithAttr` read one immutable catalog, assembled before the first job exists ([above](#the-module-environment-is-built-once-before-any-job-exists)).

```text
CatalogEntry = { name : QIdent , sort : value | foreign | constructor
               , scheme : forall k̄. τ⁺ , attributes : [Attribute] }
```

It holds the entries the interfaces of the imported modules publish and every top-level value name this module declares, and it holds the value namespace: what `lookupGlobal` resolves is a name a term can refer to. **The domain is fixed and a provisional scheme sharpens**: a scheme still being inferred carries metavariables, which are zonked against the current `Ψ` at each read, and which names exist never changes. `declsWithAttr` lists the names in ascending order of their qualified names, so that a search over them has one order whatever order the interfaces were read in.

### An attempt held open across requests

A guest synthesizer does not hand the host one action to run: it asks, is answered, and asks again, and the attempt stands open between its requests. **A conversation is that attempt**, driven one request at a time.

```text
Envelope = { conversation : ConversationId , transaction : Maybe TransactionToken }

openAttempt       : PendingId -> Opened Conversation | OpenStopped Attempt
request           : Envelope -> Elab a -> Answered (Returned a | CandidateFailed TransactionToken Diagnostic)
                                         | Finished Attempt
beginTransaction  : Envelope -> Returned TransactionToken
commitTransaction : Envelope -> Returned Unit
finishAttempt     : Envelope -> (acceptance : Elab Unit) -> Attempt

postpone : [Meta] -> Elab a
```

**A conversation attempts a job already taken, and nothing else.** Which job runs, and the fuel a retry spends, stay the scheduler's and the loop's. What the conversation holds — the attempt's checkpoint, the frame, and the transactions open inside it — is the host's control state, and none of it is rolled back: the checkpoints are what a rollback restores. Opening checks what an attempt has always checked before anything is asked, and a job that fails it stops with the state as it was.

**A failure inside a transaction is answered, not raised.** The host rolls back to the innermost transaction's checkpoint, closes it, and answers the request with `CandidateFailed` and the diagnostic, so the synthesizer learns that the candidate did not hold while it still has control, as `transact` returning `Left` tells it; there is no request to abandon a candidate. A failure outside every transaction ends the attempt as rejected. **A postponement and a defect end the attempt wherever they are raised**, rolled back past every open transaction to the attempt's checkpoint, as [above](#transact-catches-a-failure-and-not-a-postponement).

**Every request names where the conversation stands**: the conversation, and the innermost transaction. Both are identified by the host and never reissued — a conversation's identifier is drawn from a counter no rollback restores, and a transaction token from one its conversation holds — so a request arriving late from an attempt rolled back, or from a candidate already closed, names something the host does not hold rather than something that has taken its place. A session that has identified every conversation it can, or a conversation that has issued every token it can, stops rather than wrap around to an identifier a late request may still carry. A token is an identifier and not a handle: it names no object in the arena. A request naming another conversation, or a transaction other than the innermost, and a commit with no transaction open, are defects of the synthesizer.

**Nothing commits before the attempt is finished, and finishing accepts first.** An attempt finished with a transaction open is a defect; one with a binder open is the defect it is wherever an attempt succeeds; and the acceptance given then runs inside the attempt, before it commits, and rolls back with it where it fails, postpones, or breaks. Running one action as an attempt is the one-request conversation finished with nothing to accept, so a runner written as one action and a synthesizer answered request by request reach the same place by construction.

**A synthesizer's `postpone` names metavariables by their handles**, and whether each can wake the goal is decided where the attempt ends, against `Ψ` as its rollback leaves it, and not when the request is made. A metavariable the attempt solved is unsolved again after the rollback, and as good a thing to wait on as any; one the attempt created, one solved before it, and an empty set are the defects [above](#a-defect-in-the-mechanism-is-outside-the-three-outcomes).

### Requests, answers, and commands

**Every kernel operation is a request, and every request is first-order data**: the operation's name and its arguments — handles, views, names, literals — and never a function or a host representation. The requests form one closed sum, split by the part of the kernel they belong to, and one interpreter per part answers them. A request carries no session and no frame: the runner has set both, so a synthesizer cannot answer under another.

```text
KernelRequest = BuildRequest … | TermRequest … | TreeRequest … | RecordRequest …
              | HandlerRequest … | SolveRequest … | ObserveRequest … | ReportRequest …
KernelAnswer  = Unit | Handle | Boolean | TypeView | RowView | KindView | Context | Constraints
              | Decl | Names | Binder | Assumption | ConstraintAbs | LetRec | Join | Case
              | SwitchCtor | SwitchLit | SwitchKey | Handler
Command       = Kernel KernelRequest | BeginTransaction | CommitTransaction | Finish Expr
CommandAnswer = KernelAnswered KernelAnswer | TransactionBegun TransactionToken | TransactionCommitted
```

**An answer is classified by its shape, and not by the request it answers**: operations answering alike share a constructor. **Which shape a request is answered in is one table**, `expectedAnswerShape`, and `throw` and `postpone` are answered in none. Every answer the host gives passes through the interpreter, which holds it to the table, so a script and a guest on the wire are answered alike, and an answer out of shape is a defect of the host on both. The boundary holds raw handles throughout, the class of each checked by the host where it is resolved, which is the one place it is checked.

**A command is what drives a conversation**: a kernel request, the opening and closing of a transaction, or the end of the attempt with a result. The sequence of commands is what a guest on Steam sends and what a record of a conversation holds.

**A synthesizer written in the host is a script over the same requests**: each operation makes the request its name says and takes back only the shape that request is answered in, which the same table fixes, and `transact` is the one form not made of requests — the driver opens a transaction where it starts, commits it where it ends, and resumes the script after it with the diagnostic where a failure is answered inside it, matching the failure to the transaction by its token. The synthesizer is given its goal as a Goal handle, issued as the attempt opens, and ends in the Expr handle it offers. The driver runs it by sending the commands it makes to the dispatcher a guest's commands are answered by. **A script's representation is not the synthesizer's**: the operations and `transact` are all it is given, so it cannot make a request of its own or refuse an answer the host gives.

### Accepting a result

**A result is accepted inside the attempt, before it commits**, where no transaction and no binder is open:

```text
1. the Expr handle resolved
2. built in the goal's root scope — otherwise a defect of the synthesizer
3. its claim unified with the goal's type — a failure, or a postponement where the equation waits
4. the term assigned to the goal's target — a failure where it escapes the target's scope
```

Only in the root scope does what the term may mention agree with where the goal stands. Unifying the claim first is what lets the goal's type be learned from the result, as [above](#what-a-synthesis-job-holds). Whatever acceptance comes to, it comes to inside the attempt, so a result it refuses is rolled back with everything the synthesizer did.

### The trace of a conversation

**A trace is a conversation as the host saw it**, and what a runner in the host and a guest on Steam are compared by:

```text
TraceEvent = AttemptOpened    { conversation , pending , goal : Maybe Goal }
           | AttemptNotOpened { pending , outcome : Attempt }
           | CommandHandled   { conversation , pending , envelope , command , reply }
           | AttemptAbandoned { conversation , pending , outcome : Attempt }
TraceReply = Replied CommandAnswer | FailedCandidate TransactionToken Diagnostic | Ended Attempt
```

Every command is handled by one dispatcher, whoever sends it: a script is run by sending the commands a guest would send, so the two are driven, answered, and recorded alike. An attempt that did not open names no conversation, since one that ran out of identifiers was never given one; an attempt the host ends at its own fault, rather than in reply to a command, is recorded as abandoned. **Only a synthesis attempt is traced**: an equality job sends no command, and a trace is not a history of the scheduler.

**A trace is only appended to**, and kept where no rollback reaches, so a command a rollback undid stays in it. What became of each event is computed from the order of the events rather than written into them:

| Fate | |
| --- | --- |
| kept | part of what the attempt committed |
| rolled back | by a failure in its transaction or in one around it — a transaction committed inside one later rolled back is rolled back — or by the attempt ending without a result |
| pending | the conversation had not ended where the trace ends |
| not run | an attempt that did not open |

**What a trace fixes** is two things, told apart. From one state, one synthesizer gives one trace, one outcome, and one final state, and the commands it recorded, sent again from that state, give all three again, identifiers and handles included. And a retry of a goal sends the same commands as the first attempt up to the first reply that differs — compared with their handles renamed by the order they first appear, a session never issuing a generation twice — and may part from them after it: that reply is the first point where what the attempts observe has changed, which is why the goal was woken. What a retry reproduces is that common prefix, and not the first attempt's commands entire.

**Recording is chosen per session**: a compilation traces nothing, and a test, a comparison of runners, or a debugger turns it on.

### Messages, `throw`, and `warn`

**A synthesizer reports in a message it builds, and the host makes the diagnostic.**

```text
Message       = [ TextPart String | TypePart Type | TermPart Expr | NamePart QIdent ]
FrozenMessage = [ FrozenText String | FrozenType { type : τ⁺ , kind : KindEvidence }
                | FrozenTerm { term : e⁺ , claimed : τ⁺ } | FrozenName QIdent ]
GoalSummary   = { origin , pending : PendingId , synthesizer : SynthRef , expectedType : τ⁺ }

throw : Message -> Elab a        a failure: this candidate, or this goal, does not hold
warn  : Message -> Elab Unit     a warning, which does not end the attempt

SynthesisFailed { goal : GoalSummary , message : FrozenMessage }     the diagnostic a throw makes
Warning         { goal : GoalSummary , message : FrozenMessage }
```

A guest cannot build the host's diagnostic, which names sites and holds Core⁺; what it can say is a message over the handles it holds. **The host freezes the message where it is said**: each handle is resolved then, and what it holds is zonked against `Ψ` as it is then, so a report holds values and never a handle — one a later rollback invalidates leaves no dangling reference, and one whose metavariable is solved later does not change what the report shows. A handle in a message is shown and not built with, so the scope rules do not apply to it: a type a sibling candidate built, or one observed under a binder, may be named; it must still be a valid handle of the running session, of the class its part names. The host adds the goal the running job is about. A report is a synthesizer's, so one made where no goal runs is a defect of the host.

**A warning is part of what an attempt owns.** The journal of warnings is in the tentative state, so one raised by an attempt that fails, postpones, or breaks, or by a candidate a `transact` discards, is rolled back with it, and a goal re-run from its beginning reports each warning once. **What commits is drained once**, where the driver stops — at the end of a loop, or at a submission whose first attempt fails or breaks, which stops with the report a loop stopping there would make — into that report beside the result, and out of the state, by the one finalizer both share. A driver reading it does not read it again, and never has to run a loop, retrying jobs a failure should have stopped short of, only to read it.

**A report is data and not text.** The text an author wrote is kept as written; what the host adds — the goal, a type, a term, the reason a request was refused — is kept structured, so that one report can be shown by whatever shows it. Turning a report into text is the business of the tool showing it, and **text shown to a library's author is self-contained**: it cites no internal document and no stage of the compiler's own development, a defect of a synthesizer included, whose reader is the author of that synthesizer.

The mechanism's own failure is `raiseDiagnostic`, which takes a diagnostic it has built; `throw` is the synthesizer's alone.

**There is no `withFuel` in the kernel.** Two budgets exist, and neither is it: the scheduler's fuel bounds retries and is the loop's, and an instruction budget bounds a guest computation inside one attempt and is Steam's. A bound on a synthesizer's own search — a depth for recursive instance search — is policy, and the guest carries it as an ordinary argument, which keeps it an input rather than hidden state.

### What goes wrong, and whose it is

| | Examples | Outcome | Caught by `transact` |
| --- | --- | --- | --- |
| **program diagnostic** | an equation no substitution satisfies; an obligation broken or rejected; a result escaping its scope; a result whose claim the goal's type refutes; a `throw` | `Failed` | yes |
| **synthesizer defect** | a postponement nothing can wake; a stale handle, one of the wrong class, or one of another session; a builder asked for what cannot be built; a binder left open by an attempt that succeeds, or closed twice; an equation between kinds that cannot meet, or a goal not at `Type`; an occurrence read outside its branch or its `case`, or a constructor the session does not know; an operation its effect does not declare, a handler's clauses naming one twice or missing one, or a cell read where no region holds it; a request naming another conversation, or a transaction other than the innermost, or an attempt finished with a transaction open, or a commit with none open; a result not built in its goal's root scope | `Broke`, naming the synthesizer and the goal | no |
| **host defect** | a `SynthRef` the session has no implementation for; a synthesis job whose target disagrees with its goal; a kernel operation reading a goal the frame does not hold; a catalog scheme ill-formed under what it declares; a name the catalog calls a constructor and the constructor table does not hold; an effect the kinding environment declares and the effect table does not hold; a handler's answer type or residual row mentioning the region variable it binds; a session or a conversation that has issued every identifier it can; a kernel request answered in another shape than its own, or a command in another shape than its own, or a candidate failure answered in a transaction the driver did not open; the mechanism's own invariants | `Broke` | no |

**A `SynthRef` with no implementation is the host's defect and not the program's.** Name resolution resolved it against `Σ` where the goal was written ([above](#what-a-synthesis-goal-carries)), so the name exists; a session unable to run what it names was set up without it.

### What this does not settle

- **How a request reaches Steam**: the transport, the instruction budget, cancellation, and how a guest fault becomes a report belong to the compile-time session protocol ([Open Questions](../99-Open-Questions/01-Open-Questions.md)). The requests themselves are the ones fixed here, whichever runner answers them.
- **Type-level entries in the catalog**, which a derive mechanism over a data type needs. The catalog above holds the value namespace.
- **What becomes of a subgoal left unsolved where a declaration is generalized.** That belongs with the design of inference, as the interleaving of generalization with the scheduler does ([above](#the-dependency-graph-is-settled-after-elaboration-not-before-it)).

## What a compile-time session asks of Steam

Running a guest synthesizer needs more of the interpreter than either of the modes [Abstract Machine](../07-Runtime/01-Abstract-Machine.md) fixes.

| | |
| --- | --- |
| apply a guest value to arguments | a session today is asked for the value a declaration holds, which is a load and not a call |
| carry a handle across | a `Goal`, a `Type`, and an `Expr` pass in both directions without being read |
| serve an `Elab` request | the guest asks, the host answers, and the same attempt continues |
| discard guest execution state | what `postpone` abandons includes the guest's stack |
| bound or cancel a guest computation | fuel bounds the scheduler's retries, so a loop inside one attempt is Steam's to stop |

Discarding rather than keeping is what the restart reading buys: nothing has to hold a guest computation once its attempt is abandoned. **The protocol itself is not settled here** and is recorded with the open questions ([Open Questions](../99-Open-Questions/01-Open-Questions.md)); what this document fixes is what it is obliged to carry.

## The bootstrap

A synthesizer written in Stella has to be compiled by an elaborator, and the elaborator that compiles it must therefore not need one. The circle is cut by layers rather than by an exception.

```text
1. a kernel elaborator in the host, using no class, no macro, and no synthesis
2. with it, compile Stella.Elab and a small guest synthesizer
3. run that synthesizer on Steam, against the host's mechanism
4. build the standard type class resolver on top
```

Layer 1 is Phase A, and it is a complete elaborator for the class-free subset rather than a stepping stone to be thrown away. Layer 2 requires only that the library's own source use no class and no macro.

**The first guest demonstration need not be a resolver.** One hand-written Typed Core `f` that solves one goal establishes that the cycle is cut; everything after that is policy, and policy is the part the guest was chosen for.

## Regression tests

Each is a case where a plausible implementation gives the wrong answer, and each is worth writing before the code it concerns.

| Input | Required outcome |
| --- | --- |
| A goal that creates metavariables, emits constraints, and raises a warning, then postpones | None of the three survives. A warning that survived would be reported once per attempt |
| The same goal, run a second time | It creates the same metavariables and emits the same constraints, and neither is duplicated. Reading a counter that the rollback left alone is what makes a second run differ |
| A `postpone` naming a metavariable the attempt itself created | A session-level defect naming the synthesizer, and no diagnostic. Registering the job blocks it on an assignment nothing can make, and quiescence then reports a name `Ψ` does not hold |
| A `postpone` naming the empty set, or a metavariable already solved | The same defect. Neither can wake a job, and the second is a type that was not zonked |
| The same `postpone`, raised inside a `transact` | Still a defect, and the checkpoint does not catch it. Caught there, the search takes the next candidate and the synthesizer's contract violation is reported nowhere |
| A stuck row equation among whose flexible tails is one the attempt created | Registered under the metavariables the attempt assigned that `Ψ` still holds unsolved. Registering under the fresh tail blocks the job on an assignment nothing can make, and refusing the postponement rejects an equation a later solution would decide |
| The same, with a candidate discarded by a `transact` in between | That candidate's assignments are none of the dependencies. A write set an inner rollback left standing has work the search rejected decide when the goal is woken |
| A `postpone` inside a `transact` | It rolls that checkpoint back and propagates to the attempt root. A `transact` returning `Left` has a resolver reject a candidate for lack of information and commit to the next |
| A `throw` inside a `transact` | Caught there, which is what `Either Diagnostic a` says |
| A unification driven against its contract inside a `transact` — a metavariable `Ψ` does not hold, one it holds solved, a journal nobody has acted on | A defect, and not caught. Read as a failure it sends the search to the next candidate with the defect reported nowhere; read as a type error it blames a program nothing is wrong with |
| A row constraint whose subject zonks to something that is not a row | The same. Only a row metavariable is named by a row constraint, so nothing the author wrote produces one |
| A `PendingUnify` whose substitution has to preserve a Lacks assumed at another site | Decided against the facts of the site that assumed it, whatever site the equation stands at. The obligation carries its own context, so nothing is decided by the facts that happen to be at hand |
| A `PendingUnify` woken far from where it was written | Creates its kind metavariables under the kind variables in scope at its own site. What it needs the snapshot for is that and the place a failure is reported |
| A handle a rollback invalidated, presented again | Reported as a defect in the synthesizer. Resolving it to whatever occupies that place now is how a guest cache corrupts a later attempt |
| A different object allocated into a slot a rollback freed, and the old handle presented | Still rejected. A generation counter restored with the rest of the attempt would stamp the new object with the number the old handle carries |
| An `assign` inside an attempt that goes on to postpone | The substitution and the wakeups it made are both rolled back, and the jobs it woke are waiting where they were. Publishing at the `assign` leaves a job on the ready queue for an assignment that was undone |
| A stuck equation one of whose assignments broke an obligation | A **failure**, and no registration. Waiting on information repairs nothing about a constraint that is already broken, and a job registered instead is woken to fail later or not at all |
| Two equations in one attempt, the second reaching what the first assigned | Both solved. An assignment is drained where it is acted on, so what the second is given holds none nobody has acted on; a unification refuses one that does |
| A goal awaiting `?a` and `?b`, with `?a` assigned | It wakes once, and it is registered under `?b` no longer. Leaving the entry under `?b` runs a job that is already on the ready queue |
| The same goal, postponing again on `?b` alone | It waits on `?b` and on nothing else. A dependency set accumulated across attempts would wake it on an assignment it no longer cares about |
| A goal woken far from where it was created | `localContext` and `localConstraints` answer with the goal's own site. Answering with the elaborator's current position is what the snapshot exists to prevent |
| A goal created under one binding group and woken while a later one is being elaborated | `declsWithAttr` answers with what the first attempt saw. A catalog that grew with the fold would have a resolver's candidates, and so coherence, turn on the schedule |
| A synthesizer inserting a reference to a declaration standing later in the text | The groups are ordered over the final graph, so that reference is backwards in the Core emitted. An order computed before elaboration leaves a `nonrec` referring forwards, which the Core type checker rejects |
| A candidate that builds a dictionary reference and is then discarded | Contributes no edge. The graph is read off the committed right-hand sides, so a reference a rollback removed is in none of them; an edge recorded as elaboration went would survive, none of D40's list covering one |
| A generated reference closing a cycle between two declarations | Treated as any other cycle: one `rec` group, admissible only under guardedness (D14) |
| A reference to an imported global | A sink, and no edge. Treating one as a node puts a module's imports into its own dependency order |
| Quiescence, with a job woken and not yet postponed again | Its `awaiting` is empty and it names nothing. A set left standing from before the wake names a metavariable that is no longer why anything waits |
| An assignment reaching a blocked goal | The goal is on the ready queue and has not run. Running it inside `assign` opens an attempt within an attempt |
| A synthesizer that succeeds on its second attempt | The term that reaches Core is the second attempt's, and the first attempt's metavariables are absent from `Ψ` |
| Fuel, across a postpone | Not restored. Restoring it leaves a goal that postpones unconditionally running forever |
| One scripted synthesizer, run by the host runner and by the guest Steam runner | The same result, the same diagnostics, and the same sequence of requests. This is what makes the host implementation a reference rather than a second design |
| A synthesizer holding state between attempts | Out of contract. The host cannot detect it; what the test establishes is that the reference synthesizer does not |
