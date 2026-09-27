# Bytecode and the `.dmo` module object

Bytecode is one lowering of middle-end IR (ANF), beside any backend including JS
and WebAssembly. Its target is *Steam*, an abstract machine Stella owns.

`lower` takes an ANF module and produces a **`.dmo` file**, a module object
holding the module's tables and the code of its functions.

The machine that executes a `.dmo` is specified separately
([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)). This document fixes
the instruction set and the container, and states what a consumer owes them.

## A `.dmo` is the artefact others build on

ANF is an in-memory representation, and a compiler that goes on to generate
JavaScript or Wasm need not write anything to disk between the two. **A `.dmo`
is what a consumer outside this compiler reads**, and the format is fixed here
for that reason rather than for the machine's convenience.

PureScript publishes `corefn.json`, and several backends outside its compiler
consume it. Stella publishes the lowered form instead, and what that buys a
consumer is the work already done: erasure, A-normal form, spine folding,
explicit closures with their capture lists, and decision trees whose branches no
longer overlap. A consumer of Typed Core would have to perform every one of
those before generating code, and each is a place to differ from the reference
compiler.

| Consumer | Reads |
| --- | --- |
| The virtual machine | A `.dmo` |
| The JavaScript and Wasm backends | Mid IR, or a `.dmo`; both are available and neither is fixed here |
| A backend outside this compiler | A `.dmo` |

The two routes for the first-class backends are a question of what a build is
convenient to organize — a single command generating JavaScript without an
intermediate file is the likely shape — and not one the format answers. What the
format does settle is that a `.dmo` is enough on its own.

### The interface file

A `.dmo` is one of a pair. Beside it stands a **`.dmi` file**, the interface of
the same module, and the two together are what the compiler writes.

| File | Holds |
| --- | --- |
| `.dmi` | A module's exported types, and what a module downstream of it needs in order to optimize across the boundary — the bodies of functions eligible for inlining among them |
| `.dmo` | The module's tables and the code of its functions |

**What a `.dmi` carries is settled when the optimizer is written**, its content
being determined by what optimization across a module boundary turns out to
require. What is fixed already is the split: compiling a module reads the `.dmi`
of each module it imports, and reads a `.dmo` only to link or to execute.

One thing in this document depends on that file already. `callk` names a
top-level value together with its **definitional arity**, which is the number of
leading lambdas its right-hand side has and not something its type says
([Translation](../04-MiddleEnd/02-Translation.md)); for an imported value the
`.dmi` is where it comes from. Where it is absent the call is a `callu`, which is
correct for every callee, so a `.dmi` that does not yet publish arity costs
sharpness and nothing else.

**That much of the file is therefore fixed**, and [Interface](03-Interface.md)
fixes it: what a `.dmi` holds today is the definitional arity of each value a
module exports, and what it holds tomorrow is what the optimizer asks for.

### What it therefore carries

**The meaning of every instruction is fixed by this document**, in terms of
[Semantics](../03-Typed-Core/06-Semantics.md), and not by what the machine
happens to do. A consumer that is not the machine reads the same specification.

**Representation types reach the file.** A backend choosing a Wasm GC struct per
data type, or an unboxed integer, needs to know which class of value a register
holds, and `Rep` is what says so ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)).
Dropping it would leave a consumer with a uniform representation and no way to
improve on it.

**Debug information is worth writing even though it may be stripped.** Source
spans are what a consumer emits a source map from, and no other section carries
them.

### What it does not carry

Core's types, rows, effect rows, and constraints are gone, and `Rep` is what
survives of them. A consumer wanting to optimize on the strength of a row — a
record whose fields are all known, an effect row that turns out empty — has to
read Typed Core instead.

That is the trade the format makes: **lowered and ready to generate code from,
rather than typed and general.** Type-directed work belongs before this stage,
where the types still exist.

## Semi-linearized form

Code is linear within a straight run of instructions and **structured above
it**. A function is not one instruction array. It is a tree of instruction
sequences, whose edges name their destinations.

```text
Function ::= { nparams   : Int
             , regs      : [Rep]     one per register; the first nparams are the parameters
             , captures  : [Rep]     one per capture slot
             , joins     : [Join]
             , body      : Node
             }

Join     ::= { name : JoinName, params : [Reg], body : Node }

Node     ::= { code : [Instr], tail : Tail }
```

A `Node` is a straight run of instructions ending in exactly one `Tail`. A
`Tail` either leaves the function, jumps to a join point, or **dispatches into
further `Node`s held inline**.

Two things are therefore not flattened, and both are deliberate.

**A transfer to a join point names its destination; it is never an offset.** A
jump carries the name, which the machine resolves when it loads the module.

**A decision tree stays a decision tree.** The dispatches of a Core `case` nest
here as they nest in Core, each branch holding its own instruction sequence
rather than standing as an edge to a block somewhere else in the function.

### Why the structure survives

What a consumer must do afterwards is the reason. Offsets into a flat array
discard the loop and branch structure that a language with `if`, `switch`, and
nested blocks needs, and recovering it means running a **relooper** — an
algorithm that reconstructs structured control flow from an arbitrary control
flow graph. It is substantial to write, and what it recovers is worse than what
was thrown away.

A backend handed this form walks it instead. A nested dispatch becomes a nested
`switch`, a join point becomes a label or a local function, and nothing has to
be reconstructed because nothing was lost. **That holds whether such a backend
reads Mid IR or reads a `.dmo`**, and keeping it true of the `.dmo` is what
leaves the second route open.

The cost falls on the machine, which resolves names and walks a tree rather than
incrementing a program counter. For a first evaluator that is the right side to
pay on, and it is the only side that a relooper could not be written for.

### Join points

**A join point names the registers its parameters occupy, and a jump supplies
them.** A Mid IR `letjoin` becomes a `Join` and a `jump` becomes a `JMP`
carrying arguments. Nothing else is needed to express what a join point is, and
the machine reconstructs no data flow across a transfer.

The registers are part of the file. Lowering assigns them, and a `JMP` writes
its arguments into them, so a consumer that did not know which they were could
not perform the transfer at all — the `Join` carries `params` for that reason
rather than a count.

The join table is flat. Join names are unique within a function, and Mid IR has
already established that every `jump` names one in scope and stands in tail
position, so nesting the table would re-state a property that holds already.

## Registers

A function has a flat register file, indexed from 0. Parameters occupy the first
`nparams`, and a join point's parameters occupy slots the lowering assigns.
Every other Mid IR local takes a slot of its own.

Mid IR names each local once, so the naive assignment of one slot per local is
already correct and lowering performs no register allocation. Reusing slots is a
later concern and changes nothing above this line.

**Each slot carries the `Rep` of what it holds**, which is the `Rep` Mid IR
wrote on the binding ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)). A consumer
choosing a representation reads it there; one keeping a uniform representation
ignores it. `Rep Data T` names a type constructor, whose constructors are found
in the `CTORS` table of whichever module declares it — this one, or one it
imports.

Reusing a slot later would mean a slot holding two classes of value over its
lifetime, so whatever does it records a `Rep` per definition rather than per
slot. Nothing in this document does.

A `JMP` writes its arguments into the join point's parameter slots. Where an
argument register is itself a parameter slot of that join point, the writes are
performed as a parallel move rather than in sequence.

Captures are not registers. `CAPT` reads one from the closure of the current
activation.

## Instructions

Operands are written `d` for a destination register, `s` for a source register,
and `r…` for a vector of source registers. An index into a module table is
written by the name of the table.

### Loading

| Instruction | Effect |
| --- | --- |
| `LOADK d, const` | The literal at `const` in the constant pool |
| `LOADG d, global` | The value stored in a global slot |
| `LOADC d, ctor` | The constructor `ctor`, whose arity is 0 |
| `MOVE d, s` | |
| `CAPT d, i` | Capture `i` of the current activation's closure |

### Allocation and calls

| Instruction | Effect |
| --- | --- |
| `CLOS d, func, n, r…` | A closure over `func` with `n` captures |
| `CLOSN d, func, n` | A closure over `func` with `n` capture slots, unfilled |
| `SETCAP d, i, s` | Fill capture slot `i` of the closure in `d` |
| `PAP d, callee, n, r…` | A partial application; `n` is below the callee's arity |
| `CTOR d, ctor, n, r…` | A saturated constructor; `n` is its arity |
| `CALLK d, global, n, r…` | Call the closure in a global slot; `n` is its arity |
| `CALLU d, s, n, r…` | Call the value in `s` with `n` arguments |
| `PRIM d, prim, n, r…` | Carry out a `Base` ABI operation. **May fault** |
| `FFI d, foreign, n, r…` | Call a foreign implementation; `n` is its arity. **May fault** |

`CLOSN` and `SETCAP` exist for a recursive group, whose members capture one
another: every closure of the group is allocated before any capture list is
filled. `CLOS` is the whole of the non-recursive case.

`CALLU` is where under- and over-application are resolved. Applying a `PAP`
below its arity yields another `PAP`; applying one that saturates it performs
the call; supplying more arguments than a callee takes calls it and applies the
rest to the result — left to right, the arguments being values already.
**Applying a continuation is an ordinary `CALLU`**, a continuation being an
ordinary function value ([Semantics](../03-Typed-Core/06-Semantics.md)).

**An argument vector is in source order, and every register in it already holds
a value.** Stella evaluates an application's argument before its function, so a
spine is evaluated right to left (D35) — but that happened in Mid IR, where each
argument became a binding of its own in that order. By the time a call
instruction runs there is nothing left to evaluate and nothing to reorder, so
`r…` reads as the call reads.

### Data, records, and variants

| Instruction | Effect |
| --- | --- |
| `FIELD d, s, ctor, j` | The `j`-th field of the constructor value in `s` |
| `RNEW d` | The empty record |
| `REXT d, key, s_v, s_r` | Extend the record in `s_r` at `key` with the value in `s_v` |
| `RSEL d, key, s` | |
| `RRES d, key, s` | Restrict |
| `RUPD d, key, s_r, s_v` | Update |
| `RMRG d, s1, s2` | Merge two records |
| `VINJ d, key, s` | Inject into a variant at `key` |
| `VPAY d, key, s` | The payload the variant in `s` carries at `key` |
| `VABS d, s` | Unreachable; the operand's type is uninhabited |

`VABS` has no defined result. Core's `absurd` has no reduction rule because its
argument has type `Variant ()`, so the instruction is never reached; the machine
treats reaching it as an internal error rather than as a fault.

### Effects

| Instruction | Effect |
| --- | --- |
| `PERF d, key, op, s` | Perform `op` on the element keyed `key` with the argument in `s` |
| `HNDL d, handler, r_body, r_ret, n, r…, m, c…` | Open the handler's region, install the handler, and call the body; `d` receives what the return clause gives |
| `CGET d, key` | The cell keyed `key` of the innermost region declaring it |
| `CSET d, key, s` | Replace what that cell holds with the value in `s`; `d` receives `Prim.Unit` |

`PERF` is not a `Tail`. Where the clause found is `fast`, control returns to
the instruction after it with the clause's value in `d`; where it is `full`,
control does not return to it at all unless the clause resumes the continuation,
and the resumed value arrives in `d`.

**`HNDL` is an ordinary instruction and not a `Tail`**, because the value of a
`handle` is the value of a computation. It supplies its functions in registers:
`r_body` holds the body, `r_ret` the return clause, and `r…` the operation
clauses in the order the handler table lists them. Each is built by an ordinary
`CLOS`, so nothing here carries a capture list of its own. `c…` holds the initial
value of each cell of the handler's region, one per key of its `cells` and in
that order, and is empty for a handler declaring none.

Installing the marker and calling the body is one step. **The marker stands
between the calling activation and the body's**, which is what lets the return
clause's value arrive in `d` by the ordinary route a call's value arrives by.

**The marker `HNDL` pushes is an owner**, and it owns the frame directly below
it. A marker a continuation reinstalls is a **reinstatement** and owns nothing;
the two differ in what finishing does and in nothing else, and neither is written
in the file — an owner is what installing produces and a reinstatement what
applying a continuation produces.

**The region frame stands below the marker**, the whole of what places the cells
where the clauses reach them and the handled computation does not: a clause runs
where the marker has been popped or is still installed, and either way the frame
is below it, while the body runs above it. Which continuations carry the frame
follows from the same placement and needs no rule of its own.

`CGET` and `CSET` walk the continuation from the top for the first frame
declaring the key, as `PERF` walks it for a marker. A write replaces what that
frame holds and has no result of its own, so `d` takes the machine's `Prim.Unit`;
reading back what was just set takes a `CGET`.

### Tails

A `Tail` ends a `Node`. `node` below stands for a `Node` held **inline**, which
is what keeps a decision tree a tree; `join` stands for a join point's name.

| Tail | Effect |
| --- | --- |
| `RET s` | Return the value in `s` |
| `TAILK global, n, r…` | A tail call to a global |
| `TAILU s, n, r…` | A tail call to a value |
| `TAILFFI foreign, n, r…` | A tail call to a foreign. **May fault** |
| `JMP join, n, r…` | Enter a join point with arguments |
| `BRIF s, node, node` | Branch on a boolean |
| `BRC s, [(ctor, node)…], node?` | Dispatch on a constructor tag |
| `BRL s, [(const, node)…], node` | Dispatch on a literal |
| `BRK s, [(key, node)…], node?` | Dispatch on the key a variant carries |
| `TAILHNDL handler, r_body, r_ret, n, r…, m, c…` | The same as `HNDL`, in tail position |

**A branch is a `Node` and not a name**, so the instructions a branch needs
before its own dispatch stand inside it. This is where the projections of a
decision tree land: the `FIELD` reading a constructor's field sits in the branch
that selected that constructor, which is the only place the field exists
([Translation](../04-MiddleEnd/02-Translation.md)).

Sharing a branch between several leaves is what a join point is for: such a
branch is a `Join`, and the leaves that share it end in `JMP`. Lowering
introduces none of its own, Mid IR's join points being exactly the ones Core
wrote.

`BRL` always carries a default and the other two carry one unless their cases
exhaust, which Mid IR already guarantees. **The machine performs no totality
check**: the Core type checker established local totality and Mid IR preserved
it.

A Mid IR `tail` of a computation that is not a call — a `ctor`, a `closure`, a
record operation — lowers to that instruction followed by `RET`. What has a
`Tail` of its own is a transfer of control that a backend must be told not to
push a frame for: a call, and a `handle`, which calls its body.

### `RET`, an installed handler, and an open region

**`RET` returns from the current activation, and that is the whole of the rule.**
It has no case for a handler and none for a region.

What a value does on its way down is decided by what it reaches. `HNDL` pushes a
frame and a marker and then calls the body, so both stand **below** the body's
activation, and returning from the body reaches the marker first.

| The value reaches | What the machine does |
| --- | --- |
| an **owner** marker | pops the marker and the frame it owns, then calls the return clause with the value; that clause's result goes on down |
| a **reinstatement** marker | pops the marker alone, then calls the return clause with the value; the frame the marker stood in is untouched |
| a **frame** whose marker is gone | pops the frame and carries the value on down |

The three are the reduction rules for a value read as machine steps, and the
distinction they turn on is the one the markers carry.

**An owner finishing closes the region, so its return clause runs outside it.**
This is `region [r] θ in ( handleO v with h ) → e_r[x := v]`, which is one step
in Core for the same reason: there is no moment at which an answer and a cell
both exist, and a return clause that could read a cell is what would make a
handler with cells a state monad in disguise (D36). Where the handler declares no
region there is no frame to pop and the rule reads as
`handle v with h → e_r[x := v]`.

**A reinstatement finishing leaves the region open**, the frame it stands in being
another activation's to close — the `handle` that opened it, or the `full` clause
that holds the continuation where that `handle`'s own marker was captured. This is
`handleI v with h`, whose return clause runs within the region and whose value
goes to whoever applied the continuation.

**A `full` clause's answer reaches the frame directly.** Splitting the
continuation at the marker took the marker and left the frame, so the clause runs
with the cells still reachable — which is what lets it copy one into the answer —
and its value then reaches a frame no marker owns. This is `region [r] θ in v → v`:
the region closes with no return clause, that clause having run already or not at
all.

`HNDL` therefore needs no matching instruction to close what it opened. A
handler's extent is the part of the continuation above its marker, and the table
above is the whole of what closes a marker and a frame: a marker goes where a
value reaches it, and a frame where its own owner does or where a value reaches
it with that owner gone.

**A tail call inside the body does not disturb any of this.** `TAILK` and its
kin replace the body's activation, and the marker is not in that activation, so
the path from wherever control ends up back to the marker and its return clause
is the same one. The same holds of a tail call inside a clause.

## A worked function

The `sum` of [Translation](../04-MiddleEnd/02-Translation.md), lowered:

```text
function Main.sum   nparams 1   captures []   joins []
  regs  [ Data Main.List, Int, Data Main.List, Int, Int, Val ]

  body
    tail  BRC r0, [ Main.Nil -> A, Main.Cons -> B ]      no default; the two exhaust

      A   code  LOADK r4, #0
          tail  RET r4

      B   code  FIELD r1, r0, Main.Cons, 0
                FIELD r2, r0, Main.Cons, 1
                CALLK r3, Main.sum, 1, [r2]
                PRIM  r5, IntAdd, 2, [r1, r3]
          tail  RET r5
```

`r0` is the parameter and `r1` to `r3` are the three Mid IR locals of the `Cons`
branch, the numbering of a register being the numbering of the local it stands
for. `r4` and `r5` are slots lowering introduced for itself, which is why they
come after every local: an atom that is a literal has to reach a register before
an instruction can take it, and a computation in tail position that is not a
call takes one on the way to returning. Slots are never shared, not even between
branches that cannot both run, there being no register allocation here.

`r5` carries `Val` because a Mid IR `tail` holds no `Rep`: a call returns its
value and wants none, and the class of the register a non-call takes there has
nowhere to come from ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)).

`A` and `B` are not blocks the function holds and jumps to. They are the two
branches of the `BRC`, written out here because a nested `Node` does not fit on
one line, and a JavaScript backend emits them as the two arms of a `switch`.

The rest of the function follows from that shape. The `FIELD`s stand inside `B`
and nowhere else, that being the only branch in which the fields exist. The
recursive `CALLK` is an ordinary call because its value is an argument. The
addition is a `PRIM` followed by `RET` rather than a tail call: `Base.Int.add`
is classified as the operation `IntAdd`, and an operation is not a transfer of
control, so only a call has a `Tail` of its own. Nothing is shared between the
branches, so the function has no join points at all.

A shared branch is what produces one. Where a decision tree reaches one body from
two leaves, Core lifts that body into a `letjoin`, and the two leaves become
`JMP`s naming it.

```text
function …   joins [ alt0 params [r1] ]

  body
    tail  BRC r0, [ Main.Nil  -> A, Main.Cons -> B ]

      A   code  LOADK r3, #0
          tail  JMP alt0, 1, [r3]

      B   code  FIELD r2, r0, Main.Cons, 0
          tail  JMP alt0, 1, [r2]

  join alt0 params [r1]
    …
```

The body is held once, and the name is what both leaves carry. `r1` is where a
`JMP` writes its argument, and the `Join` names it so that a consumer can
perform the transfer at all.

It takes `r1` because **a join point's parameter is a Mid IR local, numbered
where the `letjoin` stands**. The `letjoin` encloses the dispatch, so its
parameter is numbered before anything the branches bind — here before `r2`, the
field the `Cons` branch projects — and every local is numbered before `r3`, a
slot lowering introduced for itself.

## Handlers, `perform`, and continuations

The machine holds a **continuation**: a stack whose entries are activations,
handler markers, and region frames. `HNDL` pushes a frame holding the handler's
cell keys paired with their initial values, where it declares any, and then a
marker carrying the handler's key, the forms and closures of its clauses, and the
return clause.

`PERF key, op` walks the continuation from the top for the first marker whose
key is `key`. The innermost wins, which is what makes handlers deep, and
handlers of one key may nest — a function that handles an effect internally is
pure to its caller, so calling it under an outer handler of the same effect puts
two markers on the stack at once ([Semantics](../03-Typed-Core/06-Semantics.md)).

| The clause found | What the machine does |
| --- | --- |
| `fast` | Call the clause closure with the argument, leaving the continuation as it is. The clause returns to the `PERF` site with its value |
| `full` | Split the continuation at that marker, inclusive. Make the removed segment a continuation value. Call the clause closure with the argument and that value, its result returning to what remains below the marker |

Nothing here consults an effect row, a type, or an operation's signature. A key
is compared for equality and an operation is found by name among the clauses of
the one handler the key selected.

### Cells

A region frame is part of the continuation and **not a store**. `CGET` and `CSET`
find the innermost frame declaring the key, and a write replaces what that frame
holds.

**A frame leaves in three ways and no others**: its owner marker finishes, which
pops the two together; a value reaches it with its owner gone, which is a `full`
clause's answer arriving; or a fault discards the continuation entire. A
reinstatement finishing is not among them — the frame it stands in belongs to
another activation, which is still owed the rest of its own computation.

Which continuations carry the cells follows from where the capturing marker
stands, and the machine implements no rule for it beyond the ones above.

| The capturing marker | The frame | What two applications see |
| --- | --- | --- |
| **outside** the region | inside the captured segment | each begins from the values the frame held at the capture |
| the handler **owning** the region | below the marker, so outside the segment | both reach the one frame, and a write under the first is visible to the second |

The first row is what a shared mutable location would get wrong: two applications
would reach one cell whatever the composition order, and a program's result would
turn on a placement the semantics settles (D36). A machine that copies the
captured segment at each application satisfies it by copying the frame with it.

The second row is the semantics and not a concession. A handler's cells are its
state across the operations it handles, and a `full` clause of that handler
resuming twice is resuming its own computation twice.

### Resuming more than once

**A continuation may be applied any number of times, and each application
proceeds from the state that was captured** (D33). Two applications of one
continuation share no register file and no handler marker, and the second begins
from the captured state exactly as the first did.

**Each application returns to whoever applied it.** The captured segment ends at
the marker, and the value the return clause produces there goes to the
`CALLU` that applied the continuation — not to the `HNDL` that first installed
the handler. A continuation is a function value, and this is what being one
means.

**The marker at the bottom of a re-pushed segment is a reinstatement**, whichever
kind the marker captured there was. It owns no frame, so finishing pops it alone.
The frame it stands in, where there is one, is the one the original `handle`
opened: it stayed behind when the segment was split, and where the handler
capturing it was the frame's own owner, what stands between the two is the `full`
clause that holds the continuation. Every other marker in the segment returns as
what it was, an owner among them carrying the frame it owns along with it.

What is captured is a run of **whole activations**, from the one performing the
operation up to and including the marker, each with its registers and the point
it resumes at. None of them is a fragment: the body of a `handle` is an
activation of its own, so no activation straddles the marker.

Copying the segment at each application is the straightforward way to provide
this, and it is what a register machine with mutable frames must do — re-pushing
the frames it captured would have the first application write over the state the
second needs. **The requirement is the behaviour, not the mechanism**: immutable
frames shared between applications satisfy it equally, and D33 fixes only that
the machine provides it.

The cost falls on `full` clauses alone. A `fast` clause captures nothing (D28),
so the common case of translating one operation into another pays none of it.

**This makes the virtual machine conforming with respect to D18**, where the
v0.1 JavaScript and Wasm backends are not: the reference semantics is multi-shot
and no backend that raises an error on a second resumption reproduces it
([Semantics](../03-Typed-Core/06-Semantics.md)).

What that buys the test suite is narrower than being the evaluator the
properties are stated over. The machine is **a second evaluator to compare the
Core evaluator against** — one program run both ways, giving the same value and
the same sequence of observable effects — and it is what **exercises a program
that resumes a continuation more than once**, which the web backends cannot run
at all. Preservation and erasure are stated over Typed Core and its erasure, and
a machine state carries no types, so those two stay with the Core evaluator
([Implementation Plan](../01-Introduction/04-Implementation-Plan.md)).

## Faults

A foreign implementation may fail, and so may a `Base` ABI operation: the failure
is a **fault** — not an effect, intercepted by no handler, absent from every row,
and distinct from the `Partial` effect
([Semantics](../03-Typed-Core/06-Semantics.md)).

A fault discards the whole continuation, handler markers included, and ends
execution. The machine reports it; nothing in the bytecode catches it, and the
instructions that produce one are `FFI`, `TAILFFI`, and `PRIM`.

**Which entries fault, and on which inputs, belongs to the ABI specification**
and is not something a lowering decides ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).
The ABI fixes one observable meaning for every backend, so the question is
settled once for all of them rather than per target.

## Executing an `IO` is outside the machine's reduction

Reduction halts once it has constructed a value of type `IO` (D25), and
executing one belongs to the runtime ABI. To the bytecode an `IO` value is an
opaque value like any other: it is produced by an `FFI`, carried by whatever
carries it, and consumed by another `FFI`. No instruction examines one.

Running a program end to end therefore requires the machine to implement the
runtime ABI beside the instruction set: `Base.IO.pure`, `Base.IO.bind`, the
native leaf actions, and the invocation of `main`
([Prim and Base](../06-Modules/02-Prim-and-Base.md)). That is an obligation on
the machine as a backend, graded by the profile it claims, and not part of this
instruction set.

## The `.dmo` container

```text
header   magic "DMO\0"  |  format version  |  flags  |  ABI version

section  id | length | payload           repeated to the end of the file
```

**What each section holds is here and the bytes that carry it are in
[Encoding](02-Encoding.md)**, which fixes the encoding of a primitive, the id and
framing of a section, the tag of every form, and the opcode of every instruction.
Nothing there adds to what a `.dmo` holds.

| Section | Holds |
| --- | --- |
| `STRINGS` | Every string the other sections refer to, UTF-8 |
| `MODULE` | The name of the module itself, which no other section carries |
| `CONSTANTS` | The literal pool: tagged `Int`, `Number`, `String`, `Char`, and `Boolean` values |
| `KEYS` | Row keys: a tag and, for three of the four, a string or an integer |
| `OPS` | Operation names |
| `IMPORTS` | The modules this one depends on |
| `CTORS` | Per constructor: name, owning type, tag, arity, and whether its type is a `newtype` |
| `EFFECTS` | Per effect: name and the operations it declares |
| `FOREIGNS` | Per foreign: qualified name and arity |
| `CTORREFS`, `FOREIGNREFS`, `GLOBALREFS` | The constructors, foreigns, and top-level values this module's **code names** — its own and those of the modules it imports. Every `ctor`, `foreign`, and `global` operand is an index into one of these |
| `CALLEES` | Per partial-application target: a value, a foreign, or a constructor with its qualified name, or an operation. **An operation carries no name**: what it realizes comes from the ABI version, so no entry can name one operation and an unrelated entry |
| `PRIMS` | The operations the module carries out, saturated or waiting in a partial application. It holds the operations alone: **what each realizes is derived from the ABI version** the header carries |
| `HANDLERS` | Per handler: its key, the keys of the cells its region declares, and per clause the operation and its form |
| `FUNCTIONS` | Per function: `nparams`, the `Rep` of each register and of each capture slot, its join points with the registers each takes its arguments in, and its body |
| `GLOBALS` | Per top-level value: its name, whether it is run or installed, and which function |
| `EXPORTS` | The value names this module exports, its globals and its foreigns alike |
| `DEBUG` | Source spans, function names, and local names, keyed by function index and register. Translation produces this table beside the module and lowering carries it across, rewriting the keys ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)) |

`DEBUG` is the one section a reader may skip. Everything else is required, and a
machine rejects a file missing any of it rather than guessing.

What it can hold is what has an identity in Mid IR — a function, a local. A span
per instruction is not among them ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)).

**Keys and operation names are interned on load.** They are compared for
equality and for nothing else, so the machine replaces each with an integer
identifying it across every module it has loaded.

**A region key is not among them.** `KEYS` holds the keys terms carry, and no
erased term carries a region's: a handler keeps the key of the element it removes,
its cells keep their own, and `CGET` and `CSET` name those (D36).

### What a module declares, and what its code names

The two are not the same set, and the container keeps them apart.

`CTORS`, `EFFECTS`, `FOREIGNS`, and `GLOBALS` are what **this module declares**,
with the tag, the arity, and the rest that only a declaration carries.
`CTORREFS`, `FOREIGNREFS`, and `GLOBALREFS` are what **its code names**, which
includes what it imports: a module summing a list calls `Base.Int.add`, whose
arity is recorded where that foreign is declared and not here.

**A reference is a qualified name and is resolved where the module it belongs to
is loaded.** Nothing is resolved against a closed set of modules, which is what
lets modules arrive one at a time. It is also why a `CALLEES` entry carries no
arity: a partial application's callee may belong to another module, and the
arity is that module's to state.

**A join point's name is resolved on load too**, to whatever the consumer reaches
a `Join` by — a label where code is generated, a table built when the module is
loaded where the code is interpreted. A name is what the file holds so that the
structure survives the format, and what holding one must not cost is a search of
the function's join points at each transfer. **A name stands over one join point
of a function**, so a file writing two under one name is refused rather than
resolved to whichever came first.

**A key, an operation, and a constructor are resolved on load as well.** A `KEYS`,
`OPS`, or `CTORS` index is the file's own: two modules may hold one key at
different indices, and a record one of them built is selected from by the other.
So what a consumer compares while running is an identity it assigned as it loaded
— one per key, one per operation name, and one per constructor across everything
loaded — and never an index of a file. Nothing less makes `RSEL`, `BRK`, `PERF`,
`CGET`, and `BRC` work across a module boundary.

**A loader verifies a reference before it resolves one.** A qualified name must
belong to this module or to one of its `IMPORTS`, and what it resolves to must
be the kind of declaration the table it stands in calls for — a `CTORREFS` entry
a constructor, a `FOREIGNREFS` entry a foreign, a `GLOBALREFS` entry a top-level
value. A file naming something no import declares is rejected rather than
resolved to whatever else is loaded.

### The operations a module carries out

`PRIMS` holds operations and nothing else. Which `Base` entry an operation
realizes is fixed by the ABI manifest at the version the header names, so a
reader derives it rather than reading a copy: were the correspondence written
twice, target validation could check one entry while the machine ran another
operation.

**An operation is how an entry is carried out, not a way of not using it.** A
module whose `PRIMS` names `Base.Int.add`'s operation owes that entry at the
profile holding it exactly as one calling it through `FOREIGNREFS` would, so
`PRIMS` is the use set target validation reads alongside `FOREIGNREFS`
([Mid IR](../04-MiddleEnd/01-Mid-IR.md)).

### Initialization

`GLOBALS` is ordered, and initialization runs it in order: a `run` entry
evaluates its function once and stores the result, and a `func` entry installs a
closure over an empty capture list without evaluating anything. Which one a
value gets follows the shape of its right-hand side: a top-level lambda is a
`func` and everything else a `run`, so a global a `CALLK` reaches holds a
function of the arity that call supplies ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)). A module's
imports are initialized before it is.

A right-hand side that diverges hangs initialization whether or not anything
refers to it, and one that faults ends it. Both follow from evaluating eagerly
in declaration order, which Core fixes and this format preserves
([Semantics](../03-Typed-Core/06-Semantics.md)).

### The format admits modules that arrive one at a time

A `.dmo` names what it imports and refers to another module's globals by
qualified name. Nothing in it is resolved against a closed set of modules, and
no section indexes anything outside the file.

This is what a read-eval-print loop needs: an entered expression becomes a
module of its own, compiled and loaded against the modules already present,
without relinking them. Stella's REPL is a loop over the interpreter and uses
exactly that ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)). Keeping the format free of whole-program indices costs
nothing now and is expensive to retrofit.

## What lowering does not do

- **No optimization.** No inlining, no constant folding, no dead code elimination, no common subexpression elimination. Mid IR is where those would belong, and none of them is in scope
- **No register allocation.** One slot per Mid IR local, and one more wherever an atom has to reach a register before an instruction can take it
- **No totality or arity checking.** The Core type checker established the first and Mid IR's invariants the second
- **No typing.** `Rep` is carried through to the file, and nothing re-derives or checks it. Core's types, rows, and effect rows are gone by the time Mid IR exists

What it does do first is **verify the invariants it rests on**. A register is a
local's number, so lowering a module whose locals are not what Mid IR says they
are would place a caller's argument in one slot and the body's read in another
([Mid IR](../04-MiddleEnd/01-Mid-IR.md)).

## What a consumer owes

These hold of anything that executes a `.dmo` or generates code from one, the
virtual machine included. They are obligations of the format rather than of any
one implementation.

1. The evaluation order of [Semantics](../03-Typed-Core/06-Semantics.md), which is observable because any subterm may perform an effect
2. `PERF` finding the innermost marker of its key
3. A continuation applicable any number of times, each application proceeding from the captured state and returning to whoever applied it
4. A handler marker standing below the body's activation, so that returning from the body runs the return clause and a tail call inside the body leaves the path to it intact
5. A fault discarding the continuation entirely, handler markers and region frames included
6. A region frame standing below its handler's marker and within the continuation, so that `CGET` and `CSET` reach the innermost frame declaring a key and a captured segment carries the values its frame held at the capture
7. The three paths a value takes: an owner marker closing its region before its return clause runs, a reinstatement leaving that region open, and a frame no marker owns closing with no return clause at all
8. Conformance of every foreign implementation it supplies: condition (3) of `Σ ⊨ G` — each returns a value of the instantiated result type or a fault, performs no proper effect and runs no reified computation it constructs, applies no Stella function value, terminates, and has no **observational** effect where its declaration asserts `#observ(none)`, which is why such an entry does not fault. One writing to a mutable array behind a pure interface asserts nothing and is conforming. **What the condition asks is asked of the calls that respect the entry's ABI preconditions**, so a consumer owes nothing for a call that violates one and is not obliged to detect one (D42) ([Semantics](../03-Typed-Core/06-Semantics.md))
9. The runtime ABI at the profile it claims, including the execution of `main`
10. One identity per key, per operation name, and per constructor across every module it has loaded, a table index being the file's own

A consumer unable to meet (3) is non-conforming in the way D18 records, and says
so rather than failing quietly: the v0.1 JavaScript and Wasm backends are in
exactly that position, and the virtual machine is not.
