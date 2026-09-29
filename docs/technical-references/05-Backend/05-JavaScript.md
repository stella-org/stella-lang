# The JavaScript backend

The JavaScript backend turns a `.dmo` into an ES module (D45). It reads the same
file the machine executes ([Bytecode](01-Bytecode.md)), and it reaches foreign
implementations through the same manifest target the machine does
([Foreign Manifest](04-Foreign-Manifest.md)).

This document fixes what the backend reads, what it owes, what it generates, and
which of its choices are still open. How a value is represented while a program
runs is the backend's own and is not a published ABI, exactly as it is not for the
machine ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

**The backend is a package of its own**, depending on the compiler and known to no
part of it: the compiler's work ends at the `.dmo`, and a front end hands that file
to whichever backend it builds for. What the package offers is a `.dmo` in, text
out, and the file name the text is written to; the stages between are its own and
change with the strategy (below).

## It reads a `.dmo`

**The input is the module a decoder returns**, not Mid IR. A build that has just
lowered a module may hand the lowered value across without writing and reading
the bytes, since an encoding followed by a decoding gives back the module it was
handed ([Encoding](02-Encoding.md)); what the backend may not do is reach past that
value into Mid IR or Typed Core for something the file does not hold.

**The direct path accepts exactly what the bytes would.** A decoder returns only a
module that passes the walk an encoder also reads, at the format and ABI versions
it implements, with text a sequence of scalar values ([Encoding](02-Encoding.md)),
and lowering by itself establishes none of that. So a module handed across is held
to what an encoder checks before the backend reads it; otherwise the two paths
would accept different modules, and a defect of lowering would reach generated
code by one of them and be refused by the other. **The module is run through the
encoder itself**, the bytes it writes being dropped, so one walk decides both routes
rather than two walks that could come to disagree.

**What a loader establishes of one module is checked before any code is
generated.** A decoder hands on every module whose bytes it can read, and whether a
module's declarations are its own, whether a name is declared twice in one
namespace, whether its exports name its values, whether its globals are
installable — a `func` over a function of at least one parameter, a `run` over one
of none, neither expecting captures — whether a foreign the ABI fixes, an
operation or a `Base.IO` entry, is declared at the arity the ABI gives it, whether
a handler declares one cell or holds clauses for one operation twice, compared by
the key and the name an index holds rather than by the index, and whether every
`HNDL` and `TAILHNDL` supplies as many clauses and initial cell values as its
handler holds are properties of the module rather than of its bytes. Steam checks
them where a module loads ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md));
generated code has no such moment for what one module decides alone, so the backend
checks them first and refuses the module otherwise. What another module declares is
checked where the generated modules are linked and loaded (below).

**That restriction is the point of the route.** A `.dmo` is what a backend outside
this compiler builds on (D34), and a first-class backend reading the same file is
what shows the claim holds. Whatever the JavaScript backend finds missing is
missing for every other consumer too, and is added to the format rather than
fetched from the side.

**The format is revised where it falls short.** A `.dmo` carries no Core type,
row, or effect row, and `Rep` is what survives of them ([Bytecode](01-Bytecode.md)).
An optimization that needs more than that runs before lowering, where the types
still exist, or has what it needs recorded in the format. Before the first
released version of Stella the format changes freely for such a reason, the
machine and the backend being changed with it.

## References are resolved once

A `.dmo` names constructors, foreigns, globals, keys, and operations by indices
into its own tables ([Bytecode](01-Bytecode.md)). **The backend resolves every one
of them where it generates code or where the generated module is loaded, and
never where a call runs.**

**What resolution must keep is identity, not spelling.** A table index is the
file's own, so two modules may hold one key at different indices and must still
agree about it; and two keys may share a spelling and still differ:

| | Is one identity across every module | Differs from |
| --- | --- | --- |
| a key | its kind together with its payload | a key of another kind with the same spelling: a field `n` and a tag `n` are two keys (D16) |
| an effect's operation, of `OPS` | its name | — |
| a constructor | the module that declares it together with its own name | a constructor of the same name in another module |
| an effect key | the effect it names, module included | an effect of the same name in another module |

Obligation (10) of [Bytecode](01-Bytecode.md) is this table, and it binds the
backend as it binds the machine. **A representation that writes a key as its bare
spelling fails it**, a field and a tag of one spelling then selecting each other.

The backend meets the table as follows.

| | Represented as | Compared by |
| --- | --- | --- |
| a key | a string of its kind and its payload: `s:x` for a field, `t:Ok` for a tag, `p:0` for a position, `e:Mod.Sub:Eff` for an effect | string equality, which is identity across every module since the kind is part of the string |
| an effect's operation, of `OPS` | its name | string equality, where a `perform` finds the clause of the handler its key selected |
| a constructor | a descriptor object the declaring module creates and every other module imports | **reference**. A tag is unique within one type only, and nothing checks that a dispatch's branches are of one type, so a comparison of tags could send a value of one type into the branch of another |

`BRC` dispatches on a value's descriptor, and `FIELD` checks that the value it
reads is of the constructor the instruction names before reading the field.

**A `Base` operation of `PRIMS` is not in the table**, having no identity to
compare: a `.dmo` names one by the code the ABI version fixes, and the backend
resolves it where it generates code — to an expression, or to a descriptor where a
partial application waits on it — so nothing compares one while the program runs.

## The generated module

**One `.dmo` becomes one ES module**, written to a file named by the module, so
`Main.Sub` is `Main.Sub.js`, and another generated module imports it as
`./Main.Sub.js`. The runtime is imported by a specifier the build supplies.

**What another module reads is exported under a name no binding can clash with.**

| Exported as | What it is |
| --- | --- |
| the global's own name | a global of `EXPORTS`. A global the module does not export is not exported, which is what data abstraction is (D22) |
| `ctor Name` | the descriptor of a constructor the module declares. Every constructor is exported: a `.dmo` does not record which a module publishes, a type checker having settled that before the file existed |
| `foreign name` | the descriptor of a foreign of `EXPORTS`, whatever carries it out (below) |
| `arity table` | the definitional arity of each exported global installed as a function |
| `entry point` | the global the build names as the program's entry point, in the module holding it |

Every name but a global's holds a space, so no Stella identifier is one of them.

**Every name another module is referred to by is imported by that name**: each
imported name `GLOBALREFS`, `CTORREFS`, `FOREIGNREFS`, or `CALLEES` holds is imported
once, whether or not anything then reads it — a foreign the runtime carries out
included, though it is called as the runtime's own. Linking the generated modules
therefore refuses a reference to what the declaring module does not export, before
anything runs, which is where Steam refuses one. Every module of `IMPORTS` is
imported, its arity table at least, so an imported module is initialized before this
one whether or not anything of it is named, which is the order module initialization
owes ([Bytecode](01-Bytecode.md)).

**What one module assumed of another is checked where the modules load.** A known
call to an imported global supplied the definitional arity the importing module's
interface gave it, a partial application of one supplied fewer, a construction of an
imported constructor supplied its arity, and a call of an imported foreign supplied
the arity it is declared at and a partial application of one fewer. The generated
module checks each against what the declaring module exports — its arity table and
its descriptors — as its first act, and refuses to load where one disagrees. A stale
`.dmi` is therefore a module that does not load rather than a call that passes the
wrong number of arguments ([Interface](03-Interface.md)).

**A global is initialized where the module is evaluated**, in the order of
`GLOBALS`: a `func` global becomes a closure over an empty capture list, and a `run`
global is evaluated once.

## Structure is emitted, not rebuilt

A `Node` is a straight run of instructions ending in one `Tail`, and a dispatch
holds its branches inline ([Bytecode](01-Bytecode.md)). The backend walks that
tree: a `BRC` or `BRK` becomes a dispatch over resolved identities, a `BRIF` an
`if`, and a join point a construct the enclosing function can transfer to by name.
**Nothing is reconstructed from a control flow graph** (D32).

**A join point is a segment of its own** (below), and a `JMP` writes the join
point's parameters as one parallel move — every argument read before any parameter
is written, an argument register being able to be a parameter too — then transfers
through the run loop. A loop written with a join point therefore runs in bounded
host stack.

**`BRL` dispatches by literal identity, which JavaScript's `switch` does not
implement.** A `switch` compares by strict equality, which identifies `0.0` with
`-0.0` and separates a NaN from itself; literal identity does the opposite on both
counts (D37, [Prim and Base](../06-Modules/02-Prim-and-Base.md)). A `switch` is the
right lowering where strict equality and literal identity agree — an `Int`, a
`Char`, a `String`, a `Boolean` — and a `Number` dispatch compares by identity,
`Object.is` deciding the zeros and a NaN test deciding every NaN as one.

**Readable output is not a goal.** A register becomes a slot of the frame and an
instruction a statement, and what makes the result resemble hand-written code is
optimization over the backend's own representation — keeping a register in a host
variable between the points where the frame must hold it, propagating a copy,
folding a constant — rather than anything this document requires.

## What the host does not give

**JavaScript has no proper tail calls on the hosts this backend targets**, and
`TAILK`, `TAILU`, `TAILFFI`, and `TAILHNDL` oblige a transfer that pushes no frame
([Bytecode](01-Bytecode.md)). The obligation is the backend's to meet by its own
means; a loop over a bounded tail call written as a JavaScript call is a program
that runs in a test and exhausts the stack on real input.

**The host's call stack cannot be copied, and a generator cannot be cloned.**
Resuming a generator advances it, and ECMAScript offers no way to duplicate a
suspended one ([GeneratorResume](https://tc39.es/ecma262/2024/multipage/control-abstraction-objects.html)).
A continuation applied a second time must begin from the state captured
(obligation (3)), so the part of a computation a `full` clause may capture cannot
live only in host frames or in a generator's state.

**So the execution model represents a continuation itself**, as the machine does:
with frames and a run loop of the backend's own, or by converting to
continuation-passing style. That it is one of them is not a choice.

## The execution model: frames and a run loop

**An activation is a frame on a stack of the runtime's own, and a function is a set
of segments.** A function is cut at each non-tail call, each `PERF`, and each
`HNDL`: its entry is one segment, what follows each such transfer another, and each
join point a third kind. A segment runs straight to its next transfer and returns
to the run loop what to do next — return a value, call, tail call, perform, install
a handler, or continue at another segment of the same frame — so the host's call
stack never holds more than one segment.

| What the loop does | Where it comes from |
| --- | --- |
| a call pushes an entry naming the frame, the register the value goes to, and the segment that continues | a non-tail call |
| a tail call pushes nothing and replaces the frame | `TAILK`, `TAILU` |
| a perform pushes the same entry, then answers as the clause's form says (below) | `PERF` |
| an installation pushes the same entry, then a marker and, where the handler declares cells, a region directly below it, and calls the body | `HNDL`; `TAILHNDL` pushes no entry for the frame |
| a value reaching an entry is written and the frame continues, is applied to the arguments an over-application left, or passes a marker, a region, or a clause's boundary as the next section says | `RET` |

**Applying is decided by the count before the kind**, as the machine decides it:
too few arguments build a partial application whatever the callee, too many call
it with its arity and leave the rest pending on what comes back, and a partial
application completed later carries out the callee once the last argument arrives
([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)). Registers live in the
frame, so a deep non-tail recursion takes heap and not host stack: **the depth of
a program's calls narrows nothing about which programs the backend runs.**

**The strategy is the backend's to change, not the format's.** Frame IR, the lower
IR the frame strategy cuts a module into, holds the segments; a strategy converting
to continuation-passing style, or bubbling a yield up the host's stack in the
manner of Koka's generalized evidence passing, would have a lower IR of its own
between the same resolved module and the same JavaScript syntax. A build selecting a strategy selects it for every module
it generates, the strategies not sharing a calling convention. Frames and a run loop
come first because they carry the machine's model over directly, which is what
makes a continuation applied twice expressible from the start; what is faster is
measured on top of them.

## Handlers, continuations, and regions

**The stack holds what the machine's holds, in the same order**
([Bytecode](01-Bytecode.md)). Installing a handler pushes a marker and, where the
handler declares cells, a region directly below it. A `HNDL` pushes these above the
entry of the frame that installed it, and a `TAILHNDL`, pushing no entry for that
frame, directly above whatever was below it. A marker a continuation re-pushes at its bottom has no
region of its own below it. A marker is found by its key's string and a clause of it
by the operation's name, looked up in a map built when the handler is installed, so
no operation name can collide with a property the host gives every object.

**A marker records two facts apart: whether installing produced it, and whether the
entry below is the region it opened.** An owner of a handler that declares no cells
opens no region, and the entry below it belongs to someone else, so being an owner
does not say that the region below is its own. A value reaching a marker that owns
its region closes that region first — finding anything else there is a defect — and
then goes to the return clause. A value reaching a region no marker owns, or a
clause's boundary, passes on down.

**A `full` clause takes the stack from the perform up to the answering marker.**
The perform pushes its frame's entry first, so the continuation begins at the
perform, and the run of entries from there up to and including the marker is taken
off the stack and becomes the continuation; the handler's region, where it has one,
stays below. The
clause is then applied to the operation's argument and the continuation.

**A `fast` clause is applied where the perform stands, above a boundary.** The
boundary records how far below it the answering marker stands, and a search for a
marker or a cell that reaches it continues directly below that marker, so the body
sees neither the handler nor what stood between it and the perform, while it sees
the handler's region where it has one (D28). The distance is relative because a
`full` operation the body performs may take the boundary with the marker into a
continuation, and re-push the two anywhere. A search for a marker and a search for a cell are one
walk, which is what keeps a perform and a cell access reaching the same context.

**Applying a continuation re-pushes a copy of what it took, every time.** What an
application can change is the register array of each frame in the segment and the
cell slots of each region, so each is copied, holding what it held when taken; the
values they hold are shared, a value written into in place being one value before
and after. This rests on a frame being referred to by nothing but the one entry
holding it and, while it runs, the loop. **The marker at the bottom is re-pushed as
one owning nothing**, whatever it was taken as: a region its handler opened stayed
behind, and closing it belongs to whoever holds it now. The first argument
reaches the top of the segment, and arguments past it wait below the segment for
what it returns.

**A cell is found afresh at each access.** Applying a continuation copies the
regions it re-pushes, so a cell found before a transfer is not, in general, the one
after it, and nothing holds a cell across a transfer.

## A `fast` clause, and purity

**A `fast` clause is cheap and does not make its context one-shot.** It constructs
no continuation (D28), so the backend lowers it as a call — one whose body looks for
handlers and cells below the answering handler, past what stands between it and
the `perform`, as Core binds it ([Bytecode](01-Bytecode.md)). But its body may
perform an operation whose `full` handler resumes more than once, and the
evaluation context around the `perform` is then re-entered
([Effects](../03-Typed-Core/03-Effects.md)). A representation that is safe only
for one resumption is therefore not licensed by a clause being `fast`.

**What does license a plain JavaScript call is purity.** A function entry whose
body runs under the empty ambient row lets no unhandled operation propagate out of
its frame. It may still `perform` inside, under a `handle` it installs itself, and
it may call a foreign whose declaration admits an observational effect; what the
empty row rules out is a handler **outside** the frame capturing a continuation
that contains it. So no continuation built elsewhere holds the frame, and a
non-tail call to such an entry may be a host call. Its depth is then bounded by
the host's stack, which is a resource limit and not a meaning. What happens inside
the entry — a handler of its own, a `full` clause resuming twice — is lowered by
the execution model like anything else.

**Purity licenses a host call and not a lost tail call.** A pure entry still ends
in `TAILK` or `TAILU` wherever its body is a tail call, a self-recursive loop above
all, and writing that transfer as an ordinary JavaScript call grows the host stack
with every iteration. A tail transfer stays one that pushes no frame, whether or
not the entry is pure (above). **So an entry is generated as a host function only
where every tail transfer it holds is a `TAILK` to itself — written as a loop — a
`TAILFFI`, or a `Tail` that is not a call.** A pure entry with any other tail
transfer stays in frames. This does not bound a non-tail recursion, which is what
reporting an exhausted host stack is for (below).

**The row that decides is the body's, not the first arrow's.** An entry collapses a
run of lambdas ([Translation](../04-MiddleEnd/02-Translation.md)), so
`A -> B -{ ρ }-> C` is one entry of two parameters whose body runs under `ρ`: its
first arrow is pure and the entry is not. A `handle` body and a handler clause are
entries whose bodies run under a row that is in general not empty.

**A `.dmo` does not say today which functions are pure, so every function is
generated in frames.** The effect row is erased before the file exists, and
Translation is where it is still known
([Translation](../04-MiddleEnd/02-Translation.md)). What follows in this section is
the design adopted for the step that adds the record (the fourth of
[Implementation Plan](../01-Introduction/04-Implementation-Plan.md)'s steps for this
backend); until that step lands, [Bytecode](01-Bytecode.md) and
[Encoding](02-Encoding.md) describe `FUNCTIONS` as it is, without the byte below.

**The record will be one byte per entry of `FUNCTIONS`**, `1` for a pure entry and
`0` for any other, an encoder and a decoder accepting those two alone. The format
keeps its version while Stella is unreleased, so a build caching `.dmo` files drops
them when the byte arrives, and Steam will read it and make nothing of it.
Translation will set it as follows.

| Entry | Pure where |
| --- | --- |
| a run of lambdas | the annotation on its innermost lambda, `τ -{ ρ }-> τ'`, has `ρ` the closed empty row once normalized |
| a `run` global | always: a top-level right-hand side is checked under the empty row ([Modules](../06-Modules/01-Modules.md)) |
| a `handle` body, a handler clause | never, for now. A body runs under the row its handler handles, and a clause's row is not written in any annotation Translation reads |

With the record, pure entries are generated as host functions, and two more
things come with them.

**A function's descriptor will carry its calling convention**, `direct` for one
generated as a host function and `frame` for any other, because a closure, a partial
application, and a continuation are applied without the caller knowing which it
holds. The one generic apply reads the convention: from frame code a `direct` callee
is a host call and a `frame` callee a pushed frame; from a host function a `direct`
callee is a host call and a `frame` callee, or a continuation, is entered in a run
loop of its own — sound because the empty row lets nothing that run performs escape
it. Arguments an over-application leaves go through the same apply, whichever
convention the value that comes back has.

**An exhausted host stack is a failure of the host, not of the program.** A deep
non-tail recursion through host functions can exhaust the host's stack, which the
frame strategy alone never does, so the failure arises only once host functions
are generated. It is then reported apart from a Stella fault, as a host resource
failure carrying what the host threw as its cause. **An arbitrary
`RangeError` is not taken to be an exhausted stack**, one being raised for other
reasons too, among them a defect; what cannot be told apart is reported as a host
resource failure of undetermined cause, still carrying what was thrown.

## Foreigns, operations, and `IO`

**A foreign is resolved as a declaration first**: one of this module's `FOREIGNS`,
or one a module it imports exports, which the generated module imports by name like
anything else it names in another module. **The name then selects what carries it
out**, as it does on the machine: an operation of the ABI, `Base.IO.pure` or
`Base.IO.bind`, which the runtime carries out itself, or else an implementation a
host supplies. So a foreign of the runtime's that its module does not declare, or
does not export, is refused as any other would be.

**A foreign implementation is the one the machine calls.** It is reached through the
manifest for the target `javascript`, marshalled by the signatures that manifest
carries, and a refusal is recognised by the helper's brand
([Foreign Manifest](04-Foreign-Manifest.md)), so one implementation serves both
consumers. The rules of that document apply unchanged: an adapter is uncurried,
synchronous, and checked on the way out.

**The build reads the manifest, and the backend reads no file.** The build hands the
backend, for a module, the signature of each foreign it declares that a host
implements and the specifier those implementations are imported by, resolved
already: a specifier is resolved against the manifest's place
([Foreign Manifest](04-Foreign-Manifest.md)), and an import written into the
generated module would be resolved against the generated module's own. **Only the
declaring module imports the implementations**, and it alone makes the descriptor of
each foreign it declares, holding the signature where a host implements it; a module
calling the foreign imports that descriptor, and the arity a call supplies is checked
against the declaration where the modules load (above).

**Each invalid combination is refused at the earliest point that can tell.**

| Refused | Where |
| --- | --- |
| a foreign a host must implement, declared by a module the manifest gives no entry; an entry giving it no signature; a signature whose `params` are not the declared arity long; an entry the runtime carries out declared at another arity | where the module is generated |
| an implementation module that cannot be reached; one lacking the export | where the generated modules are linked, the implementation being imported by name |
| an export that is not callable; a call or partial application of an imported foreign at a count its declaration does not admit | where the generated module is loaded |

**A call is an expression and cuts no segment.** A foreign's body is synchronous and
applies no Stella function, so nothing can capture the frame across it, and a call
in tail position returns what the call gives.

**What crosses is converted by the kind of its position, and checked on the way
out.** A `char` crosses as a string of its one scalar value, and a `unit` parameter
keeps its place as `undefined`. A result is a breach where it is not of its kind — an
`int` not a whole number within 32 bits, a `char` not one scalar value, a string
holding an unpaired surrogate — and `-0` returned as an `int` is `0`, an `Int` having
one zero (D37). An action is checked to be callable, and what it produces is checked
by its kind when it is performed.

**Only the host's own call is inside the `try`.** Whatever the implementation
throws, or an action it returned throws as it is performed, is a throw, the runtime's
own fault and defect classes included: a host cannot pass for the runtime, and the
machine, catching every exception there, agrees. The marshalling around the call is
the runtime's, and what it raises is not taken for a throw. **The six failures are
kept apart**: a refusal, a throw, and a breach, of a foreign or of an action it
returned, each reported with the foreign it arose at where the machine reports one.

**An operation is carried out where it stands**, with the meaning
[Prim and Base](../06-Modules/02-Prim-and-Base.md) fixes, as an expression of the
generated code where one expression carries it out and as a call of the runtime
where one does not — a check that faults, a count of scalar values. Where that
meaning and the host's operator part, the backend implements the meaning:
`Base.Int.mul` is not `(a * b) | 0`, `Base.Number.toInt` is not `| 0`, and
`Base.String.lt` is not `<`. **Every operation of the ABI version has one**, so no
module names an operation the backend leaves without a meaning.

**A fault and a defect are two failures and stay two.** An operation failing on an
input its specification says it fails on is a fault: it discards the whole run, no
handler intercepting it (obligation (5)). A state no well-formed `.dmo` admits —
reading a field of another constructor, extending a record at a key it holds — is a
defect above the program and is reported as that, never as a fault. **A fault that
ends a module's initialization names the global being initialized**, which is what
Steam reports where a global's initialization fails
([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

**Executing an `IO` is the drive loop's**, with the shape and the obligations the
machine's has: `Pure`, `Bind`, and a native action, executed iteratively over a
stack of pending continuations ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).
Applying a pending function is a run of its own, finished before the loop goes round
again, and one returning what is not an `IO` is a defect: a `.dmo` carries no type
to hold it to `a -> IO b`.

**The entry point is the build's to name.** The module holding it exports that global
as `entry point`, and a name that is no global of the module is refused where the
module is generated. Whatever starts the program imports it and hands it to the
runtime to execute. **A global holding no action is a program that does not
start**, reported apart from a fault and from a defect: any global of a well-formed
module can be named, so it is neither a run that failed nor a state no module admits,
which is how the machine reports one too.

## What testing the backend compares

**Running one program on the machine and on the backend tests the backend, and
not lowering.** Both read the `.dmo` lowering produced, so a defect in lowering
reaches both alike and the comparison agrees with itself. What covers lowering
today is its own tests, and execution tests whose expected results are fixed
independently from hand-written Core. Comparison with an evaluator of Typed Core
is what a claim that lowering preserves meaning broadly waits on, and no such
evaluator exists yet ([Implementation Plan](../01-Introduction/04-Implementation-Plan.md)).

What the comparison is for is the part lowering does not decide: what the backend
makes of the same file.

**The two are compared through shared fixtures rather than against each other.** A
fixture is a set of lowered modules and a manifest saying which load, in what order,
whether they load or are refused or fault where they load, and what the named globals
hold, the values fixed by hand from the program. A fixture with an entry point says
how executing it ends — the value it produces, the fault it ends in, or that it does
not start — and one whose modules declare foreigns a host implements holds a foreign
manifest and the implementation module it points at. The machine and the backend each
read the bytes and check the same manifest, so the two agree wherever both pass, and
neither lowers Core. The compiler's own tests check that every fixture is what
compiling its source gives now, the format not being frozen.

**Each property of re-entering a continuation has a value of its own that only it
decides**: a region inside a continuation resumed twice, which shows its cells are
copied; a continuation whose bottom marker owns a region, resumed twice from its
clause, which shows that marker is re-pushed owning nothing; and one resumption held
captured while a second runs through the same frame, which shows the frame's
registers are copied — resumptions run one after another cannot show it, lowering
giving every local a register of its own. A module no Core compiles to, such as a
handler naming one cell twice, is made by changing a lowered one, and its manifest
says what was changed.

**What a run must produce includes the sequence of its observable effects.** The
implementation module records the events the fixture chooses to observe, which
include both ordinary foreign calls and actions as they are performed, and the machine
and the backend each read that record from the module instance the program reached,
so the two must agree on what the host saw and in what order, including where a run
ends in a fault. A fault is compared by its kind and by what both report of one of
that kind; what each says of a breach is its own wording and is not compared. The
fixture implementations that throw include ones throwing the runtime's own fault and
defect classes, which must still be reported as throws.

## Conformance

**The backend is conforming with respect to D18.** It passes the cases that decide
it: a `full` clause resuming its continuation twice, each resumption beginning from
the captured state, and a continuation captured outside a region carrying the cells
it was captured with ([Bytecode](01-Bytecode.md)). A second resumption is an
ordinary application, and no error is raised for one.

## What is open

- **A `handle` body's and a handler clause's purity**: recorded as impure until
  Translation reads the row each runs under
- **Widening which pure entries become host functions**: a tail transfer between two
  host functions, and not only to itself, once measurement says it is worth the
  host stack it spends
- **Recognising an exhausted host stack**: what on a given host tells it apart
  from another `RangeError`, beyond reporting what cannot be told apart as of
  undetermined cause
- **The lower-IR optimizations**: an evidence environment in place of a search of
  the stack for a handler or a cell, a `fast` clause run in place, and registers
  kept in host variables between the points where a frame must hold them
- **A second strategy**: continuation-passing style, or a yield bubbled up the
  host's stack, measured against frames and a run loop
