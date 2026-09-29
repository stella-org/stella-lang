# Abstract Machine

*Steam* is the **bytecode interpreter** that executes a `.dmo`. The instruction
set, the continuation, the container, and the obligations all three impose are
[Bytecode](../05-Backend/01-Bytecode.md). **This document fixes the interpreter**:
what it is for, what a value is while it runs, how its stack is shaped, how a
module enters its registry, where a foreign implementation comes from, and how a
run ends.

It is not a virtual machine of the kind the JVM and BEAM are, and nothing here is
a step towards one. What it is instead is small enough to read and useful as it
stands, and it is what the REPL runs on.

## What Steam is for

**The REPL is Steam, and that is a delivered use.** Stella's read-eval-print loop
is a loop over this interpreter: an entered expression is compiled to a module of its
own and loaded against the modules already present, which is what keeps the container
free of whole-program indices ([Bytecode](../05-Backend/01-Bytecode.md)). The
interpreter therefore reaches users, and the module lifecycle below is written for
that use rather than for a batch compiler's — the session mode below is what the
shell talks to.

**The compiler is a user too.** Elaboration is split into policy, which is guest
Stella, and mechanism, which is the compiler's (D39): a synthesizer named by a
`⟨ τ by f ⟩` is an ordinary Stella function, and the compiler runs it on this
interpreter, reaching it by the resolved qualified name the constraint carries
([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)).

**What that use shares is the machine and the session.** The registry, loading a
module at a time, resolving a name, and the interpreter running the code are the same
for it as for anything else, and it reaches them through the one long-lived `session`
mode, opened with the `elaboration` profile and speaking on the channel below. What it
asks for beyond them is its own: a synthesizer is a function, so it is **applied** to a
goal the host holds; an `Elab` operation it performs is answered by the host and **the
same attempt continues** from that answer; and an attempt the host abandons **discards
what the run had reached**. Those are requests of that profile, not a mode of their
own; what their payloads are is open
([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

Two uses stand beside those, and neither reaches a user.

- **A second evaluator to compare the Core evaluator against.** One program run
  both ways gives the same value and the same sequence of observable effects, which
  exercises the whole of translation and lowering at once
  ([Implementation Plan](../01-Introduction/04-Implementation-Plan.md))
- **A way to run what a one-shot backend cannot.** A continuation applied more than
  once is what D33 undertakes and what D18 records the v0.1 Wasm backend as
  lacking

## Two modes

Steam runs in one of two modes, and **the front end is what a user runs**: the
Stella CLI compiles, decides what Steam is given, and prints what comes back.

| | **Session** | **Run** |
| --- | --- | --- |
| lives | across many inputs | for one program |
| is given | one module, then a request naming what to report | every module of the program in dependency order, and the entry point by name |
| answers | the value that module's declaration holds | the `IO` of the entry point, executed |
| ends | when the front end closes it | when that `IO` has been executed, or at the first failure |

**What this mode fixes is the loading half**, which the compiler's use shares: a
module at a time, and a request naming what to report. Running a synthesizer asks for
more than that, and how it asks is open (above).

**Session is what the REPL is built on.** The shell belongs to the Stella CLI: it
parses, elaborates, type checks, and compiles an entry to a module of its own, hands
that module to a Steam running beside it, and prints the value Steam answers with
beside the type it checked. Steam holds the modules that accumulate and nothing of
the source.

**Run is one program, once.** The CLI builds the project to `.dmo` files, orders the
modules by their dependencies, hands Steam the list and the entry point, and Steam
loads them in the order it was given before executing that entry point.

**The entry point is named, not found.** Several modules may declare a `main`, a
`.dmo` carries no types and marks no entry point, and a list in dependency order says
nothing about which of them was meant — so the name comes with the list, as a
qualified name or as the module whose own `main` is meant. **A front end may default
the name rather than ask for it** — the `steam` command defaults to the module called
`Main` (below) — which is naming it too: what is settled before anything is looked
up is the module, and only that module's globals are then consulted. **What no front
end may do is make a duplicate `main` a condition of loading**, since a global of
that name is an ordinary global and a session wants no entry point at all. It is read from the
declaring module's globals and **not** through its exports: an entry point need not
be exported. What a process makes of the run afterwards — an exit status, and what it
is for a fault — belongs to the runtime ABI and is not settled
([Open Questions](../99-Open-Questions/01-Open-Questions.md)); what the mode fixes is
that the `IO` that global holds is executed to completion, or that a fault ends the
run.

**Steam resolves no Stella module.** It neither reads an import graph to decide an
order nor looks for a `.dmo`: what it is given is what it loads, and in the order it
is given. A module's `imports` is read as a **condition** — every one of them is
already in the registry, or the load fails — and never as a way to find anything.
Ordering is the front end's, which is where the source, the search paths, and the
build plan are.

**A host module is the one thing it does reach for**, and only as a manifest
dictates (D43): the manifest names what to load and the interpreter loads exactly
that ([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)). **That is not a
search either** — nothing is looked for, tried in several places, or inferred from a
name — so the sentence above holds as written for the modules a program is made of,
and the thing it excludes is still excluded.

### The `steam` Command Line Interface

**The `steam` command is how a program reaches the interpreter, and the Stella CLI
starts it.** The two are not competing front ends and not two paths either: there is
one path, and `stella run` compiles, writes what the command takes, and runs it.

```text
compiler                         the language: checking, lowering, the container
cli      → compiler              a library of what a command line needs
steam    → compiler, cli         this interpreter, which is a command
stella   → compiler              the application a user runs, which starts that command
```

**`cli` here is a shared library and not the application.** Both this interpreter's
command and the one above it are built out of it, which is why `steam → cli` is an
edge: it says nothing about who integrates whom.

**Nothing links the interpreter, and that is the point of D43.** `compiler → steam`
would be a cycle, so the compiler could never have called the interpreter as a
library; the application could have, and no longer needs to. What passes between
`stella` and `steam` is a command line — paths, a name, and a manifest — so the
boundary is a process for `run` exactly as it must be for `session`, and one design
serves both.

**The dependency direction still decides something**, and it is narrower than before:
it says the compiler may not reach the interpreter, which is why a compile-time
session is a process and why `session` and `run` cannot differ about who assembles
the table.

**What crosses between them is a command line, and that is enough** (D43). Running a
program is a function of three things — the modules in order, the entry point, and the
foreign table — and the third is **assembled by the interpreter** from a manifest
naming where the implementations are
([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)). A path is a thing an
argument vector carries, so `stella` starts this command rather than linking it.

**The alternative was to hand the table over, and it does not survive the session.**
A table holds host functions, which no argument vector and no framing built for names
and bytes can carry, so an application that assembled one would have to link the
interpreter and call it. That works for `run` and fails for `session`: a long-lived
session is what the compiler talks to, the compiler cannot link the interpreter
(the cycle above), so the session is a process — and a process cannot be handed host
functions either. One of the two modes therefore had to assemble its own table, and
a rule that held for one mode and not the other would be two designs wearing one
name (D43).

**So `steam run` is the whole path and not a reduced one**, and the command is what a
program reaches the machine through. What it adds beyond being that path is that a
`.dmo` already built can be run without rebuilding it.

```text
steam run --entry Main  base/Base.Int.dmo  lib/Lib.dmo  main/Main.dmo
```

**The files are given in dependency order and the command sorts nothing.** That is
the rule above read at the command line: the arguments are loaded left to right, a
module whose imports are not already loaded is refused, and no path is searched and
no name resolved to a file. **A wrong order is a load error and not a reordering** —
the command has no import graph to sort by, and inventing one here would put a second
answer beside the build plan's.

**The entry point is named by two options, one for each half**, and each has a
default. The global is read from the named module's own globals and not through its
exports (above).

| | Names | Default |
| --- | --- | --- |
| `--entry` | the module | `Main` |
| `--entry-global` | the global within it | `main` |

**One option carrying both halves would be ambiguous, and the ambiguity is not
resolvable.** A module name has dots in it, so `A.B` reads as the module `A.B` and
as the global `B` of the module `A`, and nothing in the spelling separates them.
**Deciding by looking at which modules were loaded is the one answer to rule out**:
the same argument would mean different things for different sets of files, so a
command line that worked would stop working when a module was added.

**Two options say it without a separator to invent.** A qualified name could be
spelled with something other than a dot — `Main::main`, say — but `::` already means
something in the language, any other choice is a private convention of this command,
and the split matches what is actually being said: the module is settled first, and
only then is a global looked up inside it.

**Nothing is ever searched for across modules**, and that is the whole of why the
question of a duplicate does not arise. The entry module is settled before anything
is looked up — by the default or by the flag — and only its own globals are
consulted, so a second module declaring a `main` is not a competitor, not an
ambiguity, and not consulted at all.

| | |
| --- | --- |
| a module declaring a global called `main` | **loads**, wherever it stands. Nothing about the name is reserved, and a session that never wants an entry point is not refused one |
| two of them | likewise. The entry module is named, so which one is meant was never in question |
| no module named `Main`, and no `--entry` | a failure of `run`, and of nothing below it |

**Making a duplicate a load error instead would reserve `main` across everything
that links together.** A `.dmo` carries no type, so what a loader could compare is
the name and nothing else: a library with a global called `main` — for its own
reasons, and legitimately — would then refuse every program that imported it. The
cost would fall on library authors, and it buys nothing that naming the module does
not already give.

**An `@[entrypoint]` attribute would be resolved above the interpreter and never
here.** A `.dmo` carries no attribute, and the runtime reads no `.dmi`
([Bytecode](../05-Backend/01-Bytecode.md), [Interface](../05-Backend/03-Interface.md)),
so nothing Steam is given would let it search for one. What the attribute changes is
therefore the front end's question, and what reaches Steam is what reaches it now: a
resolved module and global, which is what the two options above carry. **That the entry
point is named rather than found holds unchanged**, which is the point of routing it
this way rather than teaching the runtime a new input.

**Nor is the entry point written into the module as code to run.** `GLOBALS` is
already the initialization section — a `run` entry is evaluated once as the module
loads — so the place to put such code exists; what does not exist is the stage that
would put it there. **Deciding which of many modules is a program's entry is a
linker's question**, and lowering answers a different one: it is handed one module
and knows nothing of the program it will be linked into. Steam is given the modules
unlinked and in dependency order, so there is no linking stage to carry the
decision, and a module that ran its own entry point as it loaded would run it in a
session too — which is what loading must not do (D25).

**The search the attribute implies stays inside the entry module**, and that is the
front end's rule to keep. A dependency may carry the attribute — a library that is
also runnable is an ordinary thing to write — and a search that ranged over
everything linked would find it. What is under the program's control is the entry
module, so that is what is asked; what the runtime then receives is one name and no
question at all.

**The foreign table is assembled from a manifest the command is pointed at**, and is
complete for a module before that module is loaded ([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)).
A program declaring a foreign that neither the interpreter claims nor the manifest
covers does not load, as before; what has changed is who fills the gap.

```text
steam run --manifest build/foreign-manifest.json --entry Main  … .dmo
```

**A manifest is not required, and its absence is not an error.** A program over
`Base` alone declares no foreign anything needs to supply, so there is nothing for a
manifest to say; a program that does declare one and was given no manifest is refused
where that module loads, naming the foreign rather than the missing file — the
declaration is what was unmet, and the manifest is one way to meet it.

**The long-lived command is `session`, and it waits.** It speaks on a channel of its
own, fixed below, and answers each request there; the `run` mode needs none of that,
being given its modules at once and answering by exiting.

**It is `session` rather than `eval` because evaluating is one of the things it is
for.** The other is the compile-time use: a synthesizer named by a `⟨ τ by f ⟩` is
guest Stella, the compiler cannot call the interpreter as a library (the cycle
above), so the CLI starts a long-lived Steam and brokers between the two
([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)). **One process mode
serves both, and what separates them is a profile fixed when the session opens** —
what a REPL may ask for and what an elaboration may ask for are different sets, and
a REPL reaching a compiler's metavariables is what keeping them apart prevents.

**What that costs the `run` command is nothing, and what it costs the framing is one
decision now.** The messages a session carries will grow — a request that yields
back to the host mid-attempt is what the elaboration profile needs, and it does not
exist yet — so the framing is tagged from the first version rather than being a
single request and a single answer that a later kind has to be squeezed into.

#### The session's channel

**A session speaks on descriptor 3 and nowhere else.** Whoever starts `steam
session` opens descriptor 3 as a bidirectional pipe; standard output and standard
error stay for logs and for what host modules print, which on Node reaches standard
output and would otherwise corrupt the channel. A starter inherits the two streams or
reads them continuously, a pipe nobody reads filling up and stopping the process.
Started without descriptor 3, the command does not start. POSIX hosts are supported.

**A frame is a length and a JSON object.**

```text
frame   = length payload
length  = unsigned 32-bit big-endian, the byte count of payload
payload = a JSON object, in UTF-8, of at most 16 MiB
```

A reader cuts frames out of the bytes as they arrive, so several frames in one read
and one frame across several are the same frames. **Two kinds of bad input are kept
apart by whether a boundary is left to trust.** A length above the limit, and the
channel ending inside a frame, leave none, and the session ends. An empty payload, one
that is not UTF-8 or not JSON, and JSON that is not an object leave the next frame
where it was, and the session answers with a protocol error and goes on.

**A message is a request, a response, or a notification.**

```text
request      = { kind, id, payload }
response     = { kind, replyTo, payload }
notification = { kind, payload }
```

Each side numbers its own requests from 1 up to `2³¹−1`, never reusing one, and stops
rather than wraps once it has used them all; **a side receiving a request whose number is
not above every number that side used before does not run it** and answers a
protocol error, since a request sent twice would otherwise act twice; a response names by `replyTo` a request
of the side receiving it that still awaits one. The numberings are independent, which
is what lets a request of one side stand inside a request of the other — the callback
a synthesizer makes while it is being run. What a message is about beyond that, an
attempt among it, travels in its payload.

**Each side receives in one place.** One listener cuts frames and dispatches: a
response to the request it answers, a request to a handler, a notification to its own
handler. A request never reads the channel itself, since one that did could not
answer a request arriving while it waits. Every message leaves through one writer.

**A message that cannot be taken is answered with `protocolError`**, carrying a code
and a description: as a response where the message is a request whose `id` could be
read, and as a notification otherwise. It is about the message and never about a
program, and a protocol error is never answered in turn. A protocol error whose own payload is not
one is the other side misbehaving, and ends the session rather than refusing a
request.

**The handshake fixes the session.** `hello { protocol, profile, offers, requires }` is
answered by `ready { protocol, profile, capabilities }`, naming the capabilities in
force, which a client checks against what it asked — the same protocol and
profile, every required capability in force, and none it did not offer or require — or by `refused { reason, supported }`, the reason being `protocol`, `profile`,
or `capability` and `supported` what this side can open with. **The lifecycle requests are the protocol itself** — the handshake, `ping` answered by
`pong`, and `close` answered by `closed` — and every open session answers them, whatever
it negotiated. A capability names an optional family of requests beyond them; the set
the handshake put in force is held for the life of the session, and a request of a
family not in force is a protocol error. Only what is implemented is advertised:
protocol `1`, the profile `elaboration`, and the capabilities `modules` and `invoke`
(below); the kernel callbacks of the elaboration profile will be a third. A request
before the handshake, a second handshake, and any request once `close` has arrived are
protocol errors.

| How it ends | Status |
| --- | --- |
| `close`, answered by `closed` | `0` |
| a handshake answered by `refused` | `1` |
| the channel ending or failing unasked, or a frame with no boundary to trust | `1` |
| a defect of the interpreter answering a request, or reached while loading or running what was asked | `3` |
| a manifest given at start that does not read, or names another target | `1`, before the handshake |

**The process ends by having nothing left to do**, the last frame written and the
channel released, never by exiting at once, which would cut off what a pipe had not
yet taken. A client reads the outcome off both what arrived and how the process ended:
`closed` then status `0` is a session closed; `refused` is a session not opened,
whatever status follows; an exit without `closed`, status `0` included, is a session
failed; a protocol error answering a request fails that request, and the session goes
on.

#### Loading modules and applying guest functions

**`steam session [--manifest path]`.** The manifest is optional, as for `run`, and read
before the channel is opened. Without one, a module declaring a foreign a host must
supply is refused where it loads.

| capability | request | answered by |
| --- | --- | --- |
| `modules` | `load { path }` | `loaded { module }`, or `loadFailed { stage, detail }` |
| `invoke` | `invoke { global: { module, name }, arguments: [ token ] }` | `returned { token }`, or `invocationFailed { reason, detail }` with a `class` where the reason is `notAToken` |

Every payload has exactly those fields, and a request whose payload has another shape
is a protocol error rather than a failed load or invocation. A `load` path is resolved
against the session's working directory; a manifest's own specifiers against the
manifest's directory.

**`load`, `invoke`, and `close` run one at a time, in the order they arrived**, not in
the order of their numbers, while the receiver goes on reading. So a module one request
loads is there for the next, one module is never initialized twice, and nothing closes
under a request still running. Once a well-formed `close` has arrived the session is
closing: what arrived before it is finished and answered, and what arrives after it is
refused at once. **A channel lost is not a close**: it is noticed before the next
request is started and wins over the queue, so the request running when it went
finishes and nothing queued behind it starts.

**A request is judged in one order**, the first rule that applies answering: the
envelope; the stage the session stands at; the kind; the capability; and only then the
payload the kind carries.

**A load commits whole or not at all.** The module, its globals, and the foreign entries
reached for it enter the session together; a load failing at any stage — the path
unreadable, the bytes not a `.dmo`, the implementations unreachable, the loader
refusing, a global faulting as it is evaluated — leaves them as they were. Identities
interned on the way, and host modules reached with whatever their top level did, are
not taken back.

**A token is a JSON object the session never reads.** It is held as an opaque value
under a brand of the session's own, so a guest can carry it and return it, and only a
value holding one reads back as one: another opaque value, an array among them, is
`notAToken`, and so is anything else, named by its class alone. The same token coming
back means the same JSON, not the same object. Whether the global holds a function is
asked before it is applied, so `notCallable` is never a defect of the interpreter read
as the program's.

**A fault is the program's and is answered; a defect is the interpreter's and is not.**
A global faulting as it initializes, or a guest faulting as it runs, fails that request
and the session goes on. The interpreter meeting a `Bug` — a state no `.dmo` admits —
or an `Unimplemented` — something it does not carry out — in either ends the session
with status `3` and answers nothing more.

#### What the process makes of the outcome

**This is the interpreter's own convention and not the ABI's**, which fixes only that
the `IO` is executed to completion or that a fault ends the run, and leaves what a
process reports open (above). What follows is what this command does, so that a shell
can act on it; a different front end may choose differently without being
non-conformant.

**Two questions decide the status, and asking them in order makes it total.** Was it
an interpreter bug? If so, `3`, wherever it arose. Otherwise, had the entry point
begun to run?

| | Exit status |
| --- | --- |
| the `IO` ran to its end | `0` |
| **an interpreter bug**, anywhere — while a module initialized, or while the entry point ran | `3` |
| **anything that stopped the program before the entry point ran**: a file that could not be read, bytes the decoder rejected, a module that did not load, a module that faulted while initializing, no entry module, no such global in it, a global holding something that is not an `IO` | `1` |
| **a fault while the entry point ran** | `2` |

Everything but `0` is reported on standard error.

**The split is between what happened and whose it is, and the order is what keeps
them from overlapping.** A bug is asked about first because it is a statement about
the defect rather than about the moment — the program is not what went wrong, and a
script should hear that whether it happened during initialization or during the run.
What is left divides by the moment: **`1` is a program that never started**, which a
caller acts on by fixing what it handed over, and `2` is a program that started and
reached something the ABI admits may fail. Collapsing the three would leave a script
unable to tell a broken build from a program that ran and failed.

**Initialization is where the two questions visibly cross**, which is why it is
named in two rows: a module whose global faults as it is evaluated did not load, so
the program never started and the status is `1`; a bug reached in the same place is
still a bug and is `3`.

#### What the entry point produced is not reported

**The value is discarded and nothing is printed of it.** A front end that type
checks knows the entry point is `IO Unit`, and the value is then the one value there
is; but that is the front end's knowledge and not the command's.

**What the command can check is that the global holds an `IO`, and it checks exactly
that.** A `.dmo` carries no type ([Bytecode](../05-Backend/01-Bytecode.md)), so
`IO Unit` is not a thing to verify here — and the drive loop answers with whatever
the chain produced, which for a program the front end accepted is `Prim.Unit` and
for one it did not is anything at all. **Requiring it to be `Prim.Unit` is not done**:
it would be a type check performed with no types, catching a case a front end already
refuses and refusing a hand-written `.dmo` that a test legitimately wants to run.

## Scope

- **A reference interpreter running on Node**, written as a JavaScript application
- **Its input is a decoded and validated `.dmo`.** The bytes are the reader's
  concern ([Encoding](../05-Backend/02-Encoding.md)), and a module reaches the
  interpreter as tables it can index. Nothing here parses a byte
- **The host's values and the host's collector.** An `Int` is a JavaScript number,
  a `String` a JavaScript string, and what reclaims a value is the host
- **`Rep` is ignored.** Every value is held one way; `Rep` exists for a backend
  choosing a representation per class, and this one chooses none (D31)
- **No just-in-time compilation, no collector of its own, no register allocation,
  no native code generation, and no optimization of the code it runs**

**The interpreter is a JavaScript application rather than a Wasm one** (D38). It
runs where Node runs, a foreign written in JavaScript is callable directly, and one
written in Wasm is reached through a JavaScript adapter. An interpreter compiled to
Wasm would need bridges for strings, closures, continuations, and the JavaScript
FFI before it could run anything, and the REPL gains nothing from them.

## The core and the host

A **host** is what the interpreter runs on and reaches the outside world through.
The **core** is everything an instruction means, and it is written once so that a
second host changes no rule.

**A host is not always a command line.** For a session the compiler opens, the
compiler is the host: an `Elab` operation — unify these two, make a metavariable,
abandon the attempt — is a capability it supplies where another host supplies a
native action ([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)).

| The core holds | The host supplies |
| --- | --- |
| the value representation, the stack, and dispatch | — |
| finding a marker, splitting a segment, applying one again | — |
| the operations of `PRIMS`, whose meaning the ABI fixes | — |
| the `Base` ABI entries it claims, `Base.IO.pure` and `Base.IO.bind` among them | — |
| a registry of names waiting to be filled | the adapter behind each of those |
| the shape of an `IO` value, and the loop that executes one | the actions an `IO` is built from |
| what a fault is, and that it discards the stack | where a report goes |

**The core names nothing of the host** — no dynamic import, no file system, no
path, no console, no clock — because what a program computes is Core's and the
ABI's. An interpreter whose host could decide any of it would give one `.dmo` two
meanings.

## What a value is

This is the interpreter's internal representation and **not a published ABI**: no
`.dmo` depends on it, and a foreign reaches it only through the boundary below.

| | The interpreter holds |
| --- | --- |
| `Int` | a JavaScript number, always an int32 (D37) |
| `Number` | a JavaScript number (D37) |
| `Char` | the integer of a Unicode scalar value (D27) |
| `String` | a JavaScript string, whose meaning is a sequence of scalar values |
| `Boolean` | a JavaScript boolean |
| data | `{ ctor, fields }`, `ctor` being a resolved constructor identity |
| record | a map from a `RuntimeKeyId` to a value |
| variant | `{ key, payload }`, `key` being a `RuntimeKeyId` |
| closure | `{ function, captures }` |
| partial application | `{ callee, args }` |
| continuation | a captured stack segment |
| `IO` | one of `pure v`, `bind io k`, and a native action. **Opaque to the instruction set and not to the interpreter**: no instruction examines one (D25), and the loop that executes one takes it apart |
| a value only a foreign observes | whatever the foreign gave, which nothing here takes apart |

**Everything but a closure's capture vector and a region cell is immutable**, which
is what lets the host's collector be the whole of memory management.

**Literal identity is equality of the value, with a `Number`'s bit pattern deciding
and all NaNs taken as one** (D37). `BRL` implements that rather than the host's
`==`, which identifies the two zeros and separates a NaN from itself.

## Keys, operations, and constructors are interned at load

**An index into a module's table is that file's own.** Two modules may hold the key
`SymbolKey "n"` at different `KEYS` indices, and a record one of them built is
selected from by the other; comparing the two indices compares nothing. The same
holds of `OPS`, since the `perform` and the handler that answers it need not be in
one module.

**At load every `KEYS` entry is interned into a table shared by every loaded
module, giving a `RuntimeKeyId`**, and every `OPS` entry likewise. Equal keys get
one id whichever module wrote them, the mapping from a module's own indices is
built once where that module is loaded, and nothing compares an index afterwards.

What holds an id rather than an index:

| | |
| --- | --- |
| a record's fields, and a variant's key | `RSEL`, `RRES`, `RUPD`, `BRK` compare ids |
| a handler marker's key, and the clauses under it | `PERF` finds a marker by id and a clause by an operation's id |
| a region frame's cell keys | `CGET` and `CSET` find the innermost visible frame declaring an id |

**A constructor resolves the same way.** A data value holds the identity a loader
resolved — the declaring module's name with the constructor's own — and not an index
into the tables of whoever built it. `BRC` in one module dispatches on values
another module constructed, so both must compare one thing.

## The execution loop

The interpreter holds five things.

```text
current activation
stack
module registry
global slots
the intern tables for keys and operations
```

An **activation** holds what one call is running.

```text
function          the function table entry it is inside
registers         one slot per local, the parameters first
closure           the captures CAPT reads
node, position    where it stands in that function's tree of Nodes
```

A **branch is not a call.** `BRIF`, `BRC`, `BRL`, and `BRK` select a `Node` of the
current activation and continue there, and a `JMP` writes its arguments into a join
point's slots as a parallel move and does the same. Nothing is pushed for either.

The control instructions are these. Every other instruction reads and writes
registers of the current activation, and what each one means is where the
instruction set is ([Bytecode](../05-Backend/01-Bytecode.md)).

```text
CALLK d, f, r…   push Resume { current activation, d }, then enter f with the
                 arguments in fresh registers

CALLU d, s, r…   by what s holds and how many arguments it takes
                   exactly       push Resume { …, d } and enter
                   too few       write a partial application into d
                   too many      push Resume { …, d }, then
                                 ApplyRemaining { the arguments past the arity },
                                 then enter with the arity's worth
                   continuation  push Resume { …, d }, then
                                 ApplyRemaining { the arguments past the first }
                                 where there are any, then copy the captured
                                 segment, push it, and resume at its top

TAILK f, r…      enter f, replacing the current activation and pushing no Resume
TAILU s, r…      as CALLU without the Resume: an argument past the callee's
                 arity, or past a continuation's one, pushes ApplyRemaining
                 alone, and the value reaches what is below

RET s            hand s to the top of the stack, by the table below

HNDL d, …        push Resume { current activation, d }, then a region frame where
                 the handler declares cells, then an owner marker, then enter the
                 body's closure
TAILHNDL …       the same without the Resume

PERF d, key, op, s
                 the innermost visible marker whose key is key
                   fast clause   push Resume { …, d }, then a ClauseBoundary
                                 over the distance down to that marker, and call
                                 the clause with the argument; the stack
                                 otherwise stands
                   full clause   push Resume { current activation, resuming after
                                 this PERF, d }, then split at the marker
                                 inclusive — that entry among the removed — and
                                 call the clause with the argument and the segment;
                                 what the clause returns reaches what is below the
                                 marker
```

## The stack

**The host's call stack cannot carry this.** `PERF` searches the stack and splits
it, and a continuation is applied more than once; neither is a nesting of host
calls. So the stack is a structure of the interpreter's own, and **every entry says
what it does with a value that reaches it**.

```text
StackEntry
  = Resume          { activation, dest }
  | ApplyRemaining  { args }
  | HandlerMarker   { key, clauses, return clause, owner }
  | RegionFrame     { cells }
  | ClauseBoundary  { distance to the answering marker }
```

`Resume` is the only entry that carries a destination register. A tail call pushes
none, which is the whole of what makes it a tail call, and `TAILHNDL` differs from
`HNDL` in exactly that.

| A value reaching | What happens to it |
| --- | --- |
| `Resume { activation, dest }` | it is written into `dest` and that activation continues |
| `ApplyRemaining { args }` | it is applied to `args`, and what that produces reaches the entry below |
| an **owner** marker | the region frame below the marker closes first, then the return clause runs with the value, and what the clause produces reaches the entry below |
| a **reinstatement** marker | the marker pops alone and its return clause runs with the value; the frame it stood in is untouched, and what the clause produces reaches the entry below |
| a `RegionFrame` whose owner is gone | it pops with no return clause, and the value reaches the entry below |
| a `ClauseBoundary` | it pops, and the value — a `fast` clause's — reaches the entry below, the `Resume` of the `PERF` it answers |

The three rows about a marker and a frame are the three completion paths, and a marker's `owner` flag is what
distinguishes them ([Bytecode](../05-Backend/01-Bytecode.md)). Nothing in a `.dmo`
carries that flag: an owner marker is one `HNDL` pushed, and a reinstatement is one
that arrived at the bottom of a re-pushed segment.

**Applying a continuation copies the segment.** What is copied is the register array
of each activation in it, the markers, and the region frames it contains — not the
values those hold, which are immutable and shared. This is the one thing a light
interpreter cannot leave out: re-pushing the captured entries instead would let one
application write over the state the next one needs.

**A `fast` clause's body runs on top of the stack and is searched past what it runs
outside.** Core binds the body outside the handler that answered and outside `Ev_k`
between that handler and the `perform`, while the machine leaves both where they
stand, since nothing is captured (D28). The `ClauseBoundary` pushed above the
`PERF`'s `Resume` is what reconciles the two: a search for a marker or a cell
reaching it continues directly below the answering marker, so a handler or a
region `Ev_k` installed is not found, the handler's own region — below its marker
— is, and whatever the body installs above the boundary is found as usual. `PERF`,
`CGET`, and `CSET` read the stack by that one walk ([Bytecode](../05-Backend/01-Bytecode.md)).

**The boundary holds a distance and not a position.** A `full` operation the body
performs may be answered below the handler, and the segment it captures then holds
the boundary together with the marker it measures to; applying that continuation
re-pushes both at another depth, as many times as it is applied, and a position
recorded at the first push would name the wrong entry afterwards.

**A continuation takes one argument, and may be applied to more.** A `handle`'s
answer type is a type like any other and may be a function type, so `k x y` is well
typed and folds to one `CALLU k [x, y]` (D30). The continuation's run-time arity is
one: the first argument is what the resumption resumes with, and the rest is pending
work, which is why its `ApplyRemaining` stands between the caller's `Resume` and the
segment. What the segment returns is then applied to the arguments that were left.

**The activation that performed the operation is inside the segment.** A `full`
clause's continuation begins at the `perform` and not after it, so the `PERF`
pushes that activation before splitting: the `Resume` it pushes carries the register
file, the point after the `PERF`, and the register the operation's value is written
into. Applying the continuation writes the value there and continues from that
point, which is what makes a resumption resume ([Bytecode](../05-Backend/01-Bytecode.md)).

**An over-application's pending work is on this stack too.** An `ApplyRemaining`
stands between the call that produced it and the value it waits for, so a `full`
clause capturing that stretch captures it — which is precisely what leaving it in
the host's call stack would lose.

## Loading, and the REPL's module lifecycle

There is no linker. There is a **persistent registry** of loaded modules, and
loading one is a short procedure against it.

```text
loadModule(dmo):
  every import is already in the registry, and every condition below holds
  intern the keys, the operations, and the constructors it declares
  open a slot for each global it declares, holding nothing
  build the tables of what it declares, under the names it declares them at,
    and the intrinsic `Prim.Unit` beside them
  resolve every reference against those tables and the registry
  initialize the globals in declaration order, against the working registry
  commit the module to the registry
```

**`Prim.Unit` stands among the declarations.** It is the one value the implicit
environment holds, every module may name it, and no file declares it — so loading
puts it in the tables a reference is resolved against, under the identity every
module shares, and **`Prim` is the one module a reference may name without importing
it** ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

**The slots come before the references because a resolved reference is a slot.** A
`GLOBALREFS` entry of this module's own name resolves to the slot this load has just
opened, and so does a `CALLEES` entry over one; resolving either against a registry
that does not hold the module yet is what the order above avoids.

**Initialization runs against a working registry**, which is the persistent one with
the candidate module beside it. It has to: a `run` global's own code reads that
module's constants, calls the closures its earlier `func` globals installed, and
names its own globals through `GLOBALREFS`, all of which need the candidate's tables
and slots to be reachable while nothing of it is yet loaded. The working registry is
private to the load.

**A module is committed only once it has initialized.** One whose initialization
faults leaves the persistent registry as it was, and the working registry is
discarded with it — which is what keeps a failed entry from being visible to the next
one.

**An interned identity is not taken back.** An identity belongs to a name rather than
to a module: two modules writing one key get one `KeyId`, and a failed load leaves at
most an identity nothing refers to. A later module declaring the same name is given
the same identity, which is the rule the tables exist for, so undoing an interning
would buy nothing and would need the machine to count what refers to one.

What loading refuses:

| | |
| --- | --- |
| A module whose name is already in the registry | one name is one module |
| A module under the name `Prim` | that name is Core's own vocabulary, which no file declares |
| A declaration whose qualified name belongs to another module | `CTORS`, `EFFECTS`, `FOREIGNS`, and `GLOBALS` are what **this** module declares ([Bytecode](../05-Backend/01-Bytecode.md)) |
| A constructor whose owner type belongs to another module | a `CTORS` entry comes from a `data` declaration of this module, so the constructor's name and the type it belongs to are both of it |
| Two declarations of one name in one namespace: two constructors, two effects, or two values — a global and a foreign among them | the tables are arrays and a name table is what loading makes of them, so which of two a name meant would otherwise depend on the order they were written in |
| An exported name that is not a value this module declares | `EXPORTS` names its own globals and foreigns, and nothing else |
| Two join points of one function under one name | a transfer names one of them ([Bytecode](../05-Backend/01-Bytecode.md)) |
| A handler declaring one cell twice, or holding two clauses for one operation | a cell is found by its key and a clause by its operation, so either standing twice would leave which one a `CGET` or a `PERF` means to the order of a table. What is compared is the identity and not the index, two indices being able to intern to one |
| An import that is not loaded | nothing is resolved against a module that is not there |
| A reference to a module this one does not import | **a header says which modules a term may name**, and the order modules happen to be loaded in adds nothing to it. This is not the row above: the module may be loaded and still be one this one never imported |
| A global or foreign an imported module does not export | `EXPORTS` holds the value names a module publishes, its initialized globals and its foreign declarations alike |
| A reference that reaches the wrong kind of declaration | a `CTORREFS` entry must reach a constructor, a `FOREIGNREFS` entry a foreign, a `GLOBALREFS` entry a top-level value ([Bytecode](../05-Backend/01-Bytecode.md)) |
| A foreign with no implementation | resolution happens at load, so a program whose foreigns are incomplete does not start. What could have supplied one is a manifest, and the refusal names the foreign rather than the manifest: the declaration is what was unmet (D43) |
| A foreign the interpreter claims, declared at an arity other than the one the ABI gives that operation | the source is selected by name, so nothing else may answer for it, and the declaration is not of the entry it names |
| A foreign a **supplied** table holds at an arity other than the one declared | an adapter is uncurried, so its arity is how many arguments reach it at once, and nothing downstream compares the two. A table assembled from a manifest carries no arity of its own, so this cannot arise there (D43) |
| An operation code the interpreter does not implement | at the profile it claims ([Prim and Base](../06-Modules/02-Prim-and-Base.md)) |

**What a count must be is the declaring module's to say, and this is where the
modules are together.** Every call in the code is read against the declaration it
reaches, so **a call a wrong arity produced is caught here** rather than where it
would run.

**What is checked are the calls and not the interface.** A `.dmi` is not read at
load, and nothing establishes that one was right: an entry no call used is caught by
nothing, and a `PAP` a wrong arity produced passes wherever it is still below the
true one — which is a partial application meaning exactly what it means
([Interface](../05-Backend/03-Interface.md)).

| The code holds | Why |
| --- | --- |
| A `CALLK` or `TAILK` supplying other than the definitional arity the declaring module states, or reaching a global that states none | a known call is a transfer to an entry whose arity is settled (D30) |
| A `PAP` supplying the callee's arity or more, **whatever kind of callee it stands over** — a global, a constructor, a foreign, or an operation | a partial application is what is applied below an arity; at or above one it is a call |
| A `CTOR` supplying other than the constructor's arity, or a `LOADC` naming a constructor that takes fields | a saturated constructor application is what either is |
| An `FFI` or `TAILFFI` supplying other than the arity the foreign declares | a foreign takes all of its arguments at once (D23) |
| A `PRIM` supplying other than the operation's arity | an operation's arity is the ABI's ([Prim and Base](../06-Modules/02-Prim-and-Base.md)) |

**How a global is installed is read against the function it names.**

| The module holds | Why |
| --- | --- |
| A `func` global whose function takes no parameters | a definitional arity counts leading lambdas and is at least one, so a value with none is a `run` global instead |
| A `run` global whose function takes parameters | it is entered with no arguments |
| Either, where the function expects captures | a global installs a closure over an empty capture list: at the top level every free name is a global, so there is nothing to capture |

**A constructor's export is not in the file.** `EXPORTS` holds value names — a
global's and a foreign's — so what a loader establishes about a constructor
reference is that it reaches a constructor some loaded module declares, not that the
declaring module published it. Data abstraction is settled where types are (D22): a compiler resolved
the name against `Σ`, and a `.dmo` is downstream of that. Enforcing it at load would
mean `EXPORTS` carrying constructors, which it does not.

**Each REPL entry is a module of its own**, and the modules accumulate.

```text
Repl.1
Repl.2   imports Repl.1
Repl.3   imports Repl.1, Repl.2
```

**A redefinition replaces nothing.** It is a new module, and it is the front end's
name resolution that sends later entries to the new definition. A closure built
before it keeps calling what it was built against, so a redefinition cannot break a
value the user is still holding.

**A `.dmi` is not read at run time.** It is what a compiler reads in order to emit
a `CALLK`; what the interpreter checks that call against is the declaring module's
own `.dmo`.

### What each mode asks of loading

**Initialization is the evaluation.** A `run` global is evaluated once as its module
is loaded, so a module that has loaded has already computed what its declarations
hold ([Bytecode](../05-Backend/01-Bytecode.md)). A session's request therefore names
a global and reads its slot; there is no second step in which a declaration is run.

| | Session | Run |
| --- | --- | --- |
| one module arrives | loaded against the registry as it stands | the same, for each of the list in turn |
| a load fails | the registry is as it was, and the next input is answered | the run ends, and the entry point is not executed |
| a fault while initializing | the same: the module is not committed | the same, and the run ends |
| what is reported | the value a named global holds | the named entry point's `IO`, executed |

**A session outlives its failures.** That is the whole of why a module is committed
only once it has initialized: an entry that faulted must leave nothing of **the
interpreter's** behind for the next entry to trip over.

**What is unwound is the interpreter's own state and nothing else**, and the
boundary matters because a foreign body may write where the reduction relation
records nothing (D41). Initialization runs a module's globals, a global may reach a
foreign, and a body may write to the host and then refuse — so a refusal that leaves
the registry as it was still leaves that write standing.

| | |
| --- | --- |
| the registry, and the candidate module | unwound. The module is not committed, and nothing of it is reachable |
| the slots the candidate's globals stood in | unwound with it, however many were filled before the failure |
| an interned identity | **not** unwound, and this is deliberate: an identity belongs to a name rather than to a module, so what is left is one nothing refers to and a later module declaring that name is given the same one |
| whatever a host module did as it was reached | **not** unwound. Reaching one runs its top-level, and that happens before an export is found missing, before one is found not to be callable, and before the Stella module that required it is loaded (D43) |
| host state a foreign body wrote before it refused | **not** unwound, and nothing here can unwind it. The write is outside what the interpreter holds |
| anything at all, after a call violating an ABI precondition | **no promise**. What such a call did is unspecified, so what is left to unwind is unknown (D42) |

**Reaching a host module is the earliest of these, and the least recoverable.** An
import is not undone, so a module whose top-level opened a socket or wrote a file has
done it before anything the interpreter could refuse on — a missing export, a value
that is not callable, the Stella module that required it then failing to load. **A session outlives
all of that and keeps what was reached**, which is what makes the next input
cheaper and what makes the effect permanent.

**The last row is a limit on the promise and not a defect to be fixed.** Undoing it
would need the host to offer a transaction over whatever a body touched, which is
exactly what the boundary does not have: an adapter is opaque, and the relation
records neither what it read nor what it wrote. What the session promises is that
**it** answers the next input, not that the world is as it was.

**The contract an entry owes is where this is addressed**, and it belongs to whoever
writes an adapter: a body that may refuse should refuse before it writes. Nothing
checks that, for the same reason nothing checks `#observ(none)` — the assertion is a
contract on the implementer, kept by conformance tests
([Semantics](../03-Typed-Core/06-Semantics.md)).

**The last row is a different kind of limit from the one above it, and the two
should not be read together.** A refusal after a write is a specified outcome whose
effects the interpreter cannot reach; a precondition violation is not a specified
outcome at all, so "the session answers the next input" is not a promise that
survives one. **The session's promise is to programs that respect preconditions**,
which is the same restriction the four properties carry (D42).

### What a report answers with

**A request naming a global is answered with a snapshot of the value it holds, and not
with text.** A snapshot is **structural**:

| The value | The snapshot |
| --- | --- |
| a scalar | itself |
| a constructor | the fully qualified name its declaration gave it, and its fields |
| a record | its fields, each under the key it stands at |
| a variant | the key it carries, with the kind that key stands at, and its payload |
| a closure, a partial application, a continuation, an `IO`, or a value only a foreign observes | what it is, and nothing more |

**This is what a report answers with and not what every boundary carries.** A
compile-time session passes live values: the argument a synthesizer is applied to, the
value it produces, and the answer to an `Elab` request cross as handles on what the
interpreter holds, never as snapshots of one. A snapshot of a handle would say only
that it is a value a foreign observes, and nothing could turn it back into the handle
([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)).

**A snapshot carries names, never the interpreter's own bookkeeping.** No runtime
identity, register, or address appears in one. That is what interning keeps both
directions for: a value carries an identity and an identity is compared rather than
read, so a snapshot needs the way back — a `CtorId` to the qualified constructor name,
a `KeyId` to the key, and an `OpId` to the operation's name where a report names one.
Loading is where those are kept, which is what stops an answer from depending on the
`DEBUG` section, a section a file need not carry
([Bytecode](../05-Backend/01-Bytecode.md)).

Three things a snapshot fixes, each because the alternative loses something a
consumer cannot recover:

| | Why |
| --- | --- |
| **A key keeps the kind it stands at** | a field and a variant's tag of one spelling are two keys (D16), and a snapshot that wrote both as the spelling would make them one |
| **A record's fields stand in the canonical order of their keys**, fixed below | the order the interpreter happened to hold them in is an artefact of when each identity was assigned, and two runs of one program must answer alike |
| **Nothing under a closure, a continuation, or an action is reached** | what is under one is the interpreter's: a capture list, a captured stack, a host action. Carrying them would carry mutable state and cycles, and would make an answer depend on what a debugger wants rather than on the value |

An identity the registry holds no name for is **not** guessed at: what stands in its
place says that the snapshot stopped there.

**The canonical order of keys.** A kind decides first, in the order below, and within
one kind the payload decides:

| Kind | Within it |
| --- | --- |
| a field or an instance name, `SymbolKey` | the spelling, **by scalar value** |
| a variant's tag, `TagKey` | the spelling, by scalar value |
| a tuple's component, `PositionKey` | the number, ascending |
| an effect, `EffectKey` | the module's name by scalar value, then the effect's |

**By scalar value and not by the host's order.** A host compares text by the code
units it holds, which puts an astral character below `U+E000` where a scalar value puts
it above ([Interface](../05-Backend/03-Interface.md)); an answer ordered that way would
depend on what the host holds text in. `RegionKey` has no row: erasure keeps no region
element, so no value carries one (D36).

**A snapshot always stops.** A value may be deeper or wider than anything wants to
read, so a snapshot is taken **within limits the request carries**, a default standing
where it names none.

| The limit | What it bounds |
| --- | --- |
| the depth | how many levels of nesting the snapshot carries. The value at the root is one, and each level under it takes one more |
| the nodes | how many values the snapshot carries in all |
| the items | how many fields or arguments of **one** value |
| the text | how many scalar values of one string |

**Each is a count and none of them is negative.** A request carries them, and one
naming a negative names none of that kind.

**Exceeding one is not an error.** What is not taken is replaced by a marker, and a
string longer than its limit carries the prefix that fits. Four rules make the
result of one value under one set of limits the same every time:

- **The depth is a place and the nodes are a budget.** At the depth limit every value
  under it is a marker, each element of a sequence among them, and the sequence is
  still all of what the value held. The node budget is what a sequence can run out of
- **The budget is spent in the order the snapshot holds**: a constructor's fields in
  the order it was applied, a record's in the canonical order of its keys. So what it
  runs out on is a tail, which the sequence says it is missing, and never an arbitrary
  part
- **A marker costs nothing.** It stands in place of what was not taken rather than
  being something carried, so it spends no node of the budget
- **A sequence cut short says so of itself** rather than through an element of its
  own: a record's fields have no key to hang a marker on, and inventing one would put
  a key in an answer that no value carried

**The limits bound the descent and not only the answer.** Nothing under a value is
descended into once the budget is gone, and no field or argument past the items limit
is descended into either, so how far into a value a snapshot reads is what the limits
decide rather than what the value happens to hold.

**A value the snapshot reaches is read whole, however.** Its identities are turned into
names whether or not the budget has room for it, since one the registry cannot name
stands as a marker whatever is left; every key of a record it carries is looked at, the
canonical order being what decides which fields the items limit keeps; and every scalar
value of a string it carries is read, the length being what says whether the prefix
carried is all of it. **So the cost of a snapshot is the limits together with the width
of the values it does reach, and not the size of what hangs below them.**

**One value gives one snapshot under one set of limits.** Two snapshots of a value are
comparable where the limits they were taken under are the same, and nothing here makes
them comparable across different ones.

**A snapshot is a value and not a handle.** It is immutable, it can be compared and
encoded, and it refers to nothing the interpreter owns — which is what lets the same
answer reach a terminal, a test, and a later encoding alike. The opaque handles a
compile-time session carries are the opposite and stay so: those name a live value
and are not snapshots of one
([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)).

### Printing one

**Text is a layer above the snapshot, and the only one that decides what anything
looks like.** A printer reads a snapshot and no value of the interpreter, which is
what keeps the answer's meaning apart from its spelling: the same snapshot prints one
way in a terminal and another in an editor, and encodes without being printed at all.

**A line shows every character it carries.** A character and a string are written as
literals of one: the delimiter of that literal is escaped and the other delimiter is
not, and a character a line cannot carry stands as the name it has or else as its code
point. Four Unicode categories are what a line cannot carry — a control (`Cc`), a
format character (`Cf`), and a line or paragraph separator (`Zl`, `Zp`) — since a
format character shows nothing and still acts: an override reorders what follows it, a
zero-width space parts a word where nothing is seen, and a tag character carries text a
display never shows. What a terminal would swallow, or act on, is therefore visible
instead.

**Type-directed printing is the front end's.** Steam holds no types (D34), so
printing by a `Show` instance is the CLI's to do beside the type it checked. What the
machine's own printer gives is what a session can say without a type.

## Foreign implementations

A foreign comes from one of two places. **The interpreter itself implements the
`Base` ABI entries it claims** — their meaning is one for every backend and what
they compute over is the interpreter's own representation — and **everything else
comes from the host**: a target entry constructing a native action, and a program's
own foreigns.

The host side is one table, and what it holds is an **adapter**: a host function of
the interpreter's values.

```text
ForeignTable : QualifiedName ⇀ Entry

Entry   = { arity, body }
body    : HostFn (Value…) Outcome                -- synchronous
Outcome = Produced Value  |  Refused reason      -- a refusal is a fault
```

**`HostFn` is a host function and not a function returning a host action**, and the
difference is the exception boundary rather than a matter of notation. A body may
read and write hidden state (D41), so what it does happens **where it is applied**;
a form that applied the function and handed back something to be run later would put
a throw at application outside whatever catches one. Applying and running are one
moment here, and the moment is the interpreter's to enclose.

**The interpreter assembles the table, and a manifest is what it assembles it from**
(D43). A manifest says where a module's implementations are, in terms the target it
names understands; the interpreter reaches them and builds one entry per foreign,
**each in time for the module that declares it** (below)
([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)).

**The table holds an arity beside each body because an arity is what a saturated call
is**, and on the manifest path that arity is **the declared one**. There is no second
number: a manifest carries none, and none can be read off a reached export — on
JavaScript, `Function.length` counts neither a rest parameter nor one with a default,
and an adapter is usually written as one of those.

**So the refusal for a supplied arity that contradicts a declaration does not fire on
this path**, and that is not the check having been removed. It belongs to a table
supplied entry by entry with an arity of its own, which is what an embedder
constructing one in the same process does — a test, above all. Nothing the command
does supplies one.

**What is fixed here and not in the manifest is the shape of an entry.** A manifest
names a module; the export an entry comes from is the foreign's own unqualified name,
so `Js.Console.log` is the export `log` of whatever the manifest says `Js.Console`
is. That derivation is the target's and is stated with the target, not here.

**What is fixed is when the table must be ready, not when it is built.**

```text
the table is complete for a module before that module is loaded
```

**The two modes meet that differently, and they have to.** `run` is given every
module at once, so it can reach everything its declarations ask for before the first
load. A session is given modules one at a time and cannot know at the start which
will arrive, so it reaches for a module's implementations when the module that needs
them arrives.

| | When the reaching happens |
| --- | --- |
| **Run** | once, before the first module is loaded, for the foreigns the given modules declare |
| **Session** | as each module arrives, for the foreigns that module declares |

**Neither is eager over the manifest.** Reaching every module a manifest names would
run the top-level of hosts the program never uses, and a session's manifest is
written for everything a REPL might load rather than for what it did. A manifest
entry for a module nothing declares against is never reached.

**Reaching the same host module twice is not twice the work.** A host reached once
stays reached — that is what an import is — so a session paying per arrival pays once
per host module, not once per Stella module that mentions it.

**Resolution still happens at load and still searches nothing** (below). What changed
is that the table it consults was built by the same process a moment earlier rather
than handed to it.

**An entry the ABI manifest fixes is in no foreign manifest.** The operations and the
two `Base.IO` entries are the interpreter's by name
([Prim and Base](../06-Modules/02-Prim-and-Base.md)), so a manifest covering them
would be a second answer to a question the precedence rule below already settles.

What assembling refuses, all of it before the module that needed it is read:

| | |
| --- | --- |
| A manifest naming a target that is not this runtime's | the payloads are written for a machine that is not this one, and reading past that would be guessing. The same rule a `.dmo` has for an ABI version it does not hold |
| A `formatVersion` this reader does not implement | likewise |
| A manifest that does not read, or that lacks a field the format fixes | the manifest is wrong, and is reported as that rather than as a foreign being absent |
| A module the manifest names that cannot be reached | named, with what the target said about not reaching it |
| A module reached that has no export of the foreign's name | named, with the export that was looked for |
| An export reached that is not callable | the one shape that can be checked, a `.dmo` carrying no type |

**A manifest entry for a module nothing declares against is ignored**, and nothing is
reached for it. What is assembled is what a declaration asked for.

**An adapter returns an `Outcome`, and a host exception is not one of them.** The
interpreter catches what a body throws synchronously and produces a fault of its
own, kept apart from a refusal: the two propagate alike — the continuation is
discarded entire and the run ends — and they are reported apart, one being a failure
the ABI admits and the other a body that broke the contract below. Letting a host
exception escape instead would end a run outside the fault path, with the stack
undiscarded and a session's promise to outlive a failed entry unkept; that promise is
worth more than the candour of not catching. A body that cannot produce a value
should nonetheless refuse rather than throw, which is what the contract asks of it.

**What is caught is the call and not only what the call produced.** A body throwing
where it is applied is the ordinary careless adapter, and it is the case a boundary
drawn one step too late lets through; the `HostFn` above is what puts the
application itself inside the catch.

**An action performed later is not this boundary's.** A body is synchronous, and so
is the action it may return; what a throw at the moment that action runs means
belongs to the drive loop and is answered there.

**An adapter is uncurried.** A saturated call hands it every argument at once, which
is what the `FFI` instruction does and what a `foreign`'s implementation is written
as; currying belongs to the declared type, and a partial application is the
interpreter's to hold ([Modules](../06-Modules/01-Modules.md)).

**No value is held as the host holds it, and the adapter is what bridges that.**
Every Stella value here is in a shape of the interpreter's own — a scalar included,
`VInt 1` being a tagged thing and not a host number — so there is no case in which an
export is the table entry as it stands.

**What makes one out of an export is marshalling, and it is derived rather than
written** (D44). The manifest carries, per foreign, how each argument and the result
crosses ([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)); the boundary
unwraps on the way in and wraps on the way out by that signature, and what an author
writes is an ordinary host function of the host's own types.

**So the adapter is versioned with the interpreter and nobody writes one**: an
implementation is an ordinary function of the arguments the declaration gives it,
and the layer between it and this interpreter is generated from the type. **What an
implementation is not is one thing serving every backend** — the manifest matches a
target to its own implementations, and what a JavaScript one and a Wasm one have in
common is the discipline rather than the code. **Constructing the `Outcome` above is
asked of no one**, that being the generated layer's.

**A value with no way to cross is refused at the declaration** rather than reaching
here. A data value, a record, a variant, a closure, or a continuation is held in a
shape that is not a published ABI and has nothing to be marshalled to; what crosses
for one is a wrapper written in Stella over the transparent thing (D44).

**A `.dmo` says nothing about a foreign's type.** `FOREIGNS` holds a name and an
arity ([Encoding](../05-Backend/02-Encoding.md)), so no check at load can establish
that an implementation and a declaration agree about what crosses between them.
**Which types a `foreign` declaration may carry is the front end's to restrict**, and
it does: only what can be marshalled may be declared, which is checked where the type
still exists (D44). What reaches here of that decision is the signature the manifest
carries; what a loader
establishes is that every name is carried out by something, at the arity its
declaration states.

### Resolution happens at load, and a call searches for nothing

**Every foreign a module declares is resolved where that module is loaded**, so what
a `FOREIGNREFS` entry reaches is the body itself rather than a name to look up
later. The table is consulted once per declaration and never while a program runs.

Two sources carry a foreign out, and **which of them a declaration reaches is
decided by the name alone**.

| The declared name | What carries it out |
| --- | --- |
| one the interpreter claims as an **operation** | the interpreter itself, and the host's table is not consulted for that name at all |
| `Base.IO.pure` or `Base.IO.bind` | the interpreter itself, likewise. Each **constructs** an `IO` value and executes nothing (D25) |
| anything else the table holds | that entry's body |
| anything else | nothing, and the module does not load |

**The two `Base.IO` entries are claimed by the interpreter and are not operations**,
and the rule that separates them is the same one everywhere: an entry returning `IO`
names an implementation rather than being carried out by a code
([Mid IR](../04-MiddleEnd/01-Mid-IR.md)). So a call of either is an `FFI` and not a
`PRIM`, it reaches `FOREIGNREFS` rather than `PRIMS`, and no operation code stands
for it. What makes them the interpreter's all the same is that **their meaning is
`core-runtime`** — executing anything at all requires them
([Prim and Base](../06-Modules/02-Prim-and-Base.md)) — and that what they construct
is the **structure** of an `IO` value rather than a leaf of one.

**A host builds `IO` values too, and that is not the same thing.** An entry whose
declared type returns `IO` returns one, a native action wrapped as an `IO` value, so
the `Native` form is the host's to make and is made all the time. What is reserved
here is the other two forms and what they mean: `Pure` and `Bind` are how a program
sequences actions, the drive loop below is written against exactly those two shapes,
and a host supplying its own `pure` or `bind` would be supplying the loop's own
semantics from outside it.

**Constructing is all either does.** `Base.IO.pure v` is an `IO` value holding `v`,
and `Base.IO.bind io k` is one holding both; neither performs anything, neither
applies `k`, and reduction halts on what they return (D25). Applying `k` is the
drive loop's, below.

**A name the interpreter claims is never reached by the host's table**, whatever
arity either side gives it. Selecting on the name together with an arity would leave
a way around that rule: a declaration of `Base.Int.add` at the wrong arity would
fail to be the interpreter's, fall through to a host entry that happened to hold the
same wrong arity, and run an implementation where the ABI fixes an operation's
meaning for every backend. The source is chosen on the name, and the arity is
checked afterwards, against whichever source the name selected.

| The name selected | The arity is checked against | A mismatch |
| --- | --- | --- |
| the interpreter, as an operation | the arity the ABI gives that operation | refused. The declaration is not of the entry it names, and no other source may answer for it |
| the interpreter, as a `Base.IO` entry | the arity the ABI gives it — one for `pure`, two for `bind` | refused, for the same reason |
| the table, where an entry carries an arity of its own | the arity the declaration states | refused, and reported as the disagreement it is rather than as an absence |
| the table, where it was assembled from a manifest | nothing. The declared arity is adopted, a manifest carrying none and none being readable off a reached export (above) |

**A mismatch is reported as a disagreement because an implementation is there.** An
adapter is uncurried, so an arity is how many arguments reach it at once, and
nothing downstream would find the discrepancy: a call site is checked against the
declaration, and the declaration is what the other side was supposed to match.
Reporting an absence instead would send a reader looking for something that exists.

**The fourth row is the one a program takes**, the third being reachable only where
something in the same process built a table entry by entry. Nothing is lost by it:
what the third row catches is a table disagreeing with a declaration, and a table
with no arity of its own cannot.

**What does not load is the module, however little of it the foreign is reached
by.** A declaration nothing calls stops the load exactly as one on every path does,
which is what keeps an incomplete program from starting
([Bytecode](../05-Backend/01-Bytecode.md)).

**The obligation that falls out of it is the manifest's to meet** (D43). A front end
that type checks knows which foreigns a module declares, and a manifest is where it
writes down what supplies each of them; the interpreter assembles from that in time, so the
table is complete for a module before that module is read — which a run meets by
reaching everything first and a session by reaching what each arrival needs.

**Completeness is checked twice, and the two catch different things.** A build that
emitted a manifest covering every foreign of every module in the program catches an
omission where the source is, with the module and the entry to hand
([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)); the loader catches what
reaches it regardless, since a `.dmo` may arrive from anywhere and a manifest may be
stale. Neither makes the other unnecessary.

### The table holds no effect summary, and the interface file does

**An adapter returns a value, and whether that value is an `IO` is the adapter's
affair.** An entry whose declared type returns `IO` returns one, a native action
wrapped as an `IO` value; the interpreter does not know which entries those are, and
nothing it does depends on knowing. No instruction examines an `IO` value
([Bytecode](../05-Backend/01-Bytecode.md)) — a `FFI` writes one into a register, a
saturated `pap` does the same, and a snapshot reads the value's own form and
descends no further. What takes one apart is the drive loop, which reads the value
rather than the table.

Recording it would also catch nothing. A `.dmo` carries no type for a foreign, so
there is no declaration a flag could be compared against; and the hazard at this
boundary is an adapter that *performs* its action where it should construct one,
which a flag does not see. That is a conformance obligation, below.

**The observational summary is not this table's either, and that is settled rather
than open.** Whether an entry has an observational effect — a hidden read or write,
a fault, an identity anything can observe — is what `#observ(none)` asserts at the
declaration, and it travels to the one reader that needs it, an optimizer, through
the interface file ([Interface](../05-Backend/03-Interface.md),
[Modules](../06-Modules/01-Modules.md)). An optimizer runs long before a `.dmo`
reaches an interpreter, and this interpreter optimizes nothing, so carrying the
summary here would give it no reader.

**Nor could the machine check one.** Presented with a refusal it cannot tell a fault
the declaration admits from an `#observ(none)` entry in breach, and hidden mutation
was never observable from outside to begin with. The assertion is a contract on
whoever implements the entry, kept by conformance tests rather than by anything at
run time.

**An adapter applies no Stella closure.** It may receive one and carry it into what
it returns — `Base.IO.bind` takes `a -> IO b` and stores it in the `IO` value it
builds — but applying one is what `Σ ⊨ G` condition (3) forbids, the reduction rule
for a saturated `foreign` being one atomic step
([Semantics](../03-Typed-Core/06-Semantics.md)). So an adapter needs nothing of the
interpreter but its values, and the interpreter is never re-entered from inside one.

What an adapter owes is that condition: it takes all of its arguments at once,
returns a value of the instantiated result type or refuses, throws nothing, performs
no proper effect and runs no reified computation it constructs, applies no Stella
function value, and terminates. **It has no observational effect only where its
declaration asserts `#observ(none)`**, and then it does not refuse either, faulting
being one of the things that class is defined by. An adapter writing to a mutable
array behind a pure interface asserts nothing and is a conforming implementation
rather than a breach ([Semantics](../03-Typed-Core/06-Semantics.md)).

**A machine cannot tell a permitted refusal from a breach of that assertion**, the
summary reaching neither a `.dmo` nor this table, and hidden mutation was never
observable from outside in any case. Which is right: the annotation is a contract on
whoever implements the entry, and **which route the implementation takes decides
only whose defect a violation is** — a host adapter's where the host supplies it, and
the machine's own where the machine carries the entry out as an operation
([Modules](../06-Modules/01-Modules.md)). An entry whose
declared type returns `IO` **constructs** the action and returns it wrapped as an
`IO` value; performing it there would be the effect escaping at the one boundary the
condition exists to hold, and nothing the interpreter reads would show it.

**The one place a closure is applied from the host side is the drive loop**, which
executes an `IO` value and is outside the reduction relation (D25) — below.

**Two layers, and they stay apart.**

| | |
| --- | --- |
| a foreign invocation | synchronous, and returns a value or faults |
| executing an `IO` action | synchronous likewise: the action is called, and returns a value or refuses |

**The JavaScript backend reaches the same implementations.** It reads the manifest
for the same target, `javascript`, and marshals by the same signatures, so one
implementation serves the interpreter and the generated code alike
([JavaScript](../05-Backend/05-JavaScript.md)). The table itself stays internal: it
holds the interpreter's values, which are not a published ABI.

## The operations

`PRIMS` names operations, and executing a `PRIM` is carrying out the `Base` entry
its code stands for. **What each one means, and which of them fault, is the ABI's
and is one meaning for every backend** — the thirty-four the format carries are fixed in
[Prim and Base](../06-Modules/02-Prim-and-Base.md) — so the interpreter implements
what is written there and decides nothing of its own. A code it does not implement
is a load error rather than something discovered when a `PRIM` runs.

**Carrying one out reaches the host, and the array operations are why.** All but the
four of `Base.Array` compute from scalar arguments alone, and it would be possible to
carry those out without leaving the interpreter; every entry of `Base.Array` reaches the payload
of an array instead — `unsafeNew` allocates one, `unsafeSet` writes into it,
`unsafeIndex` reads what that write left, and even `length` reads a count held
there — so the operation boundary is the same kind of boundary as the foreign one. **It is the same boundary
and not a second**: an operation is how an entry is carried out and not a way of not
being one (D41), so what an adapter owes an operation owes, and the interpreter
holds both behind one path.

**An array is an opaque value.** `Base.Array.Array` is an `intrinsic opaque`, so an
array is carried, returned, and handed back to an operation, and nothing else in the
interpreter takes one apart ([Semantics](../03-Typed-Core/06-Semantics.md)). What
the payload is belongs to the interpreter and to no `.dmo`: a snapshot of one reads
the value's own form and descends no further ([Structural](#printing-one)), and
nothing compares two.

**Reading a slot `unsafeNew` left unwritten violates the precondition of
`unsafeIndex`** ([Prim and Base](../06-Modules/02-Prim-and-Base.md), D42). Nothing
is owed there in either direction: an implementation may detect it and fault, and
may equally not, and both are conformant.

**This interpreter does not detect it**, and that is a decision of its own rather
than a reading of the ABI. Tracking which slots have been written would put a check
on every read, which is the operation a portable array library is built out of, and
what is bought is a diagnostic the specification does not ask for. So no array here
carries an initialization bit and no read consults one. What such a read produces is
consequently not a promise — a reader should not take it for the specification, and
**a backend faulting there is not in breach of anything this document says**. An
index outside the array is a different matter and faults on every backend, the range
being decided before the precondition is reached.

## Executing an `IO`

**Reduction halts once it has constructed a value of type `IO`** (D25). To the
instruction set such a value is opaque; to the interpreter it is one of three
things, which are what the runtime ABI builds.

```text
IOValue
  = Pure Value
  | Bind IOValue FunctionValue
  | Native host action
```

The **drive loop** executes one: `Pure v` yields `v`; a native action is performed
and yields what it gives; `Bind io k` executes `io`, **applies the Stella function
`k`** to the value that comes out — re-entering the interpreter — and executes the
`IO` that returns. Each such application is a run of its own, and it is the only
way the host side enters the interpreter: `k` is a pure arrow (D23), so it performs
no effect of its own and reaches no marker outside that run.

**`k` is a function value and not a closure in particular.** `Base.IO.bind` takes
whatever the type `a -> IO b` admits, which is a closure, a partial application, or
a continuation alike; the loop applies it the way any unknown call applies one.

### The loop is iterative, and this is an obligation rather than a preference

**A `Bind` chain has no bound, and the shape a program builds is the left-nested
one.** `m >>= f >>= g >>= h` is `Bind (Bind (Bind m f) g) h`, so executing the
outermost first descends through every one before anything runs. An executor written
as a recursive function descends the host's own call stack and dies on a chain long
enough — and every small test passes, because the chains a test writes are short.

**So the loop holds its own stack of pending continuations**, and descends and
resumes by pushing and popping it rather than by calling itself.

```text
execute(io):
  pending = []
  loop:
    Bind inner k  →  push k;  io = inner
    Pure v        →  deliver v
    Native a      →  deliver (perform a)

  deliver v:
    pending empty  →  v is the answer
    otherwise      →  k = pop
                      w = apply k to v, which is a run of its own
                      VIO next  →  io = next
                      otherwise →  a state no `.dmo` admits
```

**The last line is a boundary and not a formality.** `k` has type `a -> IO b`, so
what it returns is an `IO`; but a `.dmo` carries no types, and this loop runs beside
hosted foreigns that may be in breach of theirs, so nothing here may assume it. The
same holds of the first argument of `Base.IO.bind`: a value that is not an `IO`
reaches the same classification rather than a second one.

**What that classification is: the class that says the defect is above the
interpreter** — the one `VABS` and an uncallable callee reach ([Failures](#failures)).
It covers two different culprits and the machine cannot tell them apart: a lowering
that built a `Bind` over something that is not an `IO`, and an adapter that returned
what its declaration did not promise, which is a breach of `Σ ⊨ G` condition (3)
([Semantics](../03-Typed-Core/06-Semantics.md)). **It is not a fault**, since neither is a failure an implementation defines — both are
something above the program having gone wrong.

**What the pending stack holds is continuations and not activations.** Applying one
enters the interpreter, which makes a stack of its own and has finished with it
before the loop goes round again; the two stacks never interleave.

### Performing a native action

A native action is the host's, and performing one is calling it.

**What the loop receives is an `ActionOutcome`, and what the host returns is not
one.** A host implementation returns a plain value or a refusal
([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)); the layer generated from
the signature is what turns that into the form below, and it is the same layer that
checks a host value against the kind it is supposed to be.

```text
perform(action, k):                         -- k is what `{ "action": k }` carried
  given = call action
  refusal given   →  Refused reason
  otherwise       →  Produced (marshal given by k)
```

**A refusal is recognised by the helper's own brand**, never by shape. A brand the
runtime does not know is not a refusal: it is a host value, and the check by `k` is
what it then faces.

```text
HostAction     : HostFn () ActionOutcome         -- performed with no arguments

ActionOutcome  = Produced Value
               | Refused reason                  -- a refusal is a fault
```

**Performing an action returns, and there is no form that asks the loop to wait.**
An action is done when it returns, and the loop goes straight on; the pending stack
is what carries the rest of a `Bind`, and nothing suspends it.

**That the boundary is synchronous is a decision of the language and not of this
loop.** Stella fixes no meaning for asynchrony — no type, no effect, and no operation
says what waiting would be — so an outcome that carried a promise would oblige this
loop to have an answer the rest of the specification does not
([Open Questions](../99-Open-Questions/01-Open-Questions.md)). **Nothing here tests
for a thenable** either: a promise a host hands back is an opaque value like any
other, which is what lets a handle, a buffer, or a connection cross as itself.

**A refusal is how an action fails without throwing**, and the contract asks that it
be used: an action that cannot produce a value refuses rather than raising.

**`HostAction` is a `HostFn`**, so the rule the foreign boundary settled applies
unchanged: applying and running are one moment, and that moment is inside what
catches ([Foreign implementations](#foreign-implementations)).

**Two things end an execution here**, and they are reported apart because they mean
different things.

| | What it is | What it is not |
| --- | --- | --- |
| `Refused` | a fault the implementation defines | not a defect in the host, and not confined to entries the ABI specifies as faulting |
| a throw where the action is performed | the same hazard a foreign body has, and caught the same way | not a refusal: the contract asked for one and got an exception |

**Both are faults, and the second is the implementation in breach of its contract**
rather than a fault it defines. They propagate the way every fault does and are
reported apart, which is the same shape a refusal and a throw already have at the
foreign boundary.

**Why these are faults where the `IO` boundary above is an interpreter bug** is
worth stating, since the two look alike and are classified oppositely. **It turns on
whether the culprit is known.** Only a host action produces an `ActionOutcome`, so a
throw there is the host's and nothing else's. A continuation returning what is not an
`IO` could be a lowering's doing or an adapter's, and the machine cannot tell — so
that one is the class that says the defect is above the interpreter without saying
whose.

**This is the boundary the foreign one deferred to.** A foreign body is synchronous
and its throw is a fault of its own; performing a native action is where an action's
own throw is answered, and the two above are what "answered there" meant.

**A fault inside an applied continuation ends the whole execution.** The application
is a run of its own, but a fault discards the stack and ends the run, and the loop
has nothing to deliver to what is pending — so the pending stack is discarded with
it. Nothing catches one, here as anywhere.

### What executing is given, and what it answers

**The loop is asked for rather than reached.** What it takes is the registry and an
`IO` value; what it answers is one of three things.

| | When |
| --- | --- |
| a **value** | the chain ran to its end |
| a **fault** | an action refused or threw where it was performed; or a fault was reached inside an applied continuation — an operation or a foreign failing as the ABI says it may |
| an **interpreter bug** | a state no `.dmo` admits, reached inside an applied continuation or at the `IO` boundary above |

**A load error is not among them.** Loading happens before an `IO` value exists to
execute, and a registry is what this is handed; a module that did not load is one
whose globals hold nothing to run ([Failures](#failures)).

**The latter two are the failures; the value is the normal answer.** That they are
the failures an evaluation run may return is not a coincidence — applying a
continuation is a run, so what a run can end with is what this can end with, less
the load error, which happens before either.

**It is not part of evaluating a term**, and nothing in the instruction set reaches
it: a `FFI` constructing an `IO` writes that value into a register and the
evaluation continues past it (D25). So the two are separate entry points, and which
of them a mode uses is the mode's business — a session answers with the value a
global holds and executes one only where a request asks, and the run mode executes
the entry point's.

**A session does not execute an `IO` of its own accord.** Recognizing one is not the
difficulty — an `IO` value is one of the three forms above, and the interpreter can
see which. What it cannot know is whether the value was meant to be run: a `.dmo`
carries no types, and a session keeps evaluating an entry and executing an action
apart on purpose. So an entry whose value is an `IO` is answered as one, and
executing it is asked for: by a request of its own in a session, which is what a
`:run` becomes, and by the invocation of `main` in the run mode.

## Failures

Three kinds, reported differently because they mean different things.

| | What it is | What it means |
| --- | --- | --- |
| **Load error** | an unresolved reference, an arity that does not agree, a missing foreign | the module is not loaded, and nothing of it ran |
| **Fault** | an operation or a foreign failing as it is specified or defined to; a native action refusing; a native action in breach of its contract, throwing where it is performed; and a foreign or a native action answering with a host value the kind its signature gives cannot be, which names the entry ([Foreign Manifest](../05-Backend/04-Foreign-Manifest.md)) | the stack is discarded and the run ends; nothing catches one ([Bytecode](../05-Backend/01-Bytecode.md)). Where a drive loop was executing, its pending continuations are discarded with it |
| **Interpreter bug** | reaching `VABS`, applying what is not callable, reading a register that holds nothing, a `Bind` over what is not an `IO` | a state no `.dmo` admits. Reaching one is a defect in the interpreter, in lowering, in a check a loader owes, or in an adapter that returned what its declaration did not promise |

The `DEBUG` section is where a report finds a function's name in a file that carries
one ([Bytecode](../05-Backend/01-Bytecode.md)). How much more a report holds — a
stack trace, a source span — is the REPL's to decide and is not fixed here.

## What Steam owes

The ten obligations of a consumer of a `.dmo` are Bytecode's, and Steam meets
(3) — a continuation applicable any number of times — as the JavaScript backend
does and the v0.1 Wasm backend does not.

Two of them are the ABI's and are worth stating as this interpreter's:

- **The `Base` profile it claims**, recorded in its backend manifest. Executing
  anything at all requires `core-runtime`, which is `Base.IO.pure` and
  `Base.IO.bind` ([Prim and Base](../06-Modules/02-Prim-and-Base.md))
- **The entries of a target root, where its host can supply them.** A target entry
  is what constructs a native action, and on Node it is an ES module export like any
  other host foreign
