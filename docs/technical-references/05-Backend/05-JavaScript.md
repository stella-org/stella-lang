# The JavaScript backend

The JavaScript backend turns a `.dmo` into an ES module (D45). It reads the same
file the machine executes ([Bytecode](01-Bytecode.md)), and it reaches foreign
implementations through the same manifest target the machine does
([Foreign Manifest](04-Foreign-Manifest.md)).

This document fixes what the backend reads, what it owes, and which of its
choices are still open. How a value is represented while a program runs is the
backend's own and is not a published ABI, exactly as it is not for the machine
([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

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
code by one of them and be refused by the other.

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
| an operation | its name | — |
| a constructor | the module that declares it together with its own name | a constructor of the same name in another module |
| an effect key | the effect it names, module included | an effect of the same name in another module |

Obligation (10) of [Bytecode](01-Bytecode.md) is this table, and it binds the
backend as it binds the machine. **A representation that writes a key as its bare
spelling fails it**, a field and a tag of one spelling then selecting each other.

## Structure is emitted, not rebuilt

A `Node` is a straight run of instructions ending in one `Tail`, and a dispatch
holds its branches inline ([Bytecode](01-Bytecode.md)). The backend walks that
tree: a `BRC` or `BRK` becomes a dispatch over resolved identities, a `BRIF` an
`if`, and a join point a construct the enclosing function can transfer to by name.
**Nothing is reconstructed from a control flow graph** (D32).

**`BRL` dispatches by literal identity, which JavaScript's `switch` does not
implement.** A `switch` compares by strict equality, which identifies `0.0` with
`-0.0` and separates a NaN from itself; literal identity does the opposite on both
counts (D37, [Prim and Base](../06-Modules/02-Prim-and-Base.md)). A `switch` is the
right lowering where strict equality and literal identity agree — an `Int`, a
`Char`, a `String`, a `Boolean` — and a `Number` dispatch compares by identity,
`Object.is` deciding the zeros and a NaN test deciding every NaN as one.

**Readable output is not a goal.** A register becomes a JavaScript variable and an
instruction a statement, and what makes the result resemble hand-written code is
optimization over the backend's own representation — propagating a copy, folding
a constant — rather than anything this document requires.

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
either with frames and a run loop of the backend's own, or by converting to
continuation-passing style. Which of the two is open (below); that it is one of
them is not.

## A `fast` clause, and purity

**A `fast` clause is cheap and does not make its context one-shot.** It constructs
no continuation (D28), so the backend lowers it as a call. But its body may
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
not the entry is pure (above).

**The row that decides is the body's, not the first arrow's.** An entry collapses a
run of lambdas ([Translation](../04-MiddleEnd/02-Translation.md)), so
`A -> B -{ ρ }-> C` is one entry of two parameters whose body runs under `ρ`: its
first arrow is pure and the entry is not. A `handle` body and a handler clause are
entries whose bodies run under a row that is in general not empty.

**A `.dmo` does not yet say which functions are pure.** The effect row was erased
before the file exists, and Translation is where it is still known
([Translation](../04-MiddleEnd/02-Translation.md)). Recording it per function is the
first addition to the format this backend is expected to ask for; until then every
function is treated as one that may perform.

## Foreigns, operations, and `IO`

**A foreign implementation is the one the machine calls.** The backend reads the
manifest for the target `javascript`, marshals by the signatures it carries, and
recognises a refusal by the helper's brand ([Foreign Manifest](04-Foreign-Manifest.md)),
so one implementation serves both consumers. The rules of that document apply
unchanged: an adapter is uncurried, synchronous, and checked on the way out.

**An operation is carried out by the backend's runtime**, with the meaning
[Prim and Base](../06-Modules/02-Prim-and-Base.md) fixes. Where that meaning and the
host's operator part, the backend implements the meaning: `Base.Int.mul` is not
`(a * b) | 0`, and `Base.String.lt` is not `<`.

**Executing an `IO` is the drive loop's**, with the shape and the obligations the
machine's has: `Pure`, `Bind`, and a native action, executed iteratively over a
stack of pending continuations ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

## What testing the backend compares

**Running one program on the machine and on the backend tests the backend, and
not lowering.** Both read the `.dmo` lowering produced, so a defect in lowering
reaches both alike and the comparison agrees with itself. What covers lowering
today is its own tests, and execution tests whose expected results are fixed
independently from hand-written Core. Comparison with an evaluator of Typed Core
is what a claim that lowering preserves meaning broadly waits on, and no such
evaluator exists yet ([Implementation Plan](../01-Introduction/04-Implementation-Plan.md)).

What the comparison does cover is the part it is for: the same value, and the
same sequence of observable effects, from the same file.

## Conformance

**D18 records the JavaScript backend as one-shot, and that record stands until
this backend passes the cases that decide it**: a `full` clause resuming its
continuation twice, each resumption beginning from the captured state, and a
continuation captured outside a region carrying the cells it was captured with
([Bytecode](01-Bytecode.md)). The execution model is chosen so that those cases
are expressible; they are what shows it.

## What is open

- **The execution model**: frames and a run loop of the backend's own, or
  continuation-passing style, and how a pure function's call is kept a host call
  under either
- **The representation of a resolved identity**: a key, an operation, and a
  constructor, meeting the table above across separately generated modules
- **How a join point is emitted**: a labelled block, a loop, or a local function
- **The per-function purity record**: its shape in the format, and what
  Translation reads it from
