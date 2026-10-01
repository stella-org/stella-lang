# The `.dmi` interface file

A `.dmo` is one of a pair, and beside it stands the **`.dmi`**, the interface of
the same module ([Bytecode](01-Bytecode.md)). Compiling a module reads the `.dmi`
of each module it imports; a `.dmo` is read only to link or to execute.

**What a `.dmi` carries is settled when the optimizer is written** (D34), its
content being determined by what optimization across a module boundary turns out
to require. What it carries **now** is the one thing a compiler already needs of
an imported module and cannot obtain otherwise: the **definitional arity** of each
value it exports.

**Format 0 is therefore not yet the whole interface.** An importing module is type
checked against the signature of each import, and format 0 holds no types: a
compiler obtains `Σ` as it does today, from the modules it has in hand, and reads a
`.dmi` beside it for the arities. What D34 describes is the file this one grows
into — it takes over the signature when Core types are serialized
([Open Questions](../99-Open-Questions/01-Open-Questions.md)), and separate
compilation rests on the pair from then on. Until that, a `.dmi` is a sidecar and
says so.

## Why an arity is the minimum

`callk` names a top-level value together with its definitional arity, which is the
number of leading lambdas its erased right-hand side has
([Translation](../04-MiddleEnd/02-Translation.md)). For a value of the module
being translated that is read off the right-hand side. For an imported one there is
nothing to read: a signature gives the type, and **a type does not give the
arity** — `Int -> Int -> Int` is the type of a value of arity 2, of arity 1
returning a closure, and of one evaluated at initialization alike.

### An absent arity and a wrong one are not alike

**Absent an arity a call is `callu`**, which is correct for every callee. So what
this file buys where it is silent is **sharpness**: a module compiled without the
`.dmi` of an import computes what it would have computed with it, through calls
that resolve their arity at run time.

**An arity that is wrong is a different matter, and it is not a matter of
performance.** Translation splits an application spine at the arity it is given, so
an arity of 1 where the entry takes 2 makes `f a b` a `callk` of one argument
followed by a `callu` of the other, and a `callk` is a transfer to an entry point
whose arity is settled: no test follows it. `Σ` cannot catch it either, a type not
determining the definitional arity.

**What a wrong arity produces is rejected where the two modules are together.** A
loader reads every `callk`, and every `pap` over a global, against the arity the
declaring module's `.dmo` states ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)) — which is
where the arity of an imported global is checked at all — so a call that module's own
entry does not admit is a rejected build rather than a call that supplies the wrong
number of arguments. A compiler reading a `.dmi` has no `.dmo` to compare it against
and trusts it, which is why the check belongs there.

**What is rejected is a call at odds with the entry, and not every call a wrong
arity produced.** A `callk` supplies the arity it was given, so one supplying
anything but the entry's is rejected. A `pap` supplies fewer, and is valid against
the entry so long as it supplies fewer than the entry takes: a `pap` of one argument,
where the interface said two and the entry takes three, is the `pap` the true arity
would have produced, it passes, and it means what it would have meant — a partial
application accumulates until it reaches the arity of the entry itself. What is
rejected is a `pap` supplying as many as the entry takes or more, which the entry
would have had called.

**And the check is over the calls rather than over the pair.** A loader reads `.dmo`
files; nothing obliges it to read a `.dmi`, so an entry that is wrong and that
nothing compiled a call from is not caught at all. That is not unsound either: what
a translation did not read changed no call. A build that means to catch a stale
interface before compiling against it compares the two files itself — the arities a
`.dmo` states of its own exported globals are what a `.dmi` of that module holds —
and nothing in either format requires that of a loader.

A build that writes the pair writes both from one Mid IR module, so the two agree by
construction. What the call-site check is for is a `.dmi` that has gone stale beside
a recompiled `.dmo`, or one that never came from the module it claims.

**Absent is not zero.** A `nonrec alias = Main.f` has no definitional arity — what
it stores is a function of `Main.f`'s arity — and reading zero there would make
every call to `alias` an over-application of a nullary function. A value with no
definitional arity is therefore **not listed**, which is what a reader does with
it either way.

## What it holds

| | |
| --- | --- |
| The module's own name | Once, so that the entries need not repeat it |
| Per exported value with a definitional arity | Its own name, and that arity |

**Only exported values.** A downstream module can name nothing else: Core names
are fully qualified and an export list is what data abstraction is (D22). An
elaboration-only entry, the constructor of `Base.Continuation`, is a constructor and
has no entry here, as no constructor has: today it is in the full signature built
from its module, which the Core type checker reads, and a linker finds it among the
constructors a `.dmo` describes. Once this file carries types it carries that entry
too, under its internal name beginning with `$`, and a reader building the
environment source names resolve against, an editor's completion, or a list of a
module's API leaves it out ([Modules](../06-Modules/01-Modules.md)).

**The table is a finite map from a name to an arity**, which is what makes a name
occur once by construction rather than by a rule an encoder must keep: an export
list that names a value twice yields one entry.

**The entries ascend strictly by name**, and that is the format's order rather than
a host's: a name is compared by the bytes of its UTF-8, which is the same order as
by its scalar values, UTF-8 being order-preserving. Two encoders therefore write one
file, and a **reader rejects entries that do not ascend** — which is also what
refuses a name twice, a repeat not ascending.

**An arity is at least one, and a value of none contributes no entry.** A
definitional arity counts leading lambdas, so zero is what absence would be, and
absence is not zero: a global installed as a function over a function of no
parameters is a value whose arity is absent, not a value of arity zero.

**Nothing else, yet.** The exported types belong here too — an importing module is
type checked against the signature of each import — and they wait on a
serialization of Core types, which is open
([Open Questions](../99-Open-Questions/01-Open-Questions.md)). So does everything
optimization will want, the bodies eligible for inlining among them. Until then a
`.dmi` is a header and one table.

**What optimization will want first is an effect summary per exported foreign.** An
entry pure in its type may still write to memory, and may still fault, so a call of
it whose result nothing reads is not dead — and the type says so nowhere, which is
why the fact has to cross the boundary with the module that declares it. This file
is where it belongs rather than a `.dmo`: an optimizer reads it before a `.dmo`
exists, and an interpreter, which performs no optimization, would never read it
([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

**The summary is two fields, and neither is read off the other.**

```text
ForeignSummary = { observational : None | MayObserve
                 , returnsIO     : Boolean }
```

| Field | Where it comes from |
| --- | --- |
| `observational` | `#observ(none)` written on the declaration gives `None`; nothing written gives `MayObserve` ([Modules](../06-Modules/01-Modules.md)) |
| `returnsIO` | derived from the result type, and stated nowhere |

**Faulting is inside `observational` and is not a field of its own.** Dropping a
call that would have faulted removes the fault and reordering two changes which is
taken, so faulting is exactly what the observational class is defined by
([Semantics](../03-Typed-Core/06-Semantics.md)). `#observ(none)` therefore asserts
that the entry does not fault, among the rest of what it asserts, and an entry
without the annotation may fault as it may do anything else.

Grading more finely was considered and rejected. What lies past this boundary cannot
be characterized, and a summary with a field per kind of misbehaviour would describe
what one implementation happens to do rather than what a declaration promises. Two
values is what an optimizer can act on, and the sparing use of FFI is what makes two
enough (D19).

**What an optimizer may do with each.**

| `observational` | What is permitted |
| --- | --- |
| `None` | the call is an ordinary pure computation: dead code elimination, common subexpression elimination, duplication, and reordering, each subject to the ordinary dependency on its result |
| `MayObserve` | the call is preserved, is neither duplicated nor merged with another, and **keeps its position in the original order** |

**A `MayObserve` call is a full sequencing barrier, and the weaker rule of not
crossing another observational call is not enough.** Two cases show why. A
`unsafeSet` moved across a `perform` changes what a handler reading the same array
sees, and a `perform` is not an observational call. A faulting call moved across a
computation that diverges, or across any other transfer of control, changes whether
the fault is reached at all. Neither of the things being crossed is one this summary
describes, so a rule written in terms of this summary alone cannot license the move.

**Keeping the position is the contract to start from, and relaxing it takes a
separate argument.** A move is admissible where what stands between is shown to
terminate, to transfer control nowhere, and to observe no state the call touches —
and none of those three is read off a summary. Treating them as facts to be
established, rather than as the default, is what keeps a first optimizer from being
wrong in a way no test finds.

**`returnsIO` is orthogonal to both rows.** An entry may be `None` and return `IO`,
which is the ordinary shape of a native leaf: nothing happens where it is applied,
and the action it returns is run later by the drive loop
([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

**The route is directive, field, summary.** `#observ(none)` is written at the
declaration; declaration checking records it on the entry in `Σ` and verifies
nothing of it, there being nothing there to verify
([Semantics](../03-Typed-Core/06-Semantics.md)); and this file is where the recorded
fact leaves the module. **The route the implementation takes is not in the summary**:
whether a call lowers to an operation the machine carries out or to a host foreign
is decided afterwards, and an optimizer reads the summary without knowing which
([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

## The bytes

The primitives are the ones [Encoding](02-Encoding.md) fixes: a `uvar` is minimal
and carries at most 32 bits, a structural value is at most `0x7FFFFFFF`, and text
is well-formed UTF-8 holding no surrogate.

```text
magic            "DMI\0" — the bytes 0x44 0x4D 0x49 0x00
format version   uvar — 0, the version this document describes
flags            uvar — 0
module name      uvar byteLength, then that many bytes of UTF-8
arities          vec ( uvar byteLength, that many bytes of UTF-8, uvar arity )
```

**No string table.** No name occurs twice in this file, so a table would buy an
indirection and save nothing. A `.dmo` has one because a name there is reached
from several tables.

**No ABI version.** Nothing here has a meaning that version fixes: an arity is a
count, and no operation, `Rep`, or instruction appears.

**Names are unqualified and the module's own name stands once**, so a `.dmi`
speaks for its own module and cannot claim an arity for a name belonging to
another.

**No sections.** The file is a header and one table, and there is nothing to skip
or to reorder. A **reader rejects a byte after the table**: a longer file is a
later format, not this one with something ignorable at the end, and that is what
keeps a reader of format 0 from reading a file it does not understand as though it
had ended.

## What a reader rejects

| The file | Why |
| --- | --- |
| Other magic, or a format version it does not implement | It is not a `.dmi` this document describes |
| A flag bit it does not know | What it would ask for is not implemented |
| A varint that is not minimal, over five bytes, or over 32 bits; a structural value above `0x7FFFFFFF` | As in a `.dmo` ([Encoding](02-Encoding.md)) |
| A count or a length above what is left of the file | The same, and for the same reason: a few bytes must not cost a reader what they claim |
| Ill-formed UTF-8, or a surrogate | A name is text a Stella `String` could hold (D27) |
| An arity of zero | A definitional arity is a count of leading lambdas and is at least one; a value with none is not listed, and absence is not zero |
| Entries that do not ascend by name, a repeated name among them | The order is the format's, and one module has one file |
| A byte after the table | See above |

**What a reader of these bytes does not check is whether they are true.** Whether
the module exports the name at all, and whether its type admits that many arguments,
are questions for `Σ`. Nothing establishes that an arity is the one the declaring
module's `.dmo` states, either: what a loader establishes is that the `callk`s and
`pap`s a translation produced agree with the modules declaring their callees, which
is what the section above is about.

## What an encoder refuses

**What an encoder writes, a decoder returns.** The table being a map, and an arity
of none being no entry, leave an encoder two things to refuse.

| The interface holds | Why |
| --- | --- |
| A name carrying an unpaired surrogate | A name is text a Stella `String` could hold (D27), and no reader may read what is not |
| An arity below one | A definitional arity counts leading lambdas; a value with none is absent from the table |

Neither arises from the ordinary route: a translation gives a global installed as a
function a definitional arity of at least one, and a name reaching it came from a
lexer. **A name is not yet a type that carries the invariant**, though — a
`ModuleName` and an `Ident` are text — so hand-written Core, and a `.dmi` assembled
by hand, are where the refusals do their work, as the same refusal does for a `.dmo`
([Encoding](02-Encoding.md)).

## Where it comes from, and what reads it

**The compiler writes a `.dmi` from the same Mid IR module it lowers.** A global
installed as a function has a definitional arity, which is the number of
parameters of the function table entry it names; one evaluated at initialization
has none ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)). So the arity is read off the
term once, where the `.dmo`'s own entry is decided, and nothing computes it twice.

**Translation is what reads one.** The arities of the imports are what let a
saturated call to an imported value be a `callk`; without them the same call is a
`callu` ([Translation](../04-MiddleEnd/02-Translation.md)).

**What translation reads is a checked environment, not a collection of files.** An
interface a compiler holds need not have come through a reader of these bytes — a
name and a table of arities are ordinary data — and a wrong arity is a soundness
matter rather than a performance one, so the reader's condition on an arity is
checked again where the interfaces are gathered, together with one thing beyond it.

| The interfaces hold | Why |
| --- | --- |
| An arity below one | Translation splits an application spine at the arity it is given; at zero a saturated call becomes a `callk` of no arguments, and below zero it becomes nothing that can be split |
| Two interfaces of one module | Which arity each of that module's names has would otherwise depend on the order the two were read in |

The gathering is the only thing that builds that environment, so a translation
cannot be handed an arity nothing checked. **What it checks is the arity and nothing
else**: whether the bytes are well formed is a reader's question, and whether an
arity is the one the declaring module states is a loader's.

**An arity is read out of that environment through the import list of the module
being translated.** A term names a value of a module its own module imports, so an
interface of any other module says nothing about a name that term carries — and the
module being translated is one of those others. The arity of its own values is read
off their right-hand sides, and an interface claiming one for a value that has none,
a `nonrec` holding a function rather than being one, would make a `callk` of a call
that must stay a `callu`. An interface of a module that is not imported is not
consulted rather than refused: an absent arity costs nothing.
