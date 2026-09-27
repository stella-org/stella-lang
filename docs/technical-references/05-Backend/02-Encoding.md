# The `.dmo` encoding

[Bytecode](01-Bytecode.md) fixes the instruction set, the sections a `.dmo`
holds, and what each section means. This document fixes the **bytes**: the
encoding of a primitive, the framing of a section, the tag of every form, and
the opcode of every instruction.

The two are separate because they answer to different readers. A backend
generating code needs the meaning of an instruction; a reader of a file needs the
byte that carries it. Nothing here adds to what a `.dmo` holds.

**What is encoded is what `.dmo` names in [Bytecode](01-Bytecode.md) and nothing
besides.** A decoder returns the module a lowering produced, so an encoding
followed by a decoding gives back the module it was handed.

## Primitives

```text
u8          one byte
uvar        an unsigned integer of at most 32 bits, LEB128: seven bits per byte,
            least significant first, the high bit set on every byte but the last
svar        a signed 32-bit integer, zigzag mapped to an unsigned one — n ≥ 0
            becomes 2n and n < 0 becomes -2n-1 — and then written as a uvar
f64         eight bytes, IEEE 754 binary64, least significant byte first
vec X       a uvar count, then that many X
str         a uvar index into the string table
```

**Integers are variable width but not unbounded.** A register, a table index, a
count, and an `Int` constant each fit in 32 bits, and a format fixing four bytes
for every one of them would spend them on a module whose every index fits in one.
LEB128 costs one byte for anything below 128, which is where most of these stand.

A `uvar` is therefore **at most five bytes**, and the fifth carries at most four
significant bits. A reader rejects a sixth byte, a fifth whose value would
overflow 32 bits, and a **non-minimal** encoding — a varint longer than the
shortest one that carries its value. Rejecting the last of these is what leaves
one module one encoding (see [Canonical form](#canonical-form)).

**A structural value is at most `0x7FFFFFFF`.** A count, an index, a register, a
join point's name, a capture or field index, an arity, a tag, a position, a byte
length, and a code point are all structural, and a reader rejects one above that
bound. The bound is one short of the carrier's because these are the numbers a
consumer counts and indexes with, and no module has `0x80000000` of anything: what
the wider carrier exists for is the line below.

**`svar` exists for one form**, the `Int` of a constant, which is the only signed
quantity a `.dmo` holds. Its zigzag reaches `0xFFFFFFFF` — that is what the least
`Int` maps to — so the carrier holds 32 bits while every structural value holds 31.
Everything else is an index, a count, or a register, and none of those is ever
negative.

**Thirty-two bits and binary64 are the domains Core fixes**, an `Int` being a
32-bit signed integer and a `Number` IEEE 754 binary64 (D37), so a `svar` and an
`f64` carry a constant exactly rather than approximating one.

Were a numeric domain ever added, it would arrive as a **constant tag of its own
under a later format version**, which a reader of format 0 rejects rather than
misreads. A format that quietly truncated a value it could not hold would be worse
than one that cannot carry it at all.

**What the container preserves is what literal identity distinguishes**, which is
the bit pattern with all NaNs taken as one (D37). A zero keeps its sign, `0.0` and
`-0.0` being different literals; **a NaN is written as the one quiet NaN**,
`0x7FF8000000000000`, every NaN being one literal
([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

A payload is therefore not preserved, and nothing is lost by that: a distinction
the language does not make is one a file has no business carrying, and a reader
that found one could not say which literal it stood for. A reader accepts any NaN
pattern a file holds and reads it as that one NaN, so a file another encoder wrote
loses nothing either.

What a container must not do is the converse — merge two literals a module held
apart, which would decide a `switchLit` the module did not write.

## Strings

Every string a `.dmo` holds lives in the string table, and every name is an index
into it.

```text
STRINGS payload   vec ( uvar byteLength, that many bytes )
```

The bytes are UTF-8. A `String` constant, a module name, an identifier, a symbol,
a tag, an effect name, and an operation name are each a `str`, so a name that
occurs in several tables is stored once.

**The UTF-8 is well formed, and a reader rejects it where it is not** — an
overlong sequence, a truncated one, a byte no sequence begins, a code point above
`0x10FFFF`, or a surrogate `0xD800` to `0xDFFF`. It substitutes no replacement
character: a string that cannot be read is a file that cannot be read, and a
`switchLit` comparing what a substitution produced would compare something the
module never held.

That a surrogate is rejected is D27 read at the boundary. A Stella `String` is a
sequence of Unicode scalar values and holds no unpaired surrogate
([Prim and Base](../06-Modules/02-Prim-and-Base.md)), so **an encoder handed one
refuses to write the file** rather than producing one no reader may read.

A **qualified name** is two indices: the module and the name within it.

```text
qname   str str
```

Nothing distinguishes an `Ident` from a `TyName` or an `EffName` in the encoding.
Which of them an entry holds is settled by the table the entry stands in, and a
decoder reads the type from there rather than from a tag.

## The header

```text
magic            "DMO\0" — the bytes 0x44 0x4D 0x4F 0x00
format version   uvar     — 0, the version this document describes
flags            uvar     — 0
ABI version      uvar byteLength, then that many bytes of UTF-8
```

The ABI version is written inline rather than as a `str`, the string table being
a section and the header standing before every section.

**A reader rejects a file whose magic is not those four bytes, and one whose
format version it does not implement.** The format version is the version of
this document, which is **0**; a change to what a byte means, to what a tag
admits, or to what a section holds takes the next one.

**The ABI version is the identifier of the manifest the module was compiled
against, compared byte for byte.** The identifier `stella-base-0.1` is that
manifest's exact spelling, lower case throughout, and a reader holding another
version's table rejects the file: an operation's code is that manifest's to fix,
so a version a reader does not hold leaves every `PRIMS` entry without a meaning
([Operation codes](#operation-codes)).

`flags` is zero, and a reader rejects a file setting a bit it does not know. What
a flag would say has not arisen; reserving the field costs a byte and adding one
later costs nothing.

## Sections

```text
section   u8 id, uvar byteLength, payload
```

The sections follow the header, one after another, to the end of the file.

**The ids ascend strictly**, and a reader rejects a file whose sections stand in
any other order. Two things follow from strictness rather than needing rules of
their own: a section cannot appear twice, and an unknown id has one place it may
stand — after every id below it and before every id above.

The order the ids give is the order a decoder reads them, and it is the order in
which one section's indices are resolved before another uses them. `STRINGS` comes
first because every other section indexes it, `OPS` stands before `EFFECTS` and
`HANDLERS`, and `PRIMS` before `CALLEES`.

| id | Section | Required |
| --- | --- | --- |
| `0x01` | `STRINGS` | yes |
| `0x02` | `MODULE` | yes |
| `0x03` | `IMPORTS` | yes |
| `0x04` | `CONSTANTS` | yes |
| `0x05` | `KEYS` | yes |
| `0x06` | `OPS` | yes |
| `0x07` | `CTORS` | yes |
| `0x08` | `EFFECTS` | yes |
| `0x09` | `FOREIGNS` | yes |
| `0x0A` | `CTORREFS` | yes |
| `0x0B` | `FOREIGNREFS` | yes |
| `0x0C` | `GLOBALREFS` | yes |
| `0x0D` | `PRIMS` | yes |
| `0x0E` | `CALLEES` | yes |
| `0x0F` | `HANDLERS` | yes |
| `0x10` | `FUNCTIONS` | yes |
| `0x11` | `GLOBALS` | yes |
| `0x12` | `EXPORTS` | yes |
| `0x7F` | `DEBUG` | no |

**A required section is present even where it is empty**, as a `vec` of no
entries. A reader rejects a file missing one rather than reading the absence as
emptiness, which is what [Bytecode](01-Bytecode.md) asks of it: a module whose
`CTORS` was dropped and one that declares no constructor are different files.

**An id at or above `0x70` carries no meaning, and a reader skips one it does not
know**; an id below it does, and a reader **rejects** one it does not know. The
boundary is what keeps skipping safe: a section that bears on what a module
computes takes a low id, so a reader that has never heard of it stops rather than
running the module without what it says. `DEBUG` stands above the boundary, which
is why a reader that wants none of it passes over it.

Adding a section that bears on meaning therefore takes the next format version as
well as a low id. The version is what makes the refusal legible — a reader says
it does not implement the format rather than naming a section nobody has heard
of — and the id is what makes it happen at all.

`MODULE` holds the name of the module itself, which no other section carries.

```text
MODULE payload        str
IMPORTS payload       vec str
OPS payload           vec str
CTORREFS payload      vec qname
FOREIGNREFS payload   vec qname
GLOBALREFS payload    vec qname
EXPORTS payload       vec qname
```

### Constants

```text
CONSTANTS payload   vec constant

constant   0x01 svar        an Int
         | 0x02 f64         a Number
         | 0x03 str         a String
         | 0x04 uvar        a Char, by its scalar value
         | 0x05 u8          a Boolean, 0 false and 1 true
```

A reader rejects any other tag, and a `0x05` whose byte is neither 0 nor 1.

**A `Char` is a Unicode scalar value**: `0x0` to `0x10FFFF`, less the surrogates
`0xD800` to `0xDFFF`. This is D27 as the container carries it — a `Char` is one
scalar value and a `String` a sequence of them — so a reader rejects a code
outside that set and an encoder refuses to write one. A code above `0xFFFF` is an
ordinary constant here: nothing in the container is a code unit.

### Keys

```text
KEYS payload   vec key

key   0x01 str     a SymbolKey, by its symbol
    | 0x02 str     a TagKey, by its tag
    | 0x03 uvar    a PositionKey, by its position
    | 0x04 qname   an EffectKey, by the effect it names
```

**There is no tag for a region key.** A `KEYS` table holds the keys terms carry,
and no erased term carries a region's: a handler keeps the key of the element it
removes, its cells keep their own, and `CGET` and `CSET` name those (D36).

### Declarations

```text
CTORS payload      vec ( qname name, qname owner, uvar tag, uvar arity, u8 isNewtype )
EFFECTS payload    vec ( qname name, vec str ops )
FOREIGNS payload   vec ( qname name, uvar arity )
```

`isNewtype` is 0 or 1, and a reader rejects any other byte.

**An effect's operations are string indices rather than `OPS` indices.** `OPS`
holds the operations a module's code names, and an effect may declare one that no
code here mentions; were `EFFECTS` to index `OPS`, encoding such a module would
have to add an entry to `OPS` and so renumber the indices its instructions
already carry.

### Callees and operations

```text
PRIMS payload     vec uvar                 an operation, by its code
CALLEES payload   vec callee

callee   0x01 qname   a top-level value
       | 0x02 qname   a foreign
       | 0x03 qname   a constructor
       | 0x04 uvar    an operation, by its index into PRIMS
```

**A `0x04` callee indexes `PRIMS` rather than repeating the code**, so that a
partial application of an operation and the saturated instruction that carries it
out cannot name two different operations. `PRIMS` therefore stands before
`CALLEES`, as `OPS` stands before what indexes it. A reader rejects an index the
table does not hold.

### Operation codes

**An operation's code is the ABI manifest's to fix**, one per operation of the
version the header names, and it is what makes `PRIMS` carry no name: what an
operation realizes is derived from the ABI version and written nowhere else
([Bytecode](01-Bytecode.md)).

The manifest of `stella-base-0.1` fixes these codes, and what each operation
means beside them ([Prim and Base](../06-Modules/02-Prim-and-Base.md)).

| Code | Operation |
| --- | --- |
| `0x01` | `Base.Int.add` |
| `0x02` | `Base.Int.sub` |
| `0x10` | `Base.String.length` |
| `0x11` | `Base.String.codePointAt` |
| `0x20` | `Base.Array.unsafeIndex` |
| `0x21` | `Base.Array.unsafeNew` |
| `0x22` | `Base.Array.unsafeSet` |
| `0x23` | `Base.Array.length` |

Three rules hold of the table, and they are what let a code stand in a file.

**A code is written, never derived.** It is not a position in a list, an
alphabetical rank, or the order a compiler happens to declare its operations in:
any of those would change a published file's meaning when an operation is added.
The array family is where the table already shows it: `unsafeIndex` holds `0x20`
because it was written first, and the two entries added beside it took the codes
after rather than the order a reader would group them in.

**A code is fixed for the life of an ABI version, and a removed operation's code
is not reused.** A later version may drop an operation, and a reader of that
version then rejects the code rather than reading it as another operation.

**A reader rejects a code the version it holds does not name.** That is the same
refusal as an unknown tag: what a code means is not derivable from the file.

Where the ABI specification is written, the table moves there and this section
names it instead. The specification does not exist yet
([Open Questions](../99-Open-Questions/01-Open-Questions.md)), and a format that
carries codes needs them fixed somewhere, so they are fixed here.

### Handlers

```text
HANDLERS payload   vec ( uvar key, vec uvar cells, vec clause )

clause   uvar op, u8 form

form   0x00 full
     | 0x01 fast
```

`key` and each of `cells` index `KEYS`, and `op` indexes `OPS`. `cells` is empty
for a handler declaring no region.

### Globals

```text
GLOBALS payload   vec ( qname name, u8 kind, uvar function )

kind   0x01 run      evaluate the function once and store the result
     | 0x02 func     install a closure over an empty capture list
```

`function` is an index into `FUNCTIONS`. The order of the entries is the
dependency order Core required, and initialization runs it in that order
([Bytecode](01-Bytecode.md)).

## Functions

```text
FUNCTIONS payload   vec function

function   uvar nparams, vec rep regs, vec rep captures, vec join, node

join       uvar name, vec uvar params, node
```

A register is its index into `regs`, a join point's name is the number the
lowering gave it, and a `join`'s `params` are the registers a `JMP` writes its
arguments into.

```text
rep   0x01 Int    | 0x02 Number  | 0x03 Char     | 0x04 String
    | 0x05 Boolean| 0x06 Clos    | 0x07 Rec      | 0x08 Variant
    | 0x09 qname  a value of the data type named
    | 0x0A Opaque | 0x0B Val
```

### A node needs no count

```text
node   instr*, tail
```

**An opcode below `0x80` is an instruction and one at or above it is a `Tail`**,
so a `Node` is read until a `Tail` ends it and carries no count of its own. A
`Node` holds exactly one `Tail` by construction, which is the invariant this
encoding gives for free rather than checks.

A `Tail` that dispatches holds its branches **inline**, as
[Bytecode](01-Bytecode.md) requires: a branch is a `node` in place and never an
offset or a name.

```text
branchNode    node                  held inline
optNode       0x00                  no default
            | 0x01 node             a default
```

## Opcodes

Operands are written in the order they follow the opcode. `d` is a destination
register, `s` a source, `r…` a `vec uvar` of source registers, and an index into
a table is a `uvar`.

| Opcode | Instruction | Operands |
| --- | --- | --- |
| `0x01` | `LOADK` | `d`, constant |
| `0x02` | `LOADG` | `d`, global reference |
| `0x03` | `LOADC` | `d`, constructor reference |
| `0x04` | `MOVE` | `d`, `s` |
| `0x05` | `CAPT` | `d`, capture index |
| `0x06` | `CLOS` | `d`, function, `r…` |
| `0x07` | `CLOSN` | `d`, function, capture count |
| `0x08` | `SETCAP` | `d`, capture index, `s` |
| `0x09` | `PAP` | `d`, callee, `r…` |
| `0x0A` | `CTOR` | `d`, constructor reference, `r…` |
| `0x0B` | `CALLK` | `d`, global reference, `r…` |
| `0x0C` | `CALLU` | `d`, `s`, `r…` |
| `0x0D` | `FFI` | `d`, foreign reference, `r…` |
| `0x0E` | `PRIM` | `d`, operation, `r…` |
| `0x10` | `FIELD` | `d`, `s`, constructor reference, field index |
| `0x11` | `RNEW` | `d` |
| `0x12` | `REXT` | `d`, key, value `s`, record `s` |
| `0x13` | `RSEL` | `d`, key, `s` |
| `0x14` | `RRES` | `d`, key, `s` |
| `0x15` | `RUPD` | `d`, key, record `s`, value `s` |
| `0x16` | `RMRG` | `d`, `s`, `s` |
| `0x17` | `VINJ` | `d`, key, `s` |
| `0x18` | `VPAY` | `d`, key, `s` |
| `0x19` | `VABS` | `d`, `s` |
| `0x20` | `PERF` | `d`, key, operation name, `s` |
| `0x21` | `HNDL` | `d`, handler, body `s`, return clause `s`, clause `r…`, cell `r…` |
| `0x22` | `CGET` | `d`, key |
| `0x23` | `CSET` | `d`, key, `s` |

| Opcode | Tail | Operands |
| --- | --- | --- |
| `0x80` | `RET` | `s` |
| `0x81` | `TAILK` | global reference, `r…` |
| `0x82` | `TAILU` | `s`, `r…` |
| `0x83` | `TAILFFI` | foreign reference, `r…` |
| `0x84` | `JMP` | join point name, `r…` |
| `0x88` | `BRIF` | `s`, branchNode, branchNode |
| `0x89` | `BRC` | `s`, `vec ( constructor reference, branchNode )`, optNode |
| `0x8A` | `BRL` | `s`, `vec ( constant, branchNode )`, branchNode |
| `0x8B` | `BRK` | `s`, `vec ( key, branchNode )`, optNode |
| `0x8C` | `TAILHNDL` | handler, body `s`, return clause `s`, clause `r…`, cell `r…` |

`BRL` carries a `branchNode` rather than an `optNode`: literals cannot be
exhausted, so its default is not optional ([Bytecode](01-Bytecode.md)).

The gaps in the numbering — `0x0F`, `0x1A` to `0x1F`, `0x24` onwards — group the
opcodes by what they touch, so that a reader of a hexadecimal dump can see which
family an unknown opcode was meant to join. A reader rejects one it does not know
rather than skipping it: an instruction's operands are what say how long it is,
and one whose opcode is unknown has no known length.

## Canonical form

**One module has one encoding.** Two encoders handed the same `.dmo` write the
same bytes, and decoding bytes an encoder wrote and encoding the module again
gives those bytes back. Four rules are the whole of it.

**The second half holds of bytes an encoder wrote and not of every file a reader
accepts.** A reader takes a string table in any order and passes over what stands
above the boundary, so re-encoding a file that ordered its strings differently, or
one carrying a `DEBUG` section, yields the canonical bytes for the module it holds
rather than the bytes it was handed. A decoder returns a module, not a file.

**Every varint is minimal**, which is the rule a reader enforces above.

**A NaN is the one quiet NaN.** Every NaN is one literal, so an encoder writes one
pattern for all of them and two encoders cannot differ over which.

**Every table is written in the order the module holds it.** A `.dmo` is an
ordered structure — `GLOBALS` in dependency order, `FUNCTIONS` by identifier, a
handler's clauses as its table lists them — and an encoder reorders none of it.

**The string table is in order of first use, with no string twice.** The order
the sections are written is fixed, and within a section the entries are written
in the order they stand, so first use is determined by the module alone: an
encoder assigns index 0 to the first string the module's own name reaches, and
each later one in turn.

What this buys is a reproducible artefact — one a build can cache by its bytes
and a reader can compare — for the price of interning as the sections are
written, which an encoder does anyway.

**Three of the four are obligations on an encoder alone.** A reader resolves a
string index whatever order the table stands in, reads a table in the order it
finds, and takes any NaN pattern as the one NaN, so it rejects none of the three;
minimality is the one it enforces, and it does so because an overlong varint is
otherwise a second spelling of a value in every position a varint stands. A reader
handed a file from an encoder that ordered its strings differently, or wrote
another NaN, reads the same module out of it.

## What an encoder rejects

An encoder refuses a module it cannot write, rather than writing a file no
reader may read.

| The module holds | Why |
| --- | --- |
| A `String` constant or a name carrying an unpaired surrogate | A Stella `String` is a sequence of Unicode scalar values (D27) |
| A `Char` constant that is not a scalar value | A `Char` is one scalar value (D27) |
| An operation the ABI version it writes does not name | The code is that version's to fix, and there is none |
| A callee naming an operation the module's `PRIMS` does not hold | The callee is written as an index into that table, so there is nothing to write |
| A structural value below zero | A `uvar` carries no sign, so it would be written as a 32-bit pattern and read back as a value no module holds |
| An index no table of the module holds, a register outside a function's file, a capture it does not take, or a jump to a join point it does not declare | None of them would read back as what it was |
| A format version or an ABI version other than the ones it writes | What a byte means is this format's, and what an operation's code means is that version's |

Each is a module the stages before this one should not have produced. Refusing is
what keeps the file honest where one of them does.

**What an encoder writes, a decoder returns**, and the rows above are what make
that a contract rather than a hope: an encoder refuses a module a reader would not
read back, and a reader refuses to return one the bytes happen to describe.

**A negative structural value and an index or a scope naming nothing are found by
one walk over the module, which both directions read.** Two walks would disagree
about some module and each be satisfied with itself. The version is not among what
that walk reads: it is read where each direction begins, an encoder writing one
format and one ABI version and a reader reading the same two.

## What a reader rejects

A decoder reports a file it cannot read rather than producing a module the
encoder did not write.

| The file | Why |
| --- | --- |
| Other magic, or a format version not implemented | It is not a `.dmo` this document describes |
| An ABI version not implemented | An operation's code is the manifest's, so a version a reader does not hold leaves every `PRIMS` entry without a meaning |
| A flag bit the reader does not know | What it would ask for is not implemented |
| A required section absent, or sections out of order | A missing section is not an empty one, and the order is what resolves one table before another |
| An unknown section id below `0x70` | It bears on meaning, and running the module without it would compute something else |
| A section whose payload does not end where its length says | The two must agree, or every section after it is read from the wrong place |
| An unknown tag, opcode, or `form` byte | An unknown form has no known length |
| An unknown operation code | What it realizes is the manifest's, and this reader holds another |
| A varint over five bytes, over 32 bits, or not minimal | The value would not fit the carrier, and a longer form of one that fits is a second encoding of one module |
| A count or a length above what is left of the file | Every item takes at least one byte, so such a count is a file that ends inside the vector. **A reader says so before reserving room for it**: a few bytes must not cost a reader what they claim |
| A structural value above `0x7FFFFFFF` | A count, an index, a register, an arity, and their kin are the numbers a consumer counts with, and none reaches that |
| Ill-formed UTF-8, or a surrogate, in a string or a `Char` | A scalar value is what either holds (D27), and a substitution would hand back what the module never held |
| An index no table holds | It names nothing |
| Input exhausted mid-form | The same |

**What a decoder does not check is what a loader and a verifier check.** Whether
a qualified name belongs to this module or one of its imports, whether a register
is bound where it is read, whether a call supplies a declared arity — none of
that is a property of the bytes ([Bytecode](01-Bytecode.md),
[Mid IR](../04-MiddleEnd/01-Mid-IR.md)). A decoder rejects a file it cannot read
and hands on everything it can.

## What is not encoded

**`DEBUG` is specified as a section and not as a payload.** It holds source
spans, function names, and local names ([Bytecode](01-Bytecode.md)), and what a
span is has not been fixed: an annotation is a parameter of the Core and Mid IR
terms, which these documents fix as a source span without settling its shape. The
names would encode as two maps keyed by function index; the spans wait on that
shape. Until then an encoder writes no `DEBUG` section and a reader skips one it
is handed, which the rule above already provides for.
