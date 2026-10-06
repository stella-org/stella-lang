# The `.dmi` interface file

A `.dmo` is one of a pair, and beside it stands the **`.dmi`**, the interface of
the same module ([Bytecode](01-Bytecode.md)). Compiling a module reads the `.dmi`
of each module it depends on; a `.dmo` is read only to link or to execute.

**A `.dmi` holds the module's whole interface**: what a module contributes to the
build environment once it is compiled — what it publishes, every declaration with
its Core types, its implicit handlers, what it publishes to the catalog alone, and
its arities ([Modules](../06-Modules/01-Modules.md)). Name resolution and
elaboration of a module downstream read it, and so does translation. **What
optimization across a module boundary wants beyond that is settled when the
optimizer is written** (D34): the bodies eligible for inlining are not here.

## What it holds

| Part | Holds |
| --- | --- |
| Module | The module's name |
| Imports | The modules its header imports, which are its dependencies (D22) |
| Exports | The names it publishes, one table per namespace — value, type, operator, type operator, macro, attribute — each the name as an importer writes it, the entity it stands for, qualified by the module declaring it, and the way it came: declared, or imported from a module and re-exported; a type's members; and the modules it re-exports whole |
| Values | Every value it declares — a value, a computation, a foreign with its observation, a handler, a constructor with the type it builds, an operation with the effect declaring it — with its scheme and its attributes |
| Types | Every type it declares — a data type or newtype with its parameters and each constructor's fields, a synonym with its parameters and its body, a foreign type — with its kind and its attributes |
| Effects | Every effect it declares, with its parameters, each operation's own type variables, arguments, and the type it resumes with, and its attributes |
| Operators, type operators | Every fixity it declares: the associativity, the precedence, and what the operator stands for |
| Attributes | Every attribute it declares: its positional parameter types, and its keyword parameters with their types and defaults |
| Implicit handlers | Each handler it declares `implicit`, with the element it handles and the elements it performs in its place |
| Catalog only | The values it publishes to the catalog without exporting them to source |
| Arities | The definitional arity of each value it declares that a module downstream can reach, where it has one |
| Build hash | Where one was computed, the module's build hash |

**The declarations are every top-level declaration of the module**, and not only
those it exports: an exported scheme may mention a type the module keeps abstract,
and Core refers to an entry published to the catalog alone. Which names source may
write is the export tables' to say.

**A module re-exporting a name holds the name and the way it came, and nothing of
the entity.** `B` re-exporting the `f` of `A` holds an export of `f` standing for
`A.f`, imported from `A`; what `A.f` is stands in `A`'s file alone. So a module
downstream of `B` reads `A`'s file as well, and a build environment holds the file
of every module the imports reach, directly or through the imports of those
imported.

**An elaboration-only entry is a declaration like any other here**, under its
internal name beginning with `$`: the constructor of `Base.Continuation` is among
that module's values, and no export names it. A reader building the environment
source names resolve against, an editor's completion, or a list of a module's API
leaves it out ([Modules](../06-Modules/01-Modules.md)).

**The build hash is about the file, not the module.** What compiling a module
produces depends on more than the types and exports of what it imports: a
synthesizer may find an entry a module reaches only transitively, and a macro or a
synthesizer a dependency carries decides what elaborating it produces
([Elaborator API](../02-Surface-Language/03-Elaborator-API.md)). So the hash is
recursive, over the compiler's version, the options that change what is produced —
the target, the ABI and profile, and any feature that changes meaning — the
module's own source, and each direct dependency's identity with its hash, taken in
a fixed order and with the hash field itself left out of the input. A change
anywhere a module reaches changes its hash, and rebuilding it is decided from that
alone. How the hash is computed and compared is settled with the package manager;
until then the file carries one as bytes it does not read, and none where none was
computed.

## Arities

`callk` names a top-level value together with its definitional arity, which is the
number of leading lambdas its erased right-hand side has
([Translation](../04-MiddleEnd/02-Translation.md)). For a value of the module
being translated that is read off the right-hand side. For an imported one there is
nothing to read: a signature gives the type, and **a type does not give the
arity** — `Int -> Int -> Int` is the type of a value of arity 2, of arity 1
returning a closure, and of one evaluated at initialization alike. The arities are
the one part of the file no type carries.

### An absent arity and a wrong one are not alike

**Absent an arity a call is `callu`**, which is correct for every callee. So what
an arity buys where the file is silent is **sharpness**: a module compiled without
the arity of a callee computes what it would have computed with it, through calls
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

A build that writes the pair takes the arities from the Mid IR module it lowers, so
the two agree by construction. What the call-site check is for is a `.dmi` that has
gone stale beside a recompiled `.dmo`, or one that never came from the module it
claims.

### Which values have one

**A value the module declares and that a module downstream can reach**: one it
exports under its name, a macro it exports in the macro namespace, and a value an
operator it declares and exports stands for. Core names are fully qualified, and
what source can reach is what an export list publishes (D22). **A value the module
re-exports has no entry**: it is another module's, and its arity stands in the
file of the module declaring it. **Nor has a value published to the catalog
alone**: Core may refer to one, a synthesizer having inserted a reference to it, and
its arity is left out, so a call to it is a `callu` — correct for every callee, and
what an absent arity always costs. A constructor has none, a linker finding it
among the constructors a `.dmo` describes.

**An arity is at least one, and a value of none has no entry.** A definitional arity
counts leading lambdas, so zero is what absence would be, and absence is not zero:
a `nonrec alias = Main.f` stores a function of `Main.f`'s arity, and reading zero
there would make every call to `alias` an over-application of a nullary function.

## The effect summary of a foreign

**What optimization will want first is an effect summary per exported foreign.** An
entry pure in its type may still write to memory, and may still fault, so a call of
it whose result nothing reads is not dead — and the type says so nowhere, which is
why the fact has to cross the boundary with the module that declares it. It is read
off this file rather than a `.dmo`: an optimizer reads it before a `.dmo` exists,
and an interpreter, which performs no optimization, would never read it
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

**The file holds what the summary is derived from, and not the summary.** A foreign's
value entry carries its observation and its scheme, and the summary is computed from
the two wherever it is read, so it cannot disagree with the declaration it
summarizes.

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

**The layout is a `.dmo`'s**: a header, a string table, and sections whose ids ascend
([Encoding](02-Encoding.md)). The primitives are the ones that document fixes: a
`uvar` is minimal and carries at most 32 bits, an `svar` is a zigzag over it, an
`f64` is eight bytes with every NaN the one quiet NaN, a structural value is at most
`0x7FFFFFFF`, and text is well-formed UTF-8 holding no surrogate.

```text
magic            "DMI\0" — the bytes 0x44 0x4D 0x49 0x00
format version   uvar — 1, the version this document describes
flags            uvar — 0
ABI version      uvar byteLength, then that many bytes of UTF-8
section*         u8 id, uvar byteLength, then the payload
```

**The ABI version is the `.dmo`'s.** A file carries Core types naming the intrinsics
of `Prim`, and foreigns whose observation an optimizer acts on, and what those mean
is that version's; a reader holding another version reads none of it.

| Id | Section | Payload |
| --- | --- | --- |
| `0x01` | `STRINGS` | `vec(text)`: every name in the file is an index into it |
| `0x02` | `MODULE` | the module's name |
| `0x03` | `IMPORTS` | `vec(module)` |
| `0x04` | `EXPORTS` | the value, type, operator, type operator, macro, and attribute tables, each a map from a name, then `vec(module)` of the modules re-exported whole |
| `0x05` | `VALUES` | a map from a name to a value entry |
| `0x06` | `TYPES` | a map from a name to a type entry |
| `0x07` | `EFFECTS` | a map from a name to an effect entry |
| `0x08` | `OPERATORS` | a map from an operator to its fixity |
| `0x09` | `TYPE_OPERATORS` | the same, for type operators |
| `0x0A` | `ATTRIBUTES` | a map from a name to an attribute declaration |
| `0x0B` | `IMPLICIT_HANDLERS` | `vec`, in the order declared |
| `0x0C` | `CATALOG_ONLY` | a map from a name to nothing |
| `0x0D` | `ARITIES` | a map from a name to `uvar arity` |
| `0x70` | `BUILD_HASH` | `uvar byteLength`, then the hash; absent where none was computed |

**The sections `0x01` to `0x0D` that format 1 defines are all required**, empty or
not. No other id below `0x70` is defined, and a reader rejects one where it stands. **An id at or above `0x70` carries no meaning** and a reader
skips one it does not know: the build hash stands there because nothing reads it to
decide what the module means. A section that bears on name resolution, type
checking, or optimization is one below the boundary, or a new format version.

**A name is an index into the string table, and a qualified name is two**: the
module, then the name within it. A module speaks for itself, so the names of its
own declarations are unqualified.

**A map is written in ascending order of its keys**, compared by their scalar values
rather than by a host's order, which is the order of the bytes of their UTF-8. A
reader rejects keys that do not ascend, which is also what refuses a key twice. An
array keeps the order that means something: the constructors in the order of their
tags, the operations as declared, the arguments of an attribute as normalized.

**The string table is in order of first use**, the sections written in the order of
their ids and each in the order above. With the maps ordered, one interface has one
file, and a build may compare two by their bytes.

**Every form is a tag byte followed by its parts**, each part encoded as its own
form. An optional part is `0` for none, or `1` followed by it; a boolean is `0` or
`1`.

| Form | Tags |
| --- | --- |
| kind | `0` a kind variable, `1` `Type`, `2` `Effect`, `3` `Row` then `0` for `Type` or `1` for `Effect`, `4` an arrow |
| type | `0` a variable, `1` a constructor with its kind arguments, `2` an application, `3` `forall` with the variable and its kind, `4` a constrained type, `5` the empty row, `6` a row extended by an entry, `7` the union of two rows |
| row entry | `0` a key and a type, `1` an effect and its arguments, `2` a labelled effect instance, `3` a region and its cells |
| row key | `0` a symbol, `1` a tag, `2` a position, `3` an effect, `4` the region |
| constraint | `0` `k ∉ ρ`, `1` `ρ1 # ρ2` |
| scheme body | `0` a type, `1` a computation's result and row, `2` `forall`, `3` a constraint, `4` a synthesized parameter — its name if written, its dictionary type, its synthesizer |
| value sort | `0` a value, `1` a foreign then its observation, `2` a handler, `3` a constructor then its type, `4` an operation then its effect |
| observation | `0` it may observe, `1` `#observ(none)` |
| type sort | `0` a data type — parameters, constructors, and whether it is a newtype — `1` a synonym, `2` a foreign type, `3` an intrinsic and its canonical class |
| canonical class | `0` literal, `1` function, `2` record, `3` variant, `4` opaque |
| export's way | `0` declared, `1` imported from a module |
| type export | `0` a type, `1` an effect |
| associativity | `0` `infix`, `1` `infixl`, `2` `infixr` |
| fixity target | `0` a value, `1` a constructor; for a type operator `0` a type constructor, `1` a synonym, `2` an effect |
| constant | `0` a literal, `1` a value, `2` a constructor and its arguments, `3` a record |
| literal | `0` an `Int` as `svar`, `1` a `Number` as `f64`, `2` a `String` as an index, `3` a `Char` as its code point, `4` a `Boolean` |

A scheme and a kind scheme lead with the kind variables they quantify; a type
variable binder is a name and a kind.

## What a reader rejects

| The file | Why |
| --- | --- |
| Other magic, a format version it does not implement, or another ABI version | It is not a `.dmi` this document describes, or what it names means something else |
| A flag bit it does not know | What it would ask for is not implemented |
| A required section missing, sections out of order or repeated, an unknown id below `0x70`, a payload that does not end where its length says | As in a `.dmo` ([Encoding](02-Encoding.md)) |
| A tag it does not know, or an index outside the string table | Nothing it could read stands there |
| A varint that is not minimal, over five bytes, or over 32 bits; a structural value above `0x7FFFFFFF`; a count or a length above what is left of the file | As in a `.dmo` |
| Ill-formed UTF-8, a surrogate, or a `Char` that is no scalar value | A name and a literal are text a Stella `String` could hold (D27) |
| An arity of zero | A definitional arity is a count of leading lambdas and is at least one; a value with none is not listed, and absence is not zero |
| A map whose keys do not ascend, a repeated key among them | The order is the format's, and one interface has one file |

**What a reader checks is the bytes, and not the interface.** Whether a type is well
kinded, whether an export names a declaration that exists, and whether an arity is
the one the declaring module's `.dmo` states are not its questions: the first two
are the build environment's and the type checker's, and the last a loader's,
through the calls a translation produced (above).

## What an encoder refuses

**What an encoder writes, a decoder returns.**

| The interface holds | Why |
| --- | --- |
| A name carrying an unpaired surrogate | A name is text a Stella `String` could hold (D27), and no reader may read what is not |
| An arity below one | A definitional arity counts leading lambdas; a value with none is absent from the table |
| A precedence or a row position below zero | Each is a count, which a reader reads as one |

None arises from the ordinary route: a translation gives a global installed as a
function an arity of at least one, a precedence is written as decimal digits, and a
name reaching an interface came from a lexer. **A name is not yet a type that
carries the invariant**, though — a `ModuleName` and an `Ident` are text — so an
interface assembled by hand is where the refusals do their work, as the same refusal
does for a `.dmo` ([Encoding](02-Encoding.md)).

## Where it comes from

**The interface of a module written in source is decided in three places, and assembled from them.**

| Part | Decided by | Holds |
| --- | --- | --- |
| Surface | name resolution | the module's name and imports, its exports, what each declaration is and its members — a data type's constructors, an effect's operations — its fixities, its attributes with their arguments normalized, its attribute declarations' keyword parameters and defaults, which handlers are `implicit`, what it publishes to the catalog alone, and each foreign's observation |
| Core | elaboration | every scheme and kind, a data type's parameters and constructor fields, a synonym's parameters and body, each operation's signature, each attribute parameter's type, and what each implicit handler handles and performs |
| Arities | lowering | read off the Mid IR module the `.dmo` is lowered from: a global installed as a function has the number of parameters of the function table entry it names, and one evaluated at initialization has none ([Mid IR](../04-MiddleEnd/01-Mid-IR.md)) |

**The parts are keyed by the declarations, and assembling them checks that they
speak of one module.** An interface is made only where the checks pass.

| The parts | Why |
| --- | --- |
| A value, type, effect, attribute declaration, or implicit handler the surface part holds and the Core part does not, or a Core entry for none | Each of these has one entry, made of both parts; a fixity is the surface part's alone |
| A type declaration of one sort in one part and another in the other | A data type's fields, a synonym's body, and a foreign type's nothing are not interchangeable |
| A data type with another number of constructors in each, an effect with another number of operations, an attribute declaration with another number of parameters | The two are joined member by member |
| An arity of a value the module does not declare, or that no module downstream can reach; an arity below one | See [Which values have one](#which-values-have-one) |

### A module written in Core

**A module written in Core has a canonical interface, read off the module and its checked signature.** Such a module has no source and so no surface part: `Base.Int`, `Stella.Syntax`, and the modules the compiler or a test writes in Core. Its interface is `Stella.Compiler.Interface.FromCore` applied to the module, what checking it declared, and the arities of its translation. It is a projection of what Core holds, and no inverse of a surface part: what Core keeps nothing of is given one value.

| What | In the interface |
| --- | --- |
| a top-level value | a value |
| a foreign | a foreign that may observe, Core holding no `#observ(none)` |
| a data type, its constructors | a data type with its parameters, and its constructors in the order of their tags |
| an effect, its operations | an effect, each operation taking its one Core argument as its one argument |
| an intrinsic type the signature holds under the module's name | an intrinsic type of the module, with its canonical class: `Stella.Syntax`'s `OriginRef` |
| an attribute declaration | an attribute declaration |
| an exported value carrying `Prim.macro` | a macro exported in the macro namespace, and no value exported; declared as any value is |
| fixities, implicit handlers, entries published to the catalog alone, synonyms, foreign types | none |

**What the module owns is what the checked signature holds under its name**, and nothing of an import or of `Prim` is. An intrinsic type the signature holds under the module's name is the module's as a declared type is; a data type there must have the module's Core declaration behind it. **A projection is refused** where a data type in the signature has no declaration of the module, where an export names nothing the module declares, and where an arity is of a value no module downstream reaches or is below one, as an assembled interface's arities are checked. **A module written in source is never projected so**: its interface is assembled from the three parts above, which hold what Core has lost.

## What reads it

**Name resolution and elaboration read a build environment** made of the interfaces
of the modules a module depends on, every module the imports reach among them
([Modules](../06-Modules/01-Modules.md)). A name resolves through the export tables
of the modules the header imports, and what it stands for is read from the file of
the module declaring it.

**Translation reads a checked environment of arities, not a collection of files.**
An interface a compiler holds need not have come through a reader of these bytes,
and a wrong arity is a soundness matter rather than a performance one, so the
reader's condition on an arity is checked again where the interfaces are gathered,
together with one thing beyond it.

| The interfaces hold | Why |
| --- | --- |
| An arity below one | Translation splits an application spine at the arity it is given; at zero a saturated call becomes a `callk` of no arguments, and below zero it becomes nothing that can be split |
| Two interfaces of one module | Which arity each of that module's names has would otherwise depend on the order the two were read in |

The gathering is the only thing that builds that environment, so a translation
cannot be handed an arity nothing checked. **What it checks is the arity and nothing
else**: whether the bytes are well formed is a reader's question, and whether an
arity is the one the declaring module states is a loader's.

**An arity is read for the modules the one being translated depends on**: those it
imports, and those each of them imports in turn. A name a term carries is qualified
by the module declaring it, which is among them, whether the term reached it through
an import of that module or through a re-export, so a re-exported value is called
with the arity its declaring module publishes. **A module outside the dependencies
sharpens nothing**, and nor does the module being translated: the arity of its own
values is read off their right-hand sides, and an interface claiming one for a value
that has none, a `nonrec` holding a function rather than being one, would make a
`callk` of a call that must stay a `callu`. An interface that is not consulted is not
refused: an absent arity costs nothing.
