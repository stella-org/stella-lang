# The foreign manifest

A `foreign` declaration says a name and a type and nothing about what carries it out
([Modules](../06-Modules/01-Modules.md)). **The foreign manifest is where that is
said** — one file per program, naming for each module the thing a runtime reaches its
implementations through.

It is a compiler output like a `.dmo` and a `.dmi`, and it is read by whatever runs
the program: on this interpreter, in time for the module that declares the foreign —
which a run satisfies by reaching everything before the first load and a session by
reaching a module's implementations as that module arrives
([Abstract Machine](../07-Runtime/01-Abstract-Machine.md), D43).

## What a manifest is open to

**The format is open to a backend the compiler does not know**, and that is the
requirement it is shaped by rather than a property it happens to have.

**A convention is what it is not.** Taking the implementations of `Foo` to be a file
beside `Foo`'s source is enough for a backend whose implementations are source files
in the tree, and excludes every backend whose are not: a native backend reaching Rust
cannot put a crate inside a Stella source tree, so the location of its
implementations is a fact about the build rather than about the module. A convention
that fits one target makes adding the second a change to the format.

**So the mapping is written rather than inferred, and what the compiler reads of an
entry is the part this document fixes.** It builds `module` and the marshalling
signatures — the second from the declared types, which only it holds (D44) — and
passes the target's own part through untouched. **A backend added later needs no
change here**, because nothing here knows what a `specifier`, or whatever stands in
its place, means.

## The file

```json
{
  "formatVersion": 1,
  "target": "javascript",
  "modules": [
    { "module": "Js.Console",
      "specifier": "./js/Js.Console.mjs",
      "foreigns": [ { "name": "log", "params": [ "string" ], "result": { "action": "unit" } } ] }
  ]
}
```

| | |
| --- | --- |
| `formatVersion` | this document's version, which is **1**. A reader rejects a version it does not implement |
| `target` | the backend the payloads are written for. A reader rejects a target that is not its own |
| `modules` | one entry per Stella module whose foreigns that target supplies |

**Two fields inside an entry are fixed here, and the rest is the target's.** `module`
is the qualified module name as a `.dmo` writes it, and `foreigns` is how each of
that module's foreigns crosses the boundary. `specifier` above is JavaScript's; a
native target would name whatever it needs, and a reader of another target never sees
it, having rejected the file already.

### How a value crosses

**A signature is derived from the declared type and written down because the runtime
cannot derive it.** A `.dmo` carries no type ([Bytecode](01-Bytecode.md)), so without
this the boundary would have to guess — and for a host value that is a number there
is nothing to guess from, `Int` and `Number` being one host representation and two
Stella values (D37).

```text
value  ::= "int" | "number" | "char" | "string" | "boolean" | "unit" | "opaque"
result ::= value | { "action": value }

params : [ value ]
result : result
```

**`action` carries what the action produces**, `IO τ` losing its `τ` otherwise and the
loop having nothing to make a value out of when the action has run.

**The two grammars are separate so that the restriction is the format** rather than a
sentence beside it. An action stands in a result and nowhere else, and what it
produces is a plain value — `IO (IO τ)` is not writable here because it is not
declarable at all (D44), and an argument of type `IO τ` is excluded the same way.

| | What the host sees | What the boundary does |
| --- | --- | --- |
| `int`, `number`, `char`, `string`, `boolean` | the host's own number, string, or boolean | unwraps on the way in and wraps on the way out, **by the kind and not by the value** |
| `unit` | nothing to read, nothing to return | supplies `Prim.Unit` under the identity the registry assigned |
| `opaque` | whatever it was handed | passes it through. A value of an `intrinsic opaque` type has no host shape to convert to and needs none |
| `{ "action": k }` | returns the action itself | wraps it as the `IO` value a program halts on (D25), and marshals what the action produces by `k` when the loop runs it. **A result of type `IO τ` is this**, and it is why a target entry constructing a native action needs to know nothing of how an `IO` value is built |

#### A host value that is not what its kind says

**Marshalling on the way out is a check as well as a conversion**, because what comes
back is the host's and nothing has constrained it. A kind says what a Stella value of
that type is, and a host value that cannot be one is **a breach of the contract by
the implementation** — the same class as a body that threw where it should have
answered, and reported apart from a value the program then went wrong with.

| The kind | What is not one |
| --- | --- |
| `int` | not a number, not a whole one, or outside the range of an int32 (D37) |
| `number` | not a number |
| `char` | not a string, not one scalar value, or half a surrogate pair (D27) |
| `string` | not a string, or one holding an unpaired surrogate |
| `boolean` | not a boolean |
| `unit` | nothing is rejected: the host value is not read at all, `Prim.Unit` being supplied whatever came back |
| `opaque` | nothing is rejected: there is nothing an opaque value is not |
| `{ "action": k }` | not callable |

**It is a fault and it names the entry**, which is what the implementer needs. Letting
a bad value through instead would put something no Stella type describes into a
register, and the failure would surface somewhere else entirely as a defect that
looks like the interpreter's.

**Nothing is checked on the way in**, the values being the interpreter's own and
already what they claim.

**So an implementation is written against the host's own types and installed as it
stands**, which is the property this exists to make true.

```javascript
export const log = (message) => () => console.log(message);
export const codePointAt = (index, text) => text.codePointAt(index);
```

**Arguments arrive as arguments.** An implementation is uncurried — a saturated call
hands over every argument at once
([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)) — so it is written as a
function of them, not of an array.

**`params` is read for marshalling and is not where an arity lives.** The declaration
states the arity and the `.dmo` carries it; a manifest whose `params` are a different
length is refused rather than believed, both sides having come from the same compiler
and a disagreement therefore being a defect in what produced them.

### What cannot cross

**A type with no kind above cannot be declared `foreign`** (D44). A data value, a
record, a variant, a closure, or a continuation is held in a shape that is the
interpreter's own and is not a published ABI, so there is nothing to marshal it to;
declaring one is refused where the declaration is written, which is where the author
can do something about it.

**A wrapper written in Stella is how such a value crosses**, and the discipline is
the one a backend boundary always asks for: expose the transparent thing, and bridge
the abstract one above it.

```text
foreign draw : Picture -> Unit        -- refused: Picture is a data type
foreign drawAt : Int -> Int -> Unit   -- declared, and a Stella function unfolds Picture into it
```

**No module appears twice, and a reader rejects one that does.** First-wins and
last-wins both make the meaning depend on the order the entries were written in,
which is not a thing a hand-edited or half-updated file can be trusted about; a
duplicate is a manifest that says two things, and the answer is to say so rather than
to pick.

**No foreign appears twice inside an entry either, and a reader rejects one that
does**, for the reason above read one level down: an array makes order meaningful
where order means nothing.

**A compiler writes one entry per module and one per foreign, each in order of its
name.** Where a package declaration and a build override name the same module, the
aggregation resolves them to one entry before anything is written — the override
wins, that being what an override is — so the file a build produces is the same file
for the same inputs.

### The JavaScript target

**A `specifier` is resolved against the manifest's own location.** That is the one
base that makes the file mean the same thing wherever it is read from: the working
directory would make the same manifest name different modules on different
invocations, and the location of whatever does the importing is an implementation
detail of the runtime rather than something a build can know.

| | Resolved as |
| --- | --- |
| a relative specifier, `./js/Js.Console.mjs` | relative to the directory the manifest is in |
| a bare specifier, `@acme/stella-fs/file.mjs` | as the host resolves a bare specifier, starting from the manifest's directory |
| an absolute one | as it stands |

**The export an entry supplies is the foreign's unqualified name**, so `Js.Console.log`
is the export `log` of the module the entry names. **No export name is written
separately**, though a signature is.

#### Refusing

**An implementation returns a host value, and says the one other thing it may say
through the runtime helper.**

```javascript
import { refuse } from "@stella-lang/runtime/foreign";

export const parse = (text) =>
  looksRight(text) ? decode(text) : refuse("not a date");
```

| | |
| --- | --- |
| it produced a value | return the host value |
| it will not produce one | `refuse(reason)` |
| an action | the action returns a host value, or `refuse(reason)` |
| it threw | the contract is broken, and that is a different fault |

**A refusal is a fault the implementation defines, and a throw is the implementation
broken.** Both end the run and both are faults, but they are reported apart and a
reader chasing one should not be shown the other
([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)). **This is not a
Base-ABI-only idea**: Core reads every saturated `foreign` as returning a value or a
fault, and nothing in it distinguishes an implementation the machine carries out from
one a host supplies (D41), so an entry refusing an input it will not serve is
ordinary.

**The helper is how an implementation says that, and it is the only way.** `refuse`
builds a value the runtime recognises by a brand the helper keeps to itself — a
module-private `Symbol`, not a global one — so **nothing an implementation could have
got from elsewhere is mistaken for it**. An opaque host value is any host object at
all, and a marker obtainable without the helper would eventually be one of them.

#### What crosses is synchronous, and a promise is not awaited

**Every value a host implementation hands back is one it has already.** A foreign
call returns a value or refuses, and an action, when the loop runs it, does the same.
**Nothing at this boundary waits**, and there is no form an implementation can use to
ask for waiting.

**This is a limit of the language and not of the boundary.** Stella fixes no meaning
for asynchrony — no type, no effect, no operation says what it would be for a program
to wait — so an implementation that awaited would be producing a value the rest of
the specification has nothing to say about. Admitting it at the boundary first would
settle the language question by accident, in the one place with no standing to settle
it ([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

**A promise is therefore an ordinary host value here.** It is an object, so it
crosses where the kind is `opaque` and is a host-contract fault against any other
kind; what a program can then do with it is hold it, pass it back, and nothing else.
**No thenable is tested for**, which is what makes an opaque value the host gave a
`then` — a handle, a buffer, a connection — cross as itself rather than as something
to wait on.

**So an asynchronous host API is reached by giving it a synchronous face**, which is
the discipline every other unmarshallable thing gets: the blocking call where the
host has one, or a handle the program polls through further entries.

**An implementation that only ever returns values imports nothing**, which is most of
them. The import is the boundary at which an implementation says something other than
a value, and it is versioned with this format and the runtime that reads it.

#### One instance of the helper is a precondition of the build

**A brand a module keeps to itself identifies nothing across two copies of that
module.** If an implementation reaches a different copy of the helper than the
runtime holds — a second install under another path, a URL beside a file, a realm of
its own — the `refuse` it builds carries a brand the runtime does not know.

**So the build owes one instance**, and the specifier is fixed rather than left to
each package: `@stella-lang/runtime/foreign` is where a JavaScript implementation
reaches it, and what makes that one module is the same deduplication a host already
does for any shared dependency. **The runtime supplies the module it will then
recognise** — it is the runtime's own, not a package an implementation may pick a
version of, which is why it is versioned with the runtime and not with the program.

**One instance is a precondition of the build and not something the runtime checks.**
It is worth being exact about how far detection goes, because it goes some of the way
and stopping there would be worse than not claiming it.

| The kind the result carries | What a `refuse` from a second helper does |
| --- | --- |
| a scalar | it is a host object where a number or a string was owed, so it ends the run as a breach naming the entry |
| **`unit`** | **nothing catches it.** Nothing of the host value is read for a `unit` result — `Prim.Unit` is supplied whatever came back — so the marker is discarded and a refusal silently becomes a success |
| **`opaque`** | **nothing catches it** either. An opaque result is any host object at all, so the marker passes as the value |
| `{ "action": k }` | whatever `k` gives, by the rows above |

**So the guarantee is a build's to keep.** A program whose helper is duplicated is
mis-built in a way that shows up loudly for a scalar result and not at all for the
two kinds that read nothing of what came back, and neither the manifest nor the
loader is positioned to tell. **`IO Unit` is the case to have in mind**, a console
entry being the shape a program reaches for first.

**Making it unbreakable would mean the runtime handing the capability to an
implementation rather than the implementation importing it**, which is a different
authoring contract and not the one this document fixes
([Open Questions](../99-Open-Questions/01-Open-Questions.md)).

**Rejecting an unknown target is the same rule a `.dmo` has for an ABI version it
does not hold** ([Encoding](02-Encoding.md)). A manifest read by the wrong runtime is
not a manifest with unfamiliar fields to skip; it is a statement about a machine that
is not this one, and reading past that would be guessing.

### What an entry does not carry

**Not an argument that is dropped.** A `unit` parameter keeps its place and the host
sees `undefined` there: omitting it would make the call shorter than the arity the
declaration states, and the two are the same call.

**Not an arity of its own.** `params` says how each argument crosses, and its length
is the arity as a consequence rather than as a second statement of it; a manifest
whose length disagrees with the declaration is refused (above).

**Nor an arity read off the reached export**, which is not available: on JavaScript
`Function.length` counts neither a rest parameter nor one with a default. **What is
checked of the export itself is the one thing that can be** — that it is callable.

**Not an effect summary.** Whether an entry has an observational effect travels to an
optimizer through the interface file (D41, [Interface](03-Interface.md)), which runs
long before a manifest is read.

## What is not in a manifest at all

**An entry the ABI manifest fixes.** The operations and `Base.IO.pure` and
`Base.IO.bind` are carried out by whatever executes the program, selected by name
([Prim and Base](../06-Modules/02-Prim-and-Base.md)); a foreign manifest covering one
would be a second answer to a question the precedence rule settles, and the rule
selects the interpreter regardless, so the entry would be written and never read.

**This is why `Base` ships no implementations and is not a special package for it.**
The rule attaches to the names the ABI manifest fixes and not to a package: a
declaration of such a name needs nothing supplied, every other foreign does, and no
package but the one that owns the name could declare it anyway.

## Where the mapping comes from

**A package declares where its own implementations are**, per target, so that a
library carrying foreigns is usable without every consumer configuring it.

**A build may supply or override one**, which is what an implementation outside the
source tree needs: where a crate lives is a fact about the build, and a package that
wrote it down would be wrong on the next machine.

**Both are needed, and neither alone is enough.** With only the first, a target whose
implementations cannot live in the tree has nowhere to say so. With only the second,
no library can describe itself and the knowledge spreads to every program that
depends on one.

**What the compiler does with them is aggregate.** It collects the declarations of
every package in the program, for the target the package manager names (D47), and
writes one file. It resolves no path and interprets no payload.

## What the compiler checks

**Coverage and the signatures, and nothing of the target's part.** Every module in the
program that declares a foreign the ABI manifest does not fix must have an entry, and
every such foreign must have a signature its declared type gives. Both questions are
target-independent, which is what lets a compiler that reads no payload ask them.

**It is caught here because here is where the source is.** A build that omitted a
package's mapping should hear about it with the module and the declaration to hand,
rather than as a load error in another process later.

**The loader checks again, and what it can check is narrower.** A `.dmo` may reach an
interpreter from anywhere, so the loader answers for what it is actually given: a
foreign nothing supplies, a module the manifest names that cannot be reached, an
export that is absent or not callable, and a `params` length that disagrees with the
declared arity ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

**What it cannot check is a signature that went stale without changing shape.** A
`.dmo` carries no type, so a manifest written when an argument was `Int` and kept
when it became `Number` agrees with everything the loader can compare — the name is
the same, the arity is the same — and marshals by the old kind. What comes of that is
a value of a type nothing declared.

**So the pair is a build obligation and not a thing the loader recovers from.** A
`.dmo` and the manifest that describes it come from one compilation and belong
together; mixing them is the same mistake as mixing a `.dmo` with another module's
`.dmi`, and nothing downstream is positioned to notice. **Binding an entry to a digest
of the `.dmo` it was written for would close it**, at the cost of a manifest that must
be rewritten whenever a module is recompiled for any reason; whether that trade is
worth making is not settled here
([Open Questions](../99-Open-Questions/01-Open-Questions.md)).
