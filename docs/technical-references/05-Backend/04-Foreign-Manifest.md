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

**So the mapping is written rather than inferred, and the compiler does not read what
it writes.** What the compiler understands is which Stella module an entry is for;
everything after that belongs to the target and passes through untouched. A backend
added later needs no change here, because there is nothing here that knows what a
target's payload means.

## The file

```json
{
  "formatVersion": 1,
  "target": "javascript",
  "modules": [
    { "module": "Js.Console", "specifier": "./js/Js.Console.mjs" },
    { "module": "Js.File",    "specifier": "@acme/stella-fs/file.mjs" }
  ]
}
```

| | |
| --- | --- |
| `formatVersion` | this document's version, which is **1**. A reader rejects a version it does not implement |
| `target` | the backend the payloads are written for. A reader rejects a target that is not its own |
| `modules` | one entry per Stella module whose foreigns that target supplies |

**`module` is the only field this document fixes inside an entry.** It is the
qualified module name as a `.dmo` writes it. Everything beside it is the target's —
`specifier` above is JavaScript's, a native target would name whatever it needs — and
a reader of another target never sees it, having rejected the file already.

**No module appears twice, and a reader rejects one that does.** First-wins and
last-wins both make the meaning depend on the order the entries were written in,
which is not a thing a hand-edited or half-updated file can be trusted about; a
duplicate is a manifest that says two things, and the answer is to say so rather than
to pick.

**A compiler writes one entry per module and writes them in order of the module
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
is the export `log` of the module the entry names. Nothing is written per foreign.

**Rejecting an unknown target is the same rule a `.dmo` has for an ABI version it
does not hold** ([Encoding](02-Encoding.md)). A manifest read by the wrong runtime is
not a manifest with unfamiliar fields to skip; it is a statement about a machine that
is not this one, and reading past that would be guessing.

### What an entry does not carry

**Not the arity, and the consequence is worth stating rather than leaving to be
found.** The declaration states it and the `.dmo` carries it
([Bytecode](01-Bytecode.md)). **On this path the declared arity is adopted, and there
is no second number to disagree with it.** The loader's refusal for a supplied arity
that contradicts a declaration therefore cannot fire here — not because the check was
removed, but because nothing on this path supplies one
([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).

**A manifest could have carried one, and should not.** It would be a third place for
a number that the declaration and the container already hold, able to contradict both
while the implementation is correct — and what it would be checked against is not
what a host actually takes. **An arity read off the reached export is not available
either**: on JavaScript, `Function.length` counts neither a rest parameter nor one
with a default, and an adapter is usually written as one of those. There is nothing
to compare, so nothing is compared.

**What is checked instead is the one thing that can be**: that what was reached is
callable at all.

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
every package in the program, for the target being built, and writes one file. It
resolves no path and interprets no payload.

## What the compiler checks

**Coverage, by module name, and nothing else.** Every module in the program that
declares a foreign the ABI manifest does not fix must have an entry. That question is
target-independent, which is what lets a compiler that understands no payload ask it.

**It is caught here because here is where the source is.** A build that omitted a
package's mapping should hear about it with the module and the declaration to hand,
rather than as a load error in another process later.

**The loader checks again, and the second check is not redundant.** A `.dmo` may
reach an interpreter from anywhere, and a manifest may be stale; the loader answers
for what it is actually given ([Abstract Machine](../07-Runtime/01-Abstract-Machine.md)).
What the two catch differs — one an incomplete build, the other an incomplete
handover — and either alone leaves the other unanswered.
