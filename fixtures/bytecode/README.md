# Bytecode fixtures

Lowered modules that every consumer of a `.dmo` runs, and what running them must
give. Steam and the JavaScript backend both read these bytes and check the same
manifests; neither compiles Stella, which is the compiler's work.

## Layout

Each directory is one fixture:

```text
<fixture>/
  <Module>.dmo            one per module, e.g. Base.Int.dmo
  manifest.json
  foreign-manifest.json   where a module declares a foreign a host supplies
  host.mjs                the implementation module that manifest points at
```

`manifest.json` says:

| Field | Meaning |
| --- | --- |
| `description` | what the fixture exercises |
| `modules` | the modules to load, in the order to load them; the last is the entry |
| `outcome` | `{"loads": true}`; `{"refusedAtLoad": {"mentions": "name"}}` where loading must be refused, not by a fault, with a report naming `name`; `{"faultsAtLoad": {"global": "Main.x"}}` where loading must end in a fault as `Main.x` is initialized; or one of the three below, where the modules load and the entry point is run |
| `observe` | globals of the entry module and the value each must hold |

A value is `{"int": 6}`, `{"number": "-0"}` (the text JavaScript's `Number` reads
back to the value, so `-0`, `NaN`, and `Infinity` are writable), `{"char": 98}`,
`{"string": "b"}`, `{"boolean": true}`, `{"data": "Data.List.Cons", "fields": […]}`,
`{"record": [{"key": …, "value": …}]}`, `{"variant": …, "payload": …}`, or
`{"function": true}`. A key is `{"field": "x"}`, `{"tag": "Ok"}`,
`{"position": 0}`, or `{"effect": "Mod.Eff"}`.

## Running an entry point

A fixture with an entry point names it, as `Mod.name`, in its outcome:

| Outcome | Meaning |
| --- | --- |
| `{"runs": {"entry": …, "result": …, "effects": […]}}` | executing the action the entry global holds produces `result`, with the host seeing `effects` in order |
| `{"faultsAtRun": {"entry": …, "kind": …, …, "effects": […]}}` | executing it ends in a fault of `kind`, after the host saw `effects` |
| `{"startFails": {"entry": …, "reason": …}}` | it does not start: `noSuchGlobal` where the entry module declares no such global, `notAnAction` where the global holds no action |

A fault is compared by its kind and what every runtime observes of a fault of that
kind:

| `kind` | Also given |
| --- | --- |
| `refused` | `foreign`, the foreign that refused, and `reason` |
| `threw` | `foreign`, the foreign whose host function threw, and `message` |
| `breached` | `foreign`, the foreign whose result was not of its kind |
| `actionRefused` | `reason` |
| `actionThrew` | `message` |
| `actionBreached` | `foreign`, the foreign that returned the action |

What a runtime says of a breach is its own wording, and is not compared.

`host.mjs` records every call it takes, and every action it returns as the action
is performed, and exports the record as `events`. A runner imports it under the URL
`./host.mjs` resolves to against the fixture's directory, which is the module the
program reached, and compares what it recorded with `effects`. A fixture without
`host.mjs` has no effects.
Some `host.mjs` import `@stella-lang/runtime`, resolved upwards from the fixture's
directory, and rely on the runtime running the program being that one copy of the
package: a refusal is recognised by its brand, and a host throwing the runtime's own
`Fault` or `Bug` must still be reported as a throw.

`foreign-manifest.json` has the format of the
[Foreign Manifest](../../docs/technical-references/05-Backend/04-Foreign-Manifest.md),
and a specifier in it is resolved against the fixture's directory.

## Where they come from

A fixture is built from Stella source by the compiler: the modules under
`fixtures/source/<fixture>/`, the shared ones under `fixtures/source/common-lib/`
it names, and the modules of the `stella-packages/base`, `lists`, and `maybe`
packages those import. It holds the `.dmo` of each module it reaches and no other,
`Base.Int.dmo` being the module the compiler carries. Which source directories make
each fixture, and what each must give, are in
`compiler/test/Stella/Compiler/Fixtures.purs` and the modules beside it under
`Fixtures/`; `Fixtures/Foreigns.purs` also holds each `host.mjs` and the signatures
each foreign manifest is written from. A foreign manifest is checked against the
modules it describes as it is written, except in a fixture made to disagree with
them, whose description says so.

A fixture setting two versions of a module side by side (`stale-arity-*`,
`stale-foreign-*`, `unexported-global`, `undeclared-ctor`) is built twice:
once with the version the entry module is compiled against, and once with the
version that loads, alone. Of a module both builds give, it keeps the loaded one.

A module no source compiles to, such as a region entry naming one cell twice, is
made by building the source and then changing the lowered module. Its manifest's
description says what was changed. These are the `handler-*` and `region-*`
fixtures, `foreign-unexported`, `io-pure-unexported`, `io-bind-unexported`,
`operation-by-foreign`, and `operation-by-foreign-unexported`.

### Fixtures compiled from Core

Some values have no source the compiler elaborates to them. Each is compiled from
hand-written Core in the modules under `Fixtures/` instead, in a fixture of its own
apart from the values of the same kind that are built from source:

| Fixture | Values | Why no source gives them |
| --- | --- | --- |
| `programs-core` | `joined`, `looped`, `loopedDeep` | a join point two leaves share, and one jumping to itself, 100 000 times in `loopedDeep`: the elaborator makes no join point |
| `programs-core` | `recordShape` | record `merge`, which no form of the surface writes: a record literal spreads one record, and a record pattern's rest is a `restrict` of the record matched |
| `programs-core` | `negZero`, `posZero`, `nanCase` | a `Number` dispatch by literal identity: the surface has no `Number` literal pattern, and leaves such a test to a guard |
| `effects-core` | `contOverApplied`, `interleaved` | a clause answering with a function that applies its continuation, so that the continuation is applied to two arguments, or held captured while a second resumption runs: the surface applies `resume` under a λ of its clause only in a `reifiable` clause, and so applies no plain continuation there |
| `regions-core` | `choiceState`, `stateChoice`, `recursed`, `nestedCopy`, `closureBefore`, `stashed` | a computation reading and writing the cells of a region around it: the surface reaches a cell only from the clauses of the handler declaring it |
| `regions-core` | `nest`, which `recursed` applies | a polymorphic recursion needing a constraint written in its signature |
| `io-entry-arity-pure`, `io-entry-arity-bind` | the module `Base.IO` | `pure` or `bind` declared at an arity the ABI does not give it, which the compiler refuses in source |

## Regenerating them

The compiler's test suite checks that every fixture here is exactly what building
its source gives now, and fails naming each one that is not. It also checks that
the fixtures built from source still lower to the instructions they are to
exercise, which regenerating them would not keep. The `.dmo` format is not
frozen, so after a change to it, or to a fixture's source, regenerate them all
from the Nix dev shell:

```sh
STELLA_UPDATE_FIXTURES=1 spago test -p compiler
```

and commit the result with the change that caused it.
