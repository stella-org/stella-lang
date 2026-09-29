# Bytecode fixtures

Lowered modules that every consumer of a `.dmo` runs, and what running them must
give. Steam and the JavaScript backend both read these bytes and check the same
manifests; neither lowers Core, which is the compiler's work.

**This form is provisional.** Once a surface parser exists, the fixtures kept in git
become Stella source compiled at test time, and only a few fixed `.dmo` files stay,
to check the decoder and backward compatibility.

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
`{"string": "b"}`, `{"boolean": true}`, `{"data": "Main.Cons", "fields": […]}`,
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

The Core each fixture is compiled from, and its expected values, are in
`compiler/test/Stella/Compiler/Fixtures/Programs.purs`,
`compiler/test/Stella/Compiler/Fixtures/Effects.purs`, and
`compiler/test/Stella/Compiler/Fixtures/Foreigns.purs`, which also holds each
`host.mjs` and the signatures each foreign manifest is written from; the fixtures
themselves are listed in `compiler/test/Stella/Compiler/Fixtures.purs`. A foreign
manifest is checked against the modules it describes as it is written, except in a
fixture made to disagree with them, whose description says so.

A module no Core compiles to, such as a handler entry naming one cell twice, is made
by compiling Core and then changing the lowered module. Its manifest's description
says what was changed.

The compiler's test suite checks that every fixture here is exactly what compiling
its source gives now, and fails naming each one that is not. The `.dmo` format is
not frozen, so after a change to it, or to a fixture's source, regenerate them all
from the Nix dev shell:

```sh
STELLA_UPDATE_FIXTURES=1 spago test -p compiler
```

and commit the result with the change that caused it.
