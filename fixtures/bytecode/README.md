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
  <Module>.dmo      one per module, e.g. Base.Int.dmo
  manifest.json
```

`manifest.json` says:

| Field | Meaning |
| --- | --- |
| `description` | what the fixture exercises |
| `modules` | the modules to load, in the order to load them; the last is the entry |
| `outcome` | `{"loads": true}`, or `{"refusedAtLoad": {"mentions": "name"}}` where loading must be refused with a report naming `name` |
| `observe` | globals of the entry module and the value each must hold |

A value is `{"int": 6}`, `{"number": "-0"}` (the text JavaScript's `Number` reads
back to the value, so `-0`, `NaN`, and `Infinity` are writable), `{"char": 98}`,
`{"string": "b"}`, `{"boolean": true}`, `{"data": "Main.Cons", "fields": […]}`,
`{"record": [{"key": …, "value": …}]}`, `{"variant": …, "payload": …}`, or
`{"function": true}`. A key is `{"field": "x"}`, `{"tag": "Ok"}`,
`{"position": 0}`, or `{"effect": "Mod.Eff"}`.

## Where they come from

The Core each fixture is compiled from, and its expected values, are in
`compiler/test/Stella/Compiler/Fixtures/Programs.purs`; the fixtures themselves are
listed in `compiler/test/Stella/Compiler/Fixtures.purs`.

The compiler's test suite checks that every fixture here is exactly what compiling
its source gives now, and fails naming each one that is not. The `.dmo` format is
not frozen, so after a change to it, or to a fixture's source, regenerate them all
from the Nix dev shell:

```sh
STELLA_UPDATE_FIXTURES=1 spago test -p compiler
```

and commit the result with the change that caused it.
