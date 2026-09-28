import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

// The fixture directory, reached from this file's place in the build output.
export const fixturesRoot = fileURLToPath(new URL("../../fixtures/bytecode/", import.meta.url));

export const caseNames = (root) => () =>
  existsSync(root) ? readdirSync(root).filter((n) => statSync(join(root, n)).isDirectory()).sort() : [];

export const readText = (path) => () => readFileSync(path, "utf8");

export const readBytes = (path) => () => Array.from(readFileSync(path));

export const parseManifestImpl = (k) => (text) => {
  const m = JSON.parse(text);
  const key = (j) => {
    if ("field" in j) return k.field(j.field);
    if ("tag" in j) return k.tag(j.tag);
    if ("position" in j) return k.position(j.position);
    return k.effect(j.effect);
  };
  const value = (j) => {
    if ("int" in j) return k.int(j.int);
    if ("number" in j) return k.number(Number(j.number));
    if ("char" in j) return k.char(j.char);
    if ("string" in j) return k.string(j.string);
    if ("boolean" in j) return k.boolean(j.boolean);
    if ("data" in j) return k.data(j.data)(j.fields.map(value));
    if ("record" in j) return k.record(j.record.map((f) => ({ key: key(f.key), value: value(f.value) })));
    if ("variant" in j) return k.variant(key(j.variant))(value(j.payload));
    return k.fn;
  };
  return {
    description: m.description,
    modules: m.modules,
    loads: "loads" in m.outcome,
    mentions: "refusedAtLoad" in m.outcome ? m.outcome.refusedAtLoad.mentions : "",
    observe: m.observe.map((o) => ({ global: o.global, value: value(o.value) })),
  };
};
