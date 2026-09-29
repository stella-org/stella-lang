import { existsSync, mkdtempSync, readdirSync, readFileSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

// The runtime generated code imports, reached from this file's own place in the
// build output rather than resolved as a package, so a test needs no install step.
export const runtimeSpecifier = new URL("../../js-runtime/src/backend.js", import.meta.url).href;

// Write the generated modules into a fresh directory and import the entry one.
export const importGeneratedImpl = (files) => (entry) => (onError, onSuccess) => {
  try {
    const dir = mkdtempSync(join(tmpdir(), "stella-js-"));
    for (const file of files) writeFileSync(join(dir, file.name), file.source);
    import(pathToFileURL(join(dir, entry)).href).then(onSuccess, onError);
  } catch (e) {
    onError(e);
  }
  return (cancelError, onCancelerError, onCancelerSuccess) => onCancelerSuccess();
};

// How importing the entry module ended: whether it loaded, and where it did not,
// the message of what it threw, whether that was a Stella fault, and the global
// whose initialization a fault ended.
export const importFailureImpl = (files) => (entry) => (onError, onSuccess) => {
  try {
    const dir = mkdtempSync(join(tmpdir(), "stella-js-"));
    for (const file of files) writeFileSync(join(dir, file.name), file.source);
    import(pathToFileURL(join(dir, entry)).href).then(
      () => onSuccess({ loaded: true, message: "", fault: false, global: "" }),
      (e) =>
        onSuccess({
          loaded: false,
          message: String(e && e.message),
          fault: !!e && e.name === "StellaFault",
          global: (e && e.global) || "",
        }),
    );
  } catch (e) {
    onError(e);
  }
  return (cancelError, onCancelerError, onCancelerSuccess) => onCancelerSuccess();
};

// What an export of a generated module holds, read through the constructors the
// caller supplies. Numbers of every kind read as one, a JavaScript number being
// what an Int, a Number, and a Char are all held as.
export const shapeOfImpl = (k) => (namespace) => (name) => {
  const go = (v) => {
    if (typeof v === "number") return k.number(v);
    if (typeof v === "string") return k.string(v);
    if (typeof v === "boolean") return k.boolean(v);
    if (v === null || v === undefined) return k.other("nothing");
    const kind = v.constructor && v.constructor.name;
    if (kind === "Data") return k.data(v.c.name)(v.f.map(go));
    if (kind === "Variant") return k.variant(v.k)(go(v.v));
    if (kind === "Closure" || kind === "Pap" || kind === "Continuation") return k.fn;
    return k.record(
      Object.keys(v)
        .sort()
        .map((key) => ({ key, value: go(v[key]) })),
    );
  };
  if (!Object.prototype.hasOwnProperty.call(namespace, name)) return k.other("no such export");
  return go(namespace[name]);
};

// Each structural operation of the runtime handed what its precondition excludes,
// and whether it refused as a bug rather than answering with a value.
export const runtimeRefusals = await (async () => {
  const rt = await import(runtimeSpecifier);
  const refuses = (thunk) => {
    try {
      thunk();
      return false;
    } catch (e) {
      return e instanceof rt.Bug;
    }
  };
  const c = rt.ctor("T.C", 1);
  const d = new rt.Data(c, [1]);
  const rec = rt.extend(rt.emptyRecord, "s:x", 1);
  const other = rt.extend(rt.emptyRecord, "s:x", 2);
  return [
    { name: "a field past the constructor's arity", refused: refuses(() => rt.field(d, c, 1)) },
    { name: "a field of another constructor", refused: refuses(() => rt.field(d, rt.ctor("T.D", 1), 0)) },
    { name: "extending at a key held", refused: refuses(() => rt.extend(rec, "s:x", 2)) },
    { name: "selecting a key lacking", refused: refuses(() => rt.select(rec, "s:y")) },
    { name: "restricting a key lacking", refused: refuses(() => rt.restrict(rec, "s:y")) },
    { name: "updating a key lacking", refused: refuses(() => rt.update(rec, "s:y", 2)) },
    { name: "merging records sharing a key", refused: refuses(() => rt.merge(rec, other)) },
    { name: "a payload at another key", refused: refuses(() => rt.payload(new rt.Variant("t:A", 1), "t:B")) },
  ];
})();

// The fixture directory, reached from this file's place in the build output.
export const fixturesRoot = fileURLToPath(new URL("../../fixtures/bytecode/", import.meta.url));

export const caseNames = (root) => () =>
  existsSync(root) ? readdirSync(root).filter((n) => statSync(join(root, n)).isDirectory()).sort() : [];

export const readText = (path) => () => readFileSync(path, "utf8");

export const readBytes = (path) => () => Array.from(readFileSync(path));

// A manifest, read through the constructors the caller supplies.
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
    faults: "faultsAtLoad" in m.outcome ? m.outcome.faultsAtLoad.global : "",
    observe: m.observe.map((o) => ({ global: o.global, value: value(o.value) })),
    runs: "runs" in m.outcome || "faultsAtRun" in m.outcome || "startFails" in m.outcome,
  };
};
