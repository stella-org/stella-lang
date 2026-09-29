import { existsSync, mkdtempSync, readdirSync, readFileSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { createRequire } from "node:module";
import { isAbsolute, join } from "node:path";
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

// A manifest specifier as generated code can import it, resolved against the
// manifest's directory as a runtime reaching the entry resolves it.
export const resolveSpecifier = (base) => (specifier) => {
  if (specifier.startsWith("./") || specifier.startsWith("../")) {
    return new URL(specifier, pathToFileURL(base + "/")).href;
  }
  if (isAbsolute(specifier)) return pathToFileURL(specifier).href;
  if (URL.canParse(specifier)) return specifier;
  return pathToFileURL(createRequire(pathToFileURL(base + "/")).resolve(specifier)).href;
};

// The effects a fixture's host saw, read from `host.mjs` under the URL a manifest
// entry's `./host.mjs` resolves to against the fixture's directory: the module
// instance the program reached, and so the log it wrote.
const eventsOf = async (base) => {
  const url = new URL("./host.mjs", pathToFileURL(base + "/"));
  if (!existsSync(fileURLToPath(url))) return [];
  const host = await import(url.href);
  return host.events();
};

// Write the generated modules into a fresh directory, import the one holding the
// entry point, and execute the action it exports as `"entry point"`: how the run
// ended, what it produced or what ended it, and the effects the host saw.
export const runEntryImpl = (files) => (entryFile) => (entry) => (base) => (onError, onSuccess) => {
  const ran = async () => {
    const rt = await import(runtimeSpecifier);
    const dir = mkdtempSync(join(tmpdir(), "stella-js-"));
    for (const file of files) writeFileSync(join(dir, file.name), file.source);
    const out = { ended: "", holder: {}, kind: "", foreign: "", detail: "", message: "", effects: [] };
    let namespace;
    try {
      namespace = await import(pathToFileURL(join(dir, entryFile)).href);
    } catch (e) {
      out.ended = "notLoaded";
      out.message = String(e && e.message);
      return out;
    }
    try {
      out.holder.value = rt.runMain(entry, namespace["entry point"]);
      out.ended = "produced";
    } catch (e) {
      out.message = String(e && e.message);
      if (e instanceof rt.Fault) {
        out.ended = "faulted";
        out.kind = e.kind;
        out.foreign = e.foreign ?? "";
        out.detail = e.detail ?? "";
      } else if (e instanceof rt.StartFailure) out.ended = "failedToStart";
      else out.ended = "threw";
    }
    out.effects = await eventsOf(base);
    return out;
  };
  ran().then(onSuccess, onError);
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
  const o = m.outcome;
  const run =
    "runs" in o
      ? k.just({ entry: o.runs.entry, end: k.produces(value(o.runs.result))(o.runs.effects) })
      : "faultsAtRun" in o
        ? k.just({
            entry: o.faultsAtRun.entry,
            end: k.faultsWith({
              kind: o.faultsAtRun.kind,
              foreign: o.faultsAtRun.foreign ?? "",
              reason: o.faultsAtRun.reason ?? "",
              message: o.faultsAtRun.message ?? "",
            })(o.faultsAtRun.effects),
          })
        : "startFails" in o
          ? k.just({ entry: o.startFails.entry, end: k.failsToStart(o.startFails.reason) })
          : k.nothing;
  return {
    description: m.description,
    modules: m.modules,
    loads: "loads" in o || "runs" in o || "faultsAtRun" in o || "startFails" in o,
    mentions: "refusedAtLoad" in o ? o.refusedAtLoad.mentions : "",
    faults: "faultsAtLoad" in o ? o.faultsAtLoad.global : "",
    observe: m.observe.map((ob) => ({ global: ob.global, value: value(ob.value) })),
    run,
  };
};

export const exists = (path) => () => existsSync(path);

export const specifierIn = (path) => (module) => {
  const entry = JSON.parse(readFileSync(path, "utf8")).modules.find((m) => m.module === module);
  return entry && typeof entry.specifier === "string" ? entry.specifier : "";
};
