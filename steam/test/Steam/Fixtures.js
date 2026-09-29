import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

// The fixture directory, reached from this file's place in the build output.
export const fixturesRoot = fileURLToPath(new URL("../../fixtures/bytecode/", import.meta.url));

export const caseNames = (root) => () =>
  existsSync(root) ? readdirSync(root).filter((n) => statSync(join(root, n)).isDirectory()).sort() : [];

export const exists = (path) => () => existsSync(path);

export const readText = (path) => () => readFileSync(path, "utf8");

export const readBytes = (path) => () => Array.from(readFileSync(path));

// The effects a fixture's host saw, read from `host.mjs` under the URL a manifest
// entry's `./host.mjs` resolves to against the fixture's directory: the module
// instance the program reached, and so the log it wrote.
export const eventsImpl = (base) => (onError, onSuccess) => {
  const url = new URL("./host.mjs", pathToFileURL(base + "/"));
  if (!existsSync(fileURLToPath(url))) onSuccess([]);
  else import(url.href).then((host) => onSuccess(host.events()), onError);
  return (cancelError, onCancelerError, onCancelerSuccess) => onCancelerSuccess();
};

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
