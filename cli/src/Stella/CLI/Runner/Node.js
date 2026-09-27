import { pathToFileURL } from "node:url";

// Reaching a module is importing it, and the base a relative specifier is resolved
// against is the directory the manifest was read from — not the working directory,
// which would make one manifest name different modules on different invocations, and
// not this file's own location, which is an implementation detail of the runtime.
//
// A bare specifier is left to the host to resolve, started from that same directory.
export const importModuleImpl = (specifier) => (base) => () =>
  import(resolveFrom(specifier, base)).then(exportsOf);

const resolveFrom = (specifier, base) => {
  if (specifier.startsWith("./") || specifier.startsWith("../")) {
    return new URL(specifier, pathToFileURL(base + "/")).href;
  }
  return specifier;
};

// A plain object of the module's own exports, which is what crosses back. `default`
// is left out: an entry supplies the export whose name is the foreign's, and nothing
// is that.
const exportsOf = (module) => {
  const out = {};
  for (const name of Object.keys(module)) {
    if (name !== "default") out[name] = module[name];
  }
  return out;
};
