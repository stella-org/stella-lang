import { createRequire } from "node:module";
import { isAbsolute } from "node:path";
import { pathToFileURL } from "node:url";

// Reaching a module is importing it, and the base a specifier is resolved against is
// the directory the manifest was read from — not the working directory, which would
// make one manifest name different modules on different invocations, and not this
// file's own location, which is an implementation detail of the runtime.
//
// A specifier that does not resolve is answered as the import failing, as one that
// resolves to nothing importable is.
export const importModuleImpl = (specifier) => (base) => () => {
  try {
    return import(resolveFrom(specifier, base)).then(exportsOf);
  } catch (err) {
    return Promise.reject(err);
  }
};

const resolveFrom = (specifier, base) => {
  if (specifier.startsWith("./") || specifier.startsWith("../")) {
    return new URL(specifier, pathToFileURL(base + "/")).href;
  }
  // A filesystem path is asked about before a URL: a Windows path such as `C:\x.mjs`
  // would otherwise read as a URL of the scheme `c:`.
  if (isAbsolute(specifier)) {
    return pathToFileURL(specifier).href;
  }
  // An absolute URL — `file:`, `node:`, and the rest — is imported as it stands.
  if (URL.canParse(specifier)) {
    return specifier;
  }
  // A bare specifier is resolved as the host resolves one, searching upwards from the
  // manifest's directory. `import` alone would search from this file instead.
  return pathToFileURL(createRequire(pathToFileURL(base + "/")).resolve(specifier)).href;
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
