// Builds the `Base` package, `stella-packages/base`, from its sources, and
// writes beside the files the build writes a dependency map listing every
// module of the package, for a build of another package to be given with
// `stellac build --dependencies`.
//
// The build is `stellac build`'s development entry point, which needs the
// workspace built. `Base.Int` is a module the compiler carries, so the build
// compiles it anew (`--toolchain-rebuild`); a map listing it is accepted where
// its interface is the one the compiler carries. The build is given no map.
//
// Run from the repository root: `npm run build:base [-- --output <dir>]`. The
// output is `stella-packages/base/output` unless given, relative to the
// directory the script is run from; the map is `dependencies.json` in it.

import { spawnSync } from "node:child_process";
import { readdirSync, writeFileSync } from "node:fs";
import { dirname, join, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const base = join(root, "stella-packages", "base");
const sources = join(base, "src");

const args = process.argv.slice(2);
const at = args.indexOf("--output");
const output = at >= 0 && args[at + 1] ? resolve(args[at + 1]) : join(base, "output");

const built = spawnSync(
  "node",
  [join(root, "stellac/index.dev.js"), "build", "--workdir", base, "--output", output, "--toolchain-rebuild", "Base.Int"],
  { stdio: "inherit" },
);
if (built.status !== 0) {
  process.exit(built.status ?? 1);
}

// each module of the package, named by the path of its source
const modules = readdirSync(sources, { recursive: true })
  .filter((path) => path.endsWith(".stel"))
  .map((path) => path.slice(0, -".stel".length).split(sep).join("."))
  .sort();

const map = {
  formatVersion: 0,
  modules: modules.map((module) => ({
    module,
    interface: `_build/${module}.dmi`,
    object: `_build/${module}.dmo`,
  })),
};
const path = join(output, "dependencies.json");
writeFileSync(path, JSON.stringify(map, null, 2) + "\n");
console.log(`Wrote the map of ${modules.length} module(s) → ${path}`);
