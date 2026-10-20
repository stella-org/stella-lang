// Builds the `Base` package, `stella-packages/base`, from its sources, and
// writes beside the files the build writes a dependency map listing every
// module of the package, for a build of another package to be given with
// `stellac build --dependencies`.
//
// `Base.Int` is a seed module, loaded as the compiler bootstraps, which no
// build of a package compiles. So `stella-devtools build-seeds` writes it,
// with the other seed modules, under `seeds` in the output; then `stellac
// build`, an ordinary build, builds the package's other files against a map
// listing that `Base.Int`. The map lists it as any map may list a seed
// module, so the build is refused where its interface is not the one of the
// seed module the compiler holds: a change to its source is taken into the
// compiler first. Both run from the workspace's build output, which needs the
// workspace built.
//
// Run from the repository root: `npm run build:base [-- --output <dir>]`. The
// output is `stella-packages/base/output` unless given, relative to the
// directory the script is run from; the map is `dependencies.json` in it.

import { spawnSync } from "node:child_process";
import { mkdirSync, readdirSync, writeFileSync } from "node:fs";
import { dirname, join, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const base = join(root, "stella-packages", "base");
const sources = join(base, "src");

const args = process.argv.slice(2);
const at = args.indexOf("--output");
const output = at >= 0 && args[at + 1] ? resolve(args[at + 1]) : join(base, "output");

// the seed modules of the package
const seeds = ["Base.Int"];

const run = (script, argv) => {
  const done = spawnSync("node", [join(root, script), ...argv], { cwd: root, stdio: "inherit" });
  if (done.status !== 0) {
    process.exit(done.status ?? 1);
  }
};

const entry = (module, dir) => ({
  module,
  interface: `${dir}/${module}.dmi`,
  object: `${dir}/${module}.dmo`,
});

const writeMap = (path, entries) =>
  writeFileSync(path, JSON.stringify({ formatVersion: 0, modules: entries }, null, 2) + "\n");

// each module of the package, named by the path of its source
const modules = readdirSync(sources, { recursive: true })
  .filter((path) => path.endsWith(".stel"))
  .map((path) => ({ path, module: path.slice(0, -".stel".length).split(sep).join(".") }))
  .sort((a, b) => (a.module < b.module ? -1 : a.module > b.module ? 1 : 0));
const built = modules.filter((m) => !seeds.includes(m.module));

mkdirSync(output, { recursive: true });
run("devtools/index.js", ["build-seeds", "--output", join(output, "seeds")]);

const seedsMap = join(output, "seeds.json");
writeMap(seedsMap, seeds.map((m) => entry(m, "seeds")));
run("stellac/index.dev.js", [
  "build",
  "--workdir", base,
  "--output", output,
  "--dependencies", seedsMap,
  ...built.flatMap((m) => ["--src", ["src", ...m.path.split(sep)].join("/")]),
]);

const path = join(output, "dependencies.json");
writeMap(path, modules.map((m) => entry(m.module, seeds.includes(m.module) ? "seeds" : "_build")));
console.log(`Wrote the map of ${modules.length} module(s) → ${path}`);
