// Builds the `Base` package, `stella-packages/base`, from its sources, and
// writes `dependencies.json` beside the build's output: an entry of
// `dependencies` for every module of the package, for a `stella.json` to list.
//
// `Base.Int` is a seed module, which no build of a package compiles, so
// `stella-devtools build-seeds` writes it, with the other seed modules, under
// `seeds`. The script then runs `stellac graph` over the package's other
// modules, orders them so each comes after those it imports, and compiles
// them with `stellac compile`, `Base.Int` in `dependencies`. That build is an
// ordinary one: it is refused where the rebuilt `Base.Int` has another
// interface than the seed module the compiler holds, so a change to its
// source goes into the compiler first. The commands run from the workspace's
// build output, which needs the workspace built.
//
// Paths in `dependencies.json` are absolute, so any `stella.json` can list
// the entries as they stand. The file belongs to the machine it was made on
// and is neither shipped nor kept in the repository.
//
// Run from the repository root: `npm run build:base [-- --output <dir>]`. The
// output is `stella-packages/base/output` unless given, relative to the
// directory the script runs in.

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

// the command given run from the repository's root, what it printed returned
const run = (script, argv) => {
  const done = spawnSync("node", [join(root, script), ...argv], { cwd: root, stdio: ["ignore", "pipe", "inherit"], encoding: "utf8" });
  if (done.status !== 0) {
    process.stdout.write(done.stdout ?? "");
    process.exit(done.status ?? 1);
  }
  return done.stdout;
};

const entry = (module, dir) => ({
  module,
  interface: join(output, dir, `${module}.dmi`),
  object: join(output, dir, `${module}.dmo`),
});

const stellaJson = (modules, dependencies) => ({
  formatVersion: 0,
  options: { output, emitCore: false, traceOptimizer: [], steamCmd: "steam", logLevel: "info", monochrome: false },
  modules,
  dependencies,
});

const write = (name, json) => {
  const path = join(output, name);
  writeFileSync(path, JSON.stringify(json, null, 2) + "\n");
  return path;
};

// the modules given, each after those of them it imports as the graph reports
// them, ties kept in the order given
const ordered = (modules, graph) => {
  const names = new Set(modules.map((m) => m.module));
  const imports = new Map(graph.modules.map((m) => [m.module, m.imports.map((i) => i.module).filter((i) => names.has(i))]));
  const done = [];
  const placed = new Set();
  while (done.length < modules.length) {
    const ready = modules.find((m) => !placed.has(m.module) && imports.get(m.module).every((i) => placed.has(i)));
    if (!ready) {
      throw new Error("modules of the package import one another");
    }
    done.push(ready);
    placed.add(ready.module);
  }
  return done;
};

// each module of the package, named by the path of its source
const modules = readdirSync(sources, { recursive: true })
  .filter((path) => path.endsWith(".stel"))
  .map((path) => ({ module: path.slice(0, -".stel".length).split(sep).join("."), path: join(sources, path) }))
  .sort((a, b) => (a.module < b.module ? -1 : a.module > b.module ? 1 : 0));
const built = modules.filter((m) => !seeds.includes(m.module));
const dependencies = seeds.map((m) => entry(m, "seeds"));

mkdirSync(output, { recursive: true });
run("devtools/index.js", ["build-seeds", "--output", join(output, "seeds")]);

const printed = run("stellac/index.dev.js", ["graph", write("graph.json", stellaJson(built, dependencies))]);
const graph = JSON.parse(printed.slice(printed.indexOf("{")));
process.stdout.write(run("stellac/index.dev.js", ["compile", write("stella.json", stellaJson(ordered(built, graph), dependencies))]));

const path = write("dependencies.json", modules.map((m) => entry(m.module, seeds.includes(m.module) ? "seeds" : ".")));
console.log(`Wrote the entries of ${modules.length} module(s) → ${path}`);
