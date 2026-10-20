import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

// The fixture directory, reached from this file's place in the build output.
export const fixturesRoot = fileURLToPath(new URL("../../fixtures/bytecode/", import.meta.url));

export const updating = () => process.env.STELLA_UPDATE_FIXTURES === "1";

export const caseNames = (root) => () =>
  existsSync(root) ? readdirSync(root).filter((n) => statSync(join(root, n)).isDirectory()).sort() : [];

export const fileNames = (dir) => () => (existsSync(dir) ? readdirSync(dir).sort() : []);

// Whether a file is there. `readText` and `readBytes` throw where it is not; the
// freshness check asks this first so that it can report each missing file by name.
export const exists = (path) => () => existsSync(path);

export const readText = (path) => () => readFileSync(path, "utf8");

export const readBytes = (path) => () => Array.from(readFileSync(path));

export const writeText = (path) => (text) => () => {
  mkdirSync(join(path, ".."), { recursive: true });
  writeFileSync(path, text);
};

export const writeBytes = (path) => (bytes) => () => {
  mkdirSync(join(path, ".."), { recursive: true });
  writeFileSync(path, Uint8Array.from(bytes));
};

export const removeTree = (path) => () => rmSync(path, { recursive: true, force: true });
