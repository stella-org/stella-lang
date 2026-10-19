import { readFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

// The shared sources, and the repository's root, reached from this file's
// place in the build output.
const sourcesRoot = fileURLToPath(new URL("../../fixtures/source/", import.meta.url));
const root = fileURLToPath(new URL("../../", import.meta.url));

export const readSource = (path) => () => readFileSync(join(sourcesRoot, path), "utf8");

export const readRepositoryFile = (path) => () => readFileSync(join(root, path), "utf8");
