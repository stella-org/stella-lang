import { readFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

// The repository's root, reached from this file's place in the build output.
const root = fileURLToPath(new URL("../../", import.meta.url));

export const readRepositoryFile = (path) => () => readFileSync(join(root, path), "utf8");
