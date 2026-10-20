import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { join, relative, sep } from "node:path";
import { fileURLToPath } from "node:url";

// The repository's root, reached from this file's place in the build output.
const root = fileURLToPath(new URL("../../", import.meta.url));

// Every `.stel` file under the directories given, relative to the root, each
// with its text, in a stable order.
export const readStelUnder = (dirs) => () => {
  const found = [];
  const walk = (dir) => {
    if (!existsSync(dir)) return;
    for (const name of readdirSync(dir).sort()) {
      const path = join(dir, name);
      if (statSync(path).isDirectory()) walk(path);
      else if (name.endsWith(".stel")) found.push({ path: relative(root, path).split(sep).join("/"), text: readFileSync(path, "utf8") });
    }
  };
  for (const dir of dirs) walk(join(root, dir));
  return found;
};
