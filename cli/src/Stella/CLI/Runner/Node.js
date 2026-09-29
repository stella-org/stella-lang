import { createRequire } from "node:module";
import { isAbsolute } from "node:path";
import { pathToFileURL } from "node:url";
import { spawn } from "node:child_process";
import { Socket } from "node:net";
import { StringDecoder } from "node:string_decoder";

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

// A session channel over a Node socket: bytes cross as arrays of integers, and what
// arrives is queued until someone asks for it, so a reader that is not waiting at
// the moment a chunk arrives still gets it, in order.
const channelOf = (socket) => {
  const queued = [];
  const waiters = [];
  let last = null;
  const push = (event) => {
    if (last !== null) return;
    if (event.kind !== "data") last = event;
    const waiter = waiters.shift();
    if (waiter !== undefined) waiter(event);
    else queued.push(event);
  };
  socket.on("data", (buffer) => push({ kind: "data", bytes: Array.from(buffer) }));
  socket.on("end", () => push({ kind: "end" }));
  socket.on("close", () => push({ kind: "end" }));
  socket.on("error", (err) => push({ kind: "error", message: err.message }));
  return {
    send: (bytes) => {
      if (!socket.destroyed) socket.write(Buffer.from(bytes));
    },
    receive: (callback) => {
      if (queued.length > 0) callback(queued.shift());
      else if (last !== null) callback(last);
      else waiters.push(callback);
    },
    end: (callback) => {
      if (socket.destroyed || socket.writableFinished) callback();
      else socket.end(() => callback());
    },
    destroy: () => socket.destroy(),
  };
};

export const sendImpl = (channel) => (bytes) => () => channel.send(bytes);

export const receiveImpl = (channel) => (received) => (ended) => (failed) => (k) => () =>
  channel.receive((event) => {
    if (event.kind === "data") k(received(event.bytes))();
    else if (event.kind === "end") k(ended)();
    else k(failed(event.message))();
  });

export const endImpl = (channel) => (k) => () => channel.end(() => k());

export const destroyImpl = (channel) => () => channel.destroy();

// Descriptor 3 of this process, which whoever started it opened as the session's
// channel.
export const ownChannelImpl = (left) => (right) => () => {
  try {
    return right(channelOf(new Socket({ fd: 3, readable: true, writable: true })));
  } catch (err) {
    return left(err.message);
  }
};

// Start a session process with descriptor 3 as a bidirectional pipe. The exit is
// reported on `close`, which Node emits after every stdio stream of the child has
// closed, so nothing it wrote on its channel is still in flight when it is seen.
export const spawnSessionImpl = (command) => (args) => (drain) => () => {
  const stdio = drain === null
    ? ["ignore", "inherit", "inherit", "pipe"]
    : ["ignore", "pipe", "pipe", "pipe"];
  let exit = null;
  const waiters = [];
  const settle = (outcome) => {
    if (exit !== null) return;
    exit = outcome;
    for (const waiter of waiters.splice(0)) waiter(exit);
  };
  const onExit = (k) => () => {
    if (exit !== null) k(exit)();
    else waiters.push((e) => k(e)());
  };
  let child;
  try {
    child = spawn(command, args, { stdio });
  } catch (err) {
    settle({ code: null, signal: null, error: err.message });
    return { channel: null, onExit, kill: () => {} };
  }
  if (drain !== null) {
    decodeInto(child.stdout, drain.stdout);
    decodeInto(child.stderr, drain.stderr);
  }
  child.on("error", (err) => {
    // a process that never started emits no `close` of its own on every platform
    if (child.pid === undefined) settle({ code: null, signal: null, error: err.message });
  });
  child.on("close", (code, signal) => settle({ code, signal, error: null }));
  const socket = child.stdio[3] ?? null;
  return {
    channel: socket === null ? null : channelOf(socket),
    onExit,
    kill: () => {
      if (exit === null) child.kill("SIGKILL");
    },
  };
};

// A stream read as UTF-8 text. One decoder per stream holds the bytes of a
// character a chunk ends inside until the next chunk completes it, so a character
// split between two chunks arrives whole; what is left at the end is flushed.
const decodeInto = (stream, write) => {
  const decoder = new StringDecoder("utf8");
  stream.on("data", (b) => {
    const text = decoder.write(b);
    if (text.length > 0) write(text)();
  });
  stream.on("end", () => {
    const rest = decoder.end();
    if (rest.length > 0) write(rest)();
  });
};
