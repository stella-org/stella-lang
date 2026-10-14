import { refuse } from "@stella-lang/runtime/foreign";

const log = [];
let ticks = 0;
let opened;

export const events = () => log.slice();

export const say = (s) => () => {
  log.push(`say:${s}`);
};
export const tick = (u) => {
  ticks += 1;
  log.push(`tick:${typeof u}:${ticks}`);
  return ticks;
};
export const parse = (s) => {
  log.push(`parse:${s}`);
  return /^-?[0-9]+$/.test(s) ? Number(s) : refuse(`not a number: ${s}`);
};
export const add = (a, b) => {
  log.push(`add:${a}:${b}`);
  return a + b;
};
export const half = (x) => {
  log.push(`half:${typeof x}:${x}`);
  return x / 2;
};
export const nextChar = (c) => {
  log.push(`nextChar:${typeof c}:${c.length}:${c.codePointAt(0)}`);
  return String.fromCodePoint(c.codePointAt(0) + 1);
};
export const shout = (s) => {
  log.push(`shout:${s}`);
  return `${s}!`;
};
export const flip = (b) => {
  log.push(`flip:${typeof b}:${b}`);
  return !b;
};
export const note = (n) => {
  log.push(`note:${n}`);
  return 42;
};
export const negZero = (_u) => {
  log.push("negZero");
  return -0;
};
export const open = (n) => {
  opened = { n };
  log.push(`open:${n}`);
  return opened;
};
export const same = (h) => {
  log.push(`same:${h === opened}`);
  return h === opened;
};
export const readInt = (n) => () => {
  log.push(`readInt:${n}`);
  return n * 10;
};
export const readNumber = (u) => () => {
  log.push(`readNumber:${typeof u}`);
  return 2;
};
export const readChar = (u) => () => {
  log.push(`readChar:${typeof u}`);
  return "\u{1F600}";
};
export const readString = (u) => () => {
  log.push(`readString:${typeof u}`);
  return "ok";
};
export const readBool = (u) => () => {
  log.push(`readBool:${typeof u}`);
  return true;
};
export const readHandle = (u) => () => {
  log.push(`readHandle:${typeof u}`);
  return opened;
};
export const twice = (n) => {
  log.push(`twice:${n}`);
  return 2 * n;
};
