import { refuse } from "@stella-lang/runtime/foreign";

const log = [];

export const events = () => log.slice();

export const say = (s) => () => {
  log.push(`say:${s}`);
};
export const culprit = (_u) => () => refuse("nothing to give");
