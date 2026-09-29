import { Bug } from "@stella-lang/runtime/backend";

const log = [];

export const events = () => log.slice();

export const say = (s) => () => {
  log.push(`say:${s}`);
};
export const culprit = (_u) => {
  throw new Bug("a bug the host made");
};
