const log = [];

export const events = () => log.slice();

export const say = (s) => () => {
  log.push(`say:${s}`);
};
export const culprit = (_u) => 0;
