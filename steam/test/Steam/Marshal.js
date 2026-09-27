import { refuse } from "@stella-lang/runtime/foreign";

// Implementations as a JavaScript target writes them: functions of the host's own
// values, uncurried, importing the helper only where they refuse.

export const echo = (x) => x;

let received = [];
export const recording = (...args) => {
  received = args;
  return 0;
};
export const receivedImpl = () => received.map(String);
export const typesReceivedImpl = () => received.map((x) => typeof x);

export const twoPointZero = () => 2.0;
export const twoPointFive = () => 2.5;
export const outsideInt32 = () => 2 ** 31;
export const astral = () => "😀";
export const twoScalars = () => "ab";
export const halfAPair = () => "\uD83D";
export const loneSurrogate = () => "a\uDC00b";
export const yes = () => true;
export const aString = () => "stella";
export const anObject = () => ({ some: "host object" });

export const aPromise = Promise.resolve(42);
export const returnsPromise = () => aPromise;
export const isThePromise = (o) => o === aPromise;

export const refusing = () => refuse("nothing to give");

// A second copy of the helper: the same shape, a brand of its own. The runtime
// cannot recognise what it builds.
const anotherBrand = Symbol("stella.refuse");
export const refusingFromAnotherCopy = () => ({ [anotherBrand]: "nothing to give" });

export const actionOf = (produced) => () => () => produced;
export const actionRefusing = () => () => refuse("no action today");
export const actionThrowing = () => () => {
  throw new Error("thrown where it was performed");
};

let performed = 0;
export const countingAction = () => () => {
  performed += 1;
  return 1;
};
export const performedImpl = () => performed;
