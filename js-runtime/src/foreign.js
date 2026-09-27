import { refusal } from "./brand.js";

// What an implementation returns where it will not produce a value: a foreign, or an
// action a foreign returned. The runtime reports it as a fault carrying the reason.
//
// An implementation that only ever returns values does not import this.
export const refuse = (reason) => Object.freeze({ [refusal]: String(reason) });
