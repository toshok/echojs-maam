import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, kCFA } from "../src/index.js";
import type { AVal } from "../src/lang/values.js";
import type { Loc } from "../src/lang/core.js";

/**
 * Standard-library intrinsic modeling (`intrinsics` knob, 11th kCFA arg): modeled
 * globals resolve to sound summary types instead of degrading to `⊤`/unknown.
 */
const on = kCFA(0, "flow-sensitive", "call-site", 0, true, true, false, 0, false, true);
const off = kCFA(0, "flow-sensitive", "call-site", 0, true, true, false, 0, false, false);

const val = (src: string, spec = on): AVal<Loc> => analyze(parse(src), spec).result as AVal<Loc>;
const hasNum = (v: AVal<Loc>): boolean => v.nums.top || !v.nums.items.isEmpty();
const hasStr = (v: AVal<Loc>): boolean => v.strs.top || !v.strs.items.isEmpty();

test("Math.floor returns a number (method-call intrinsic)", () => {
  assert.equal(hasNum(val(`Math.floor(3.7);`)), true);
});

test("Math.PI is a numeric constant (data property on the namespace object)", () => {
  const v = val(`Math.PI;`);
  assert.equal(v.nums.top, false);
  assert.deepEqual(v.nums.items.toArray(), [Math.PI]);
});

test("parseInt returns a number (bare-function intrinsic)", () => {
  assert.equal(hasNum(val(`parseInt("42");`)), true);
});

test("String.fromCharCode returns a string", () => {
  assert.equal(hasStr(val(`String.fromCharCode(65);`)), true);
});

test("new Array(n) yields an object with a numeric length", () => {
  assert.equal(hasNum(val(`var a = new Array(5); a.length;`)), true);
});

test("Number(x) coerces to number while Number.isInteger reads the statics object", () => {
  assert.equal(hasNum(val(`Number("3");`)), true); // callable component
  // Number.isInteger is a bool-returning static — resolvable, not degraded.
  const spec = analyze(parse(`Number.isInteger(5);`), on).result as AVal<Loc>;
  assert.equal(spec.bools.isEmpty(), false);
});

test("without the knob, the same globals degrade (unmodeled)", () => {
  // `Math` is unbound ⇒ Math.floor(...) degrades; the result is not a precise num.
  const v = val(`Math.floor(3.7);`, off);
  assert.equal(hasNum(v), false);
});
