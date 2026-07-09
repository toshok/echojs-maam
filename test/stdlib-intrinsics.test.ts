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

// --- Phase 2: array/string prototype methods ---

test("array push returns a numeric length and slice returns a fresh array", () => {
  assert.equal(hasNum(val(`var a = [1, 2]; a.push(3);`)), true);
  const sliced = val(`var a = [1, 2, 3]; a.slice(1);`);
  assert.equal(sliced.objs.isEmpty(), false); // a new array object
});

test("array push mutates the receiver's elements (read back through an index)", () => {
  // The heap effect: `push` writes into the shared elements bucket, so `a[0]` sees it.
  assert.equal(hasStr(val(`var a = []; a.push("hi"); a[0];`)), true);
});

test("array indexOf → number, join → string, includes → boolean", () => {
  assert.equal(hasNum(val(`[1, 2].indexOf(2);`)), true);
  assert.equal(hasStr(val(`[1, 2].join(",");`)), true);
  assert.equal(val(`[1, 2].includes(2);`).bools.isEmpty(), false);
});

test("string methods dispatch on primitive receivers", () => {
  assert.equal(hasNum(val(`"abc".charCodeAt(0);`)), true);
  assert.equal(hasStr(val(`"hello".slice(1);`)), true);
  assert.equal(val(`"ab".startsWith("a");`).bools.isEmpty(), false);
  assert.equal(val(`"a,b".split(",");`).objs.isEmpty(), false); // a fresh array
});

test("array methods are unmodeled without the knob (degrade)", () => {
  // `[].push(...)` has no modeled prototype ⇒ result is not a precise number.
  assert.equal(hasNum(val(`var a = [1]; a.push(2);`, off)), false);
});

test("without the knob, the same globals degrade (unmodeled)", () => {
  // `Math` is unbound ⇒ Math.floor(...) degrades; the result is not a precise num.
  const v = val(`Math.floor(3.7);`, off);
  assert.equal(hasNum(v), false);
});
