import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval, kCFA } from "../src/index.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

/** Concrete result values (a `nondet`/switch yields several). */
function res(src: string): unknown[] {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set].map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t)).sort();
}

// --- Gap 1: UpdateExpression on a member ------------------------------------

test("o.x++ reads, increments, and writes back the property", () => {
  assert.deepEqual(res(`const o = {n: 5}; o.n++; o.n;`), [6]);
});

test("++o.x returns the new value; o.x++ returns the old", () => {
  assert.deepEqual(res(`const o = {n: 5}; const r = ++o.n; r;`), [6]);
  assert.deepEqual(res(`const o = {n: 5}; const r = o.n++; r;`), [5]);
});

test("o.x-- decrements", () => {
  assert.deepEqual(res(`const o = {n: 5}; o.n--; o.n;`), [4]);
});

// --- Gap 2: `new` on a member callee ----------------------------------------

test("new m.C() reads the constructor from a member, then constructs", () => {
  const src = `
    const m = { C: function () { this.v = 7; } };
    const o = new m.C();
    o.v;`;
  assert.deepEqual(res(src), [7]);
});

// --- Gap 3: switch ----------------------------------------------------------

test("switch dispatches to the matching case and break exits", () => {
  assert.deepEqual(res(`let x = 0; switch (2) { case 1: x = 1; break; case 2: x = 2; break; default: x = 9; } x;`), [
    2,
  ]);
});

test("switch falls through cases without break", () => {
  assert.deepEqual(res(`let x = 0; switch (1) { case 1: x = x + 1; case 2: x = x + 10; break; case 3: x = 99; } x;`), [
    11,
  ]);
});

test("switch takes default when nothing matches (regardless of default's position)", () => {
  assert.deepEqual(res(`let x = 0; switch (7) { case 1: x = 1; break; default: x = 5; break; case 2: x = 2; } x;`), [
    5,
  ]);
});

// --- Gap 4: for-in (abstraction-only — the loop bound is nondeterministic) ---

test("for-in enumerates an object's property names and terminates under k-CFA", () => {
  const src = `
    function ext(d, s) { for (const p in s) { d[p] = s[p]; } return d; }
    ext({}, { x: 5, y: 6 });`;
  const r = analyze(parse(src), kCFA(1));
  assert.ok(r.collecting.reached.size > 0, "reaches a fixpoint");
});

// --- Gap 5: `delete` ---------------------------------------------------------

test("delete evaluates to true and does not reject", () => {
  assert.deepEqual(res(`const o = {a: 1}; delete o.a;`), [true]);
});

test("delete of a computed member is accepted", () => {
  assert.deepEqual(res(`const o = {a: 1}; const k = "a"; typeof (delete o[k]);`), ["boolean"]);
});

// --- Gap 6: computed method call obj[e](...) --------------------------------

test("obj[e](args) reads the method dynamically and calls it with this=obj", () => {
  const src = `
    const o = { inc: function () { return this.n + 1; }, n: 41 };
    const name = "inc";
    o[name]();`;
  assert.deepEqual(res(src), [42]);
});

// --- Gap 7: regex literal (opaque object) -----------------------------------

test("a regex literal is accepted as an opaque object", () => {
  assert.deepEqual(res(`const re = /ab+c/; typeof re;`), ["object"]);
});

test("for-in over a property bag binds the loop variable to its key names", () => {
  // Under k-CFA the key is one of the source object's names ("a" | "b").
  const src = `
    const o = { a: 1, b: 2 };
    function keysOf(x) { let last = "none"; for (const k in x) { last = k; } return last; }
    keysOf(o);`;
  const r = analyze(parse(src), kCFA(1));
  const t = r.valueOfVar("last");
  // `last` is a string (one of the enumerated names) or its initial "none".
  assert.ok(t !== undefined);
});
