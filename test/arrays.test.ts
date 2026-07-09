import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval } from "../src/index.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

function results(src: string): unknown[] {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set]
    .map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t === "undef" ? "undefined" : v.t))
    .sort();
}

test("array literal length", () => {
  assert.deepEqual(results(`const a = [1, 2, 3]; a.length;`), [3]);
});

test("array indexing reads the (smashed) elements + possibly undefined", () => {
  // index-insensitive: any index may be any element, or out of bounds (undefined)
  const r = results(`const a = [10, 20, 30]; a[1];`);
  assert.ok(r.includes(10) && r.includes(20) && r.includes(30));
  assert.ok(!r.includes(3), "the length field does not leak into a numeric index read");
});

test("array element write is seen by later reads", () => {
  const r = results(`const a = [1, 2]; a[0] = 99; a[0];`);
  assert.ok(r.includes(99));
});

test("computed access with a constant key is a precise static read", () => {
  assert.deepEqual(results(`const o = { foo: 42, bar: 9 }; o["foo"];`), [42]);
});

test("computed assignment with a constant key is a precise static write", () => {
  assert.deepEqual(results(`const o = {}; o["x"] = 7; o.x;`), [7]);
});

test("a dynamic string key reads over the object's fields (sound blur)", () => {
  const r = results(`const o = { a: 1 }; let k = "a"; o[k];`);
  assert.ok(r.includes(1), "must include the actual value");
});

test("array literals of objects hold object references", () => {
  // m[0] is an object (array); reading a field of it works through the element bucket
  assert.deepEqual(results(`const m = [{ v: 5 }]; const first = m[0]; first.v;`), [5]);
});

test("array spread is rejected", () => {
  assert.throws(() => analyze(parse(`const a = [1]; const b = [...a];`), concreteEval()), /spread/);
});
