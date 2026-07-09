import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval, kCFA } from "../src/index.js";
import type { CVal, AVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

function concreteResult(src: string): unknown[] {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set]
    .map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t === "undef" ? "undefined" : v.t))
    .sort();
}

test("for loop accumulates", () => {
  assert.deepEqual(concreteResult(`let sum = 0; for (let i = 0; i < 5; i = i + 1) { sum = sum + i; } sum;`), [10]);
});

test("for loop with i++", () => {
  assert.deepEqual(concreteResult(`let s = 0; for (let i = 0; i < 4; i++) { s += i; } s;`), [6]);
});

test("while loop (factorial)", () => {
  assert.deepEqual(concreteResult(`let n = 4; let f = 1; while (n > 0) { f = f * n; n = n - 1; } f;`), [24]);
});

test("do-while runs the body at least once", () => {
  assert.deepEqual(concreteResult(`let i = 5; let c = 0; do { c = c + 1; i = i + 1; } while (i < 3); c;`), [1]);
});

test("break exits the loop", () => {
  assert.deepEqual(
    concreteResult(`let x = 0; for (let i = 0; i < 100; i = i + 1) { if (i === 3) { break; } x = i; } x;`),
    [2],
  );
});

test("continue skips to the next iteration", () => {
  assert.deepEqual(
    concreteResult(`let s = 0; for (let i = 0; i < 5; i = i + 1) { if (i === 2) { continue; } s = s + i; } s;`),
    [8],
  );
});

test("nested loops", () => {
  const src = `
    let count = 0;
    for (let i = 0; i < 3; i = i + 1) {
      for (let j = 0; j < 3; j = j + 1) {
        count = count + 1;
      }
    }
    count;`;
  assert.deepEqual(concreteResult(src), [9]);
});

test("abstract analysis TERMINATES on an unbounded loop (widening)", () => {
  // concretely infinite; the abstract analysis widens the counter to ⊤ and stops.
  const r = analyze(parse(`let x = 0; while (x < 1000000000) { x = x + 1; } x;`), kCFA(1));
  const nums = r.result as AVal<Loc>;
  assert.equal(nums.nums.top, true, "the counter widens to ⊤");
  assert.ok(r.collecting.reached.size > 0 && r.collecting.reached.size < 200, "finite, small state space");
});
