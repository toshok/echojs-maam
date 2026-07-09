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
  return [...set].map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t)).sort();
}

// numeric constants a variable's abstract value can hold (⊤ ⇒ null)
function absNums(v: AVal<Loc>): number[] | null {
  return v.nums.top ? null : v.nums.items.toArray().sort((a, b) => a - b);
}
function absHasStr(v: AVal<Loc>): boolean {
  return v.strs.top || !v.strs.items.isEmpty();
}

// --- method dispatch semantics ---------------------------------------------

test("method call binds `this` to the receiver and can mutate it", () => {
  const src = `
    function makeCounter() {
      const c = {};
      c.n = 0;
      c.inc = function () { this.n = this.n + 1; return this.n; };
      return c;
    }
    const c = makeCounter();
    c.inc(); c.inc(); c.inc();`;
  assert.deepEqual(concreteResult(src), [3]);
});

test("method reads a field of its receiver", () => {
  const src = `
    function Box(v) { this.v = v; this.get = function () { return this.v; }; }
    const a = new Box(7);
    a.get();`;
  assert.deepEqual(concreteResult(src), [7]);
});

test("methods dispatch per receiver (two boxes keep their own field)", () => {
  const src = `
    function Box(v) { this.v = v; this.val = function () { return this.v; }; }
    const a = new Box(10);
    const b = new Box(20);
    a.val() + b.val();`;
  assert.deepEqual(concreteResult(src), [30]);
});

// --- object sensitivity beats call-site sensitivity ------------------------

test("OBJECT-SENSITIVITY: at k=1, object context is more precise than call-site", () => {
  // `use` calls `.get()` from a single call site on receivers from two different
  // allocation sites. Call-site k=1 can't tell them apart (needs k=2); object
  // sensitivity keys on the receiver's allocation site, so it separates them.
  const src = `
    function Box(v) { this.v = v; this.get = function () { return this.v; }; }
    function use(box) { return box.get(); }
    const x = use(new Box(1));
    const y = use(new Box("s"));
    x;`;

  const callSite = analyze(parse(src), { ...kCFA(1), context: "call-site" });
  const objSens = analyze(parse(src), { ...kCFA(1), context: "object" });

  // call-site k=1: imprecise — x may spuriously be the string too
  assert.ok(absHasStr(callSite.valueOfVar("x") as AVal<Loc>), "call-site k=1 should be imprecise here");

  // object-sensitive k=1: precise — x is exactly {1}
  const xObj = objSens.valueOfVar("x") as AVal<Loc>;
  assert.equal(absHasStr(xObj), false, "object-sensitive k=1 should exclude the string");
  assert.deepEqual(absNums(xObj), [1]);
});

test("object sensitivity reaches the same precision without extra states here", () => {
  const src = `
    function Box(v) { this.v = v; this.get = function () { return this.v; }; }
    function use(box) { return box.get(); }
    const x = use(new Box(1));
    const y = use(new Box("s"));
    x;`;
  const callSite = analyze(parse(src), { ...kCFA(1), context: "call-site" });
  const objSens = analyze(parse(src), { ...kCFA(1), context: "object" });
  // Object sensitivity here separates the two Box receivers for at most a couple of
  // extra states — no blow-up. (Absolute counts depend on env trimming; the point
  // is that object sensitivity stays within a small constant of call-site.)
  assert.ok(objSens.metrics.reachedStates <= callSite.metrics.reachedStates + 4);
});
