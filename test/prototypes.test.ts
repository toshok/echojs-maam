import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval, kCFA } from "../src/index.js";
import { shapeToString } from "../src/index.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

function concreteResult(src: string): unknown[] {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set].map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t)).sort();
}

test("a prototype method runs with `this` bound to the instance", () => {
  const src = `
    function Point(x, y) { this.x = x; this.y = y; }
    Point.prototype.sum = function () { return this.x + this.y; };
    const p = new Point(3, 4);
    p.sum();`;
  assert.deepEqual(concreteResult(src), [7]);
});

test("one prototype method is shared across instances", () => {
  const src = `
    function Box(v) { this.v = v; }
    Box.prototype.get = function () { return this.v; };
    const a = new Box(10);
    const b = new Box(20);
    a.get() + b.get();`;
  assert.deepEqual(concreteResult(src), [30]);
});

test("inherited data property is found up the chain", () => {
  const src = `
    function A() {}
    A.prototype.kind = "base";
    const a = new A();
    a.kind;`;
  assert.deepEqual(concreteResult(src), ["base"]);
});

test("an own property shadows the prototype", () => {
  const src = `
    function A() { this.kind = "own"; }
    A.prototype.kind = "base";
    const a = new A();
    a.kind;`;
  assert.deepEqual(concreteResult(src), ["own"]);
});

test("a missing property returns undefined after the chain is exhausted", () => {
  const src = `
    function A() {}
    A.prototype.p = 1;
    const a = new A();
    typeof a.nope;`;
  assert.deepEqual(concreteResult(src), ["undefined"]);
});

test("the instance struct excludes the prototype (methods are not data fields)", () => {
  const src = `
    function Pt(x, y) { this.x = x; this.y = y; }
    Pt.prototype.dist = function () { return this.x; };
    const p = new Pt(1, 2);
    0;`;
  const pt = analyze(parse(src), kCFA(1)).constructors().find((c) => c.name === "Pt")!;
  assert.deepEqual(pt.shapes.map(shapeToString), ["{x: num, y: num}"]);
});

test("prototype method call is analyzable under k-CFA (terminates, per-receiver)", () => {
  const src = `
    function Counter() { this.n = 0; }
    Counter.prototype.bump = function () { this.n = this.n + 1; return this.n; };
    const c = new Counter();
    c.bump(); c.bump();
    0;`;
  const r = analyze(parse(src), kCFA(1));
  assert.ok(r.collecting.reached.size > 0);
});
