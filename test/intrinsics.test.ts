import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval } from "../src/index.js";
import { normalizeProgram, NormalizeError } from "../src/lang/normalize.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

function concreteResult(src: string): unknown[] {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set].map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t)).sort();
}

// These mirror the shape EchoJS's `desugar-classes` pass emits (methods via
// Object.defineProperty on the prototype, inheritance via Object.create +
// Object.setPrototypeOf).

test("Object.defineProperty installs a prototype method (class method desugaring)", () => {
  const src = `
    function Point(x, y) { this.x = x; this.y = y; }
    Object.defineProperty(Point.prototype, "sum", { value: function () { return this.x + this.y; }, enumerable: false });
    const p = new Point(3, 4);
    p.sum();`;
  assert.deepEqual(concreteResult(src), [7]);
});

test("Object.create + Object.setPrototypeOf build a 2-level inheritance chain", () => {
  const src = `
    function Base() {}
    Object.defineProperty(Base.prototype, "greet", { value: function () { return "hi"; } });
    function Derived() {}
    Object.setPrototypeOf(Derived.prototype, Object.create(Base.prototype));
    const d = new Derived();
    d.greet();`;
  assert.deepEqual(concreteResult(src), ["hi"]);
});

test("a subclass can override an inherited method (own prototype shadows)", () => {
  const src = `
    function Base() {}
    Object.defineProperty(Base.prototype, "who", { value: function () { return "base"; } });
    function Derived() {}
    Object.setPrototypeOf(Derived.prototype, Object.create(Base.prototype));
    Object.defineProperty(Derived.prototype, "who", { value: function () { return "derived"; } });
    const d = new Derived();
    d.who();`;
  assert.deepEqual(concreteResult(src), ["derived"]);
});

test("Object.defineProperties installs several data properties in order", () => {
  const src = `
    const o = {};
    Object.defineProperties(o, { a: { value: 1 }, b: { value: 2 } });
    o.a + o.b;`;
  assert.deepEqual(concreteResult(src), [3]);
});

test("Object.create(proto) links the prototype of a fresh object", () => {
  const src = `
    const base = {};
    base.tag = "T";
    const o = Object.create(base);
    o.tag;`;
  assert.deepEqual(concreteResult(src), ["T"]);
});

test("object spread is still rejected", () => {
  assert.throws(
    () => normalizeProgram(parse(`const a = {}; const b = { ...a };`)),
    (e: unknown) => e instanceof NormalizeError,
  );
});
