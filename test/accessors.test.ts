import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval, kCFA } from "../src/index.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

function concreteResult(src: string): unknown[] {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set]
    .map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t === "undef" ? "undefined" : v.t))
    .sort();
}

// --- getter/setter semantics (dispatched as calls) -------------------------

test("an own getter runs with `this` = the receiver", () => {
  const src = `
    const o = {}; o._x = 42;
    Object.defineProperty(o, "x", { get: function () { return this._x; } });
    o.x;`;
  assert.deepEqual(concreteResult(src), [42]);
});

test("an own setter runs with `this` = the receiver and argument = the value", () => {
  const src = `
    const o = {}; o._x = 0;
    Object.defineProperty(o, "x", { set: function (v) { this._x = v; } });
    o.x = 99;
    o._x;`;
  assert.deepEqual(concreteResult(src), [99]);
});

test("an assignment through a setter evaluates to the assigned value", () => {
  const src = `
    const o = {}; o._x = 0;
    Object.defineProperty(o, "x", { set: function (v) { this._x = v; } });
    const r = (o.x = 7);
    r;`;
  assert.deepEqual(concreteResult(src), [7]);
});

// --- inherited (prototype) accessors — the class case ----------------------

test("a getter inherited from the prototype computes over `this`", () => {
  const src = `
    function Rect(w, h) { this.w = w; this.h = h; }
    Object.defineProperty(Rect.prototype, "area", { get: function () { return this.w * this.h; } });
    const r = new Rect(3, 4);
    r.area;`;
  assert.deepEqual(concreteResult(src), [12]);
});

test("a setter inherited from the prototype mutates `this`", () => {
  const src = `
    function C() { this._n = 0; }
    Object.defineProperty(C.prototype, "n", { set: function (v) { this._n = v; } });
    const c = new C();
    c.n = 7;
    c._n;`;
  assert.deepEqual(concreteResult(src), [7]);
});

test("Object.defineProperties installs a get/set accessor pair", () => {
  const src = `
    function Box() { this._v = 1; }
    Object.defineProperties(Box.prototype, {
      v: { get: function () { return this._v; }, set: function (x) { this._v = x; } }
    });
    const b = new Box();
    b.v = 10;
    b.v;`;
  assert.deepEqual(concreteResult(src), [10]);
});

// --- the inlining report ---------------------------------------------------

test("a monomorphic accessor site is reported as inlinable", () => {
  const src = `
    function Rect(w, h) { this.w = w; this.h = h; }
    Object.defineProperty(Rect.prototype, "area", { get: function () { return this.w * this.h; } });
    const a = new Rect(2, 3);
    const b = new Rect(4, 5);
    const x = a.area;
    const y = b.area;
    0;`;
  const sites = analyze(parse(src), kCFA(1)).accessorSites();
  const getterSites = sites.filter((s) => s.kind === "getter");
  assert.ok(getterSites.length >= 2, "both a.area and b.area should be accessor sites");
  for (const s of getterSites) {
    assert.equal(s.monomorphic, true, "each site resolves to the single `area` getter");
    assert.equal(s.targets.length, 1);
    assert.ok(s.span, "accessor site carries a source span");
  }
});

test("a plain data-property read is NOT an accessor site", () => {
  const src = `const o = { p: 1 }; const x = o.p; 0;`;
  assert.deepEqual(analyze(parse(src), kCFA(1)).accessorSites(), []);
});
