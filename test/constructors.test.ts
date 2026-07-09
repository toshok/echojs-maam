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

test("new + this: the constructor builds and returns the object", () => {
  assert.deepEqual(
    concreteResult(`function Point(x, y) { this.x = x; this.y = y; } const p = new Point(3, 4); p.x + p.y;`),
    [7],
  );
});

test("new: an explicit object return overrides `this`", () => {
  assert.deepEqual(
    concreteResult(`function F() { this.a = 1; return { b: 2 }; } const o = new F(); o.b;`),
    [2],
  );
});

test("constructors(): a monomorphic constructor reports one struct", () => {
  const r = analyze(parse(`function Point(x, y) { this.x = x; this.y = y; } new Point(1, 2); 0;`), kCFA(1));
  const ctors = r.constructors();
  const point = ctors.find((c) => c.name === "Point")!;
  assert.equal(point.monomorphic, true);
  assert.deepEqual(point.shapes.map(shapeToString), ["{x: num, y: num}"]);
  assert.equal(point.layouts[0]!.sizeBytes, 16);
  assert.deepEqual(r.warnings(), []);
});

test("constructors(): construction intermediates don't create false polymorphism", () => {
  // {}, {a}, {a,b} — the intermediate shapes must not make this look polymorphic.
  const r = analyze(parse(`function C() { this.a = 1; this.b = 2; this.c = 3; } new C(); 0;`), kCFA(1));
  const c = r.constructors().find((x) => x.name === "C")!;
  assert.equal(c.monomorphic, true);
  assert.deepEqual(c.shapes.map(shapeToString), ["{a: num, b: num, c: num}"]);
});

test("WARNING: a constructor that builds incompatible shapes is flagged", () => {
  const src = `
    function Node(leaf) {
      if (leaf) { this.value = 1; }
      else { this.left = 0; this.right = 0; }
    }
    new Node(true);
    new Node(false);
    0;`;
  const r = analyze(parse(src), kCFA(1));
  const node = r.constructors().find((c) => c.name === "Node")!;
  assert.equal(node.monomorphic, false);
  assert.deepEqual(node.shapes.map(shapeToString).sort(), ["{left: num, right: num}", "{value: num}"]);

  const warns = r.warnings();
  assert.equal(warns.length, 1);
  assert.equal(warns[0]!.kind, "polymorphic-constructor");
  assert.match(warns[0]!.message, /Node/);
  assert.match(warns[0]!.message, /2 distinct hidden classes/);
});

test("WARNING: a representation-unstable field makes a constructor polymorphic", () => {
  const src = `
    function Box(useText) {
      this.v = 0;
      if (useText) { this.v = "text"; }
    }
    new Box(true);
    new Box(false);
    0;`;
  const r = analyze(parse(src), kCFA(1));
  const box = r.constructors().find((c) => c.name === "Box")!;
  assert.equal(box.monomorphic, false);
  assert.deepEqual(box.shapes.map(shapeToString).sort(), ["{v: num}", "{v: str}"]);
  assert.equal(r.warnings().length, 1);
});

test("constructor span points back to source", () => {
  const src = `function Widget() { this.w = 1; } new Widget(); 0;`;
  const r = analyze(parse(src), kCFA(1));
  const w = r.constructors().find((c) => c.name === "Widget")!;
  assert.ok(w.span);
  assert.match(src.slice(w.span!.start, w.span!.end), /^function Widget/);
});
