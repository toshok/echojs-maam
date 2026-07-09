import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval, kCFA } from "../src/index.js";
import { shapeToString } from "../src/lang/shapes.js";
import { normalizeProgram, NormalizeError } from "../src/lang/normalize.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

function concreteResult(src: string): unknown[] {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set].map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t)).sort();
}

// --- object semantics ------------------------------------------------------

test("object literal: read properties", () => {
  assert.deepEqual(concreteResult(`const o = {a: 1, b: 2}; o.a + o.b;`), [3]);
});

test("object: reading a missing property yields undefined", () => {
  assert.deepEqual(concreteResult(`const o = {a: 1}; typeof o.zzz;`), ["undefined"]);
});

test("object: mutation is visible through an alias (reference semantics)", () => {
  // p and o are the same object; writing through p is seen through o.
  assert.deepEqual(concreteResult(`const o = {x: 1}; const p = o; p.x = 99; o.x;`), [99]);
});

test("object: concrete writes are strong updates", () => {
  assert.deepEqual(concreteResult(`const o = {x: 1}; o.x = 2; o.x = 3; o.x;`), [3]);
});

test("object: adding a property transitions the hidden class", () => {
  // final shape of `o` is {a: num, b: num}
  const r = analyze(parse(`const o = {}; o.a = 1; o.b = 2; o.a;`), concreteEval());
  const shapes = r.shapesOfVar("o").map(shapeToString);
  assert.ok(shapes.includes("{a: num, b: num}"), `expected {a: num, b: num} among ${JSON.stringify(shapes)}`);
  assert.deepEqual(concreteResult(`const o = {}; o.a = 1; o.b = 2; o.a;`), [1]);
});

test("hidden classes are TYPE-AWARE: same field name, different types ⇒ different classes", () => {
  // Two objects with the SAME property name but INCOMPATIBLE field types.
  const src = `
    function use(o) { return o; }
    const a = { data: 42 };       // {data: num}
    const b = { data: "hello" };  // {data: str}
    use(a);
    use(b);
    0;`;
  const r = analyze(parse(src), kCFA(0));
  const shapes = r.shapesOfVar("o").map(shapeToString).sort();
  // Structurally identical, but the representation splits them into two classes.
  assert.deepEqual(shapes, ["{data: num}", "{data: str}"]);
});

// --- the headline: parameter type = union of incoming hidden classes -------

test("a function called with two incompatible object shapes: its parameter's type is the union of both hidden classes", () => {
  const src = `
    // a "method" that receives an object
    function render(node) { return node; }

    // two INCOMPATIBLE object shapes (different hidden classes)
    const box    = { width: 10, height: 20 };
    const circle = { radius: 5, color: 1, filled: 1 };

    render(box);
    render(circle);
    0;
  `;
  const r = analyze(parse(src), kCFA(0));

  // The inferred type of the parameter `node` is the UNION of the two classes.
  // Shapes are order-insensitive: fields are stored in canonical (sorted) order.
  const shapes = r.shapesOfVar("node").map(shapeToString).sort();
  assert.deepEqual(shapes, ["{color: num, filled: num, radius: num}", "{height: num, width: num}"].sort());

  // ...and the call site is therefore polymorphic (megamorphic-ish): 2 shapes.
  assert.equal(shapes.length, 2, "parameter is polymorphic over two shapes");
});

test("monomorphic counterpart: same shape at both calls ⇒ a single hidden class", () => {
  const src = `
    function render(node) { return node; }
    const a = { width: 1, height: 2 };
    const b = { width: 3, height: 4 };   // same shape as a
    render(a);
    render(b);
    0;
  `;
  const r = analyze(parse(src), kCFA(0));
  const shapes = r.shapesOfVar("node").map(shapeToString);
  assert.deepEqual(shapes, ["{height: num, width: num}"], "monomorphic: exactly one shape");
});

// --- soundness / termination ----------------------------------------------

test("object allocation is context-parameterized and terminates under k-CFA", () => {
  // allocates an object every recursive call; abstract heap is finite ⇒ terminates
  const src = `
    function loop(n) { const o = {v: n}; if (n <= 0) return o.v; return loop(n - 1); }
    loop(100);`;
  const r = analyze(parse(src), kCFA(1));
  assert.ok(r.collecting.reached.size > 0);
});

// --- dialect boundaries ----------------------------------------------------

test("normalize rejects object features outside the analyzable core", () => {
  const rejects: Array<[string, RegExp]> = [
    [`const o = {[k]: 1};`, /computed object keys/],
    [`const o = {...a};`, /object spread/],
    [`const o = {get x() { return 1; }};`, /getters|setters/],
  ];
  for (const [src, re] of rejects) {
    assert.throws(() => normalizeProgram(parse(src)), re, `expected ${src} rejected`);
  }
});
