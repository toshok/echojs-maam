import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval, kCFA } from "../src/index.js";
import { shapeToString, type SizeOf } from "../src/index.js";

test("monomorphic site ⇒ a single struct with packed offsets and size", () => {
  const r = analyze(parse(`const o = { x: 1, y: 2 }; 0;`), kCFA(1));
  const sites = r.layouts();
  assert.equal(sites.length, 1);
  const site = sites[0]!;
  assert.equal(site.monomorphic, true);
  assert.equal(site.layouts.length, 1);
  const s = site.layouts[0]!;
  assert.deepEqual(
    s.fields.map((f) => [f.name, f.type, f.offsetBytes, f.sizeBytes]),
    [
      ["x", "num", 0, 8],
      ["y", "num", 8, 8],
    ],
  );
  assert.equal(s.sizeBytes, 16);
});

test("field representations become field types; bool aligns/packs", () => {
  const r = analyze(parse(`const o = { flag: true, count: 7, label: "hi", child: {} }; 0;`), kCFA(1));
  // two sites: the outer object and the inner {}
  const outer = r.layouts().find((l) => l.layouts[0] && l.layouts[0].fields.length === 4)!;
  // Fields are laid out in the class's canonical (sorted-by-name) order — order is
  // a layout concern the compiler owns, not part of class identity.
  const fields = outer.layouts[0]!.fields.map((f) => [f.name, f.type, f.offsetBytes]);
  assert.deepEqual(fields, [
    ["child", "obj", 0],
    ["count", "num", 8],
    ["flag", "bool", 16], // bool packs to 1 byte…
    ["label", "str", 24], // …and the next field re-aligns to 8
  ]);
});

test("the source span maps a site back to code", () => {
  const src = `const o = { a: 1 }; 0;`;
  const r = analyze(parse(src), kCFA(1));
  const site = r.layouts()[0]!;
  assert.ok(site.span, "expected a span");
  assert.equal(src.slice(site.span!.start, site.span!.end), `{ a: 1 }`);
});

test("intermediate construction shapes are filtered; only the terminal struct remains", () => {
  // {} → {a} → {a,b}: the finished struct is {a,b}.
  const r = analyze(parse(`const o = {}; o.a = 1; o.b = 2; 0;`), concreteEval());
  const site = r.layouts()[0]!;
  assert.equal(site.monomorphic, true);
  assert.deepEqual(site.shapes.map(shapeToString), ["{a: num, b: num}"]);
});

test("polymorphic site: incompatible shapes at one allocation ⇒ multiple structs, not monomorphic", () => {
  // one literal `{}` that grows differently depending on the argument. At 1-CFA
  // each `make` call gets its own object context, so the two shapes stay apart.
  // (At 0-CFA the site's objects would merge and fields would accumulate — a nice
  // illustration of why context-sensitivity matters for precise layouts.)
  const src = `
    function make(cond) {
      const o = {};
      if (cond) { o.a = 1; } else { o.b = 2; }
      return o;
    }
    make(true);
    make(false);
    0;`;
  const r = analyze(parse(src), kCFA(1));
  const poly = r.layouts().find((l) => !l.monomorphic);
  assert.ok(poly, "expected a polymorphic site");
  const shapes = poly!.shapes.map(shapeToString).sort();
  assert.deepEqual(shapes, ["{a: num}", "{b: num}"]);
  assert.equal(poly!.layouts.length, 2, "one struct per terminal shape");
});

test("representation-unstable field ⇒ the site is polymorphic (needs a tagged/union slot)", () => {
  // o.v is a number on one path and a string on another
  const src = `
    function make(cond) {
      const o = { v: 1 };
      if (cond) { o.v = "text"; }
      return o;
    }
    make(true); make(false); 0;`;
  const r = analyze(parse(src), concreteEval());
  const site = r.layouts().find((l) => l.shapes.length > 1);
  assert.ok(site, "expected the reassigned-type site to be polymorphic");
  assert.deepEqual(site!.shapes.map(shapeToString).sort(), ["{v: num}", "{v: str}"]);
});

test("a custom sizeOf model is honored", () => {
  const tagged: SizeOf = (t) => (t === "num" ? 4 : 8); // 32-bit ints
  const r = analyze(parse(`const o = { a: 1, b: 2 }; 0;`), kCFA(1));
  const s = r.layouts(tagged)[0]!.layouts[0]!;
  assert.deepEqual(
    s.fields.map((f) => [f.name, f.offsetBytes, f.sizeBytes]),
    [
      ["a", 0, 4],
      ["b", 4, 4],
    ],
  );
  assert.equal(s.sizeBytes, 8);
});
