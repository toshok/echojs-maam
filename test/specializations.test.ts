import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, kCFA } from "../src/index.js";
import type { SpecializationReport } from "../src/index.js";

const find = (specs: SpecializationReport[], name: string) => specs.find((s) => s.name === name)!;
const sig = (s: SpecializationReport) =>
  s.specializations
    .map((r) => `(${r.params.join(",")})->${r.returns}`)
    .sort()
    .join(" | ");

test("monomorphic function reports one (params → return) row", () => {
  const src = `function add(a, b) { return a + b; } add(1, 2); add(3, 4); 0;`;
  const add = find(analyze(parse(src), kCFA(1)).specializations(), "add");
  assert.equal(add.monomorphic, true);
  assert.deepEqual(add.paramNames, ["a", "b"]);
  assert.equal(sig(add), "(num,num)->num");
});

test("the return representation reflects the function body", () => {
  const src = `
    function sq(x) { return x * x; }
    function name(x) { return "n"; }
    sq(3); name(0); 0;`;
  const specs = analyze(parse(src), kCFA(1)).specializations();
  assert.equal(sig(find(specs, "sq")), "(num)->num");
  assert.equal(sig(find(specs, "name")), "(num)->str");
});

test("a polymorphic function splits into per-type specializations (k=1)", () => {
  const src = `function id(x) { return x; } const a = id(1); const b = id("s"); 0;`;
  const id = find(analyze(parse(src), kCFA(1)).specializations(), "id");
  assert.equal(id.monomorphic, false);
  assert.equal(sig(id), "(num)->num | (str)->str");
});

test("0-CFA merges the specializations (context matters)", () => {
  const src = `function id(x) { return x; } id(1); id("s"); 0;`;
  const id = find(analyze(parse(src), kCFA(0)).specializations(), "id");
  assert.equal(id.monomorphic, true);
  assert.equal(sig(id), "(num|str)->num|str");
});

test("WARNING: a function with multiple type specializations is flagged", () => {
  const src = `function id(x) { return x; } id(1); id("s"); id(true); 0;`;
  const warns = analyze(parse(src), kCFA(1)).warnings().filter((w) => w.kind === "polymorphic-function");
  assert.equal(warns.length, 1);
  assert.match(warns[0]!.message, /`id`/);
  assert.match(warns[0]!.message, /type specializations/);
});

test("a function returning an object reports `obj`", () => {
  const src = `function mk(v) { const o = {}; o.v = v; return o; } mk(1); 0;`;
  const mk = find(analyze(parse(src), kCFA(1)).specializations(), "mk");
  assert.equal(sig(mk), "(num)->obj");
});

test("specializations carry a source span", () => {
  const src = `function f(x) { return x; } f(1); 0;`;
  const f = find(analyze(parse(src), kCFA(1)).specializations(), "f");
  assert.ok(f.span);
  assert.match(src.slice(f.span!.start, f.span!.end), /^function f/);
});
