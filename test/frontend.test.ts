import { test } from "node:test";
import assert from "node:assert/strict";

import { parse, parseExpr } from "../src/lang/parse.js";
import { spanOf, walk } from "../src/lang/ast.js";
import { checkRestrictions } from "../src/lang/restrictions.js";
import { normalizeProgram, NormalizeError } from "../src/lang/normalize.js";
import { analyze, concreteEval } from "../src/index.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

function concreteResult(src: string): unknown[] {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set]
    .map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t))
    .sort();
}

test("parse produces an ESTree Program with ranges", () => {
  const p = parse(`const x = 1; x + 2;`);
  assert.equal(p.type, "Program");
  assert.equal(p.body.length, 2);
  assert.equal(p.body[0]!.type, "VariableDeclaration");
  const span = spanOf(p.body[0]!);
  assert.ok(span.end > span.start, "ranges should be populated");
});

test("parseExpr parses a single expression and rejects trailing input", () => {
  assert.equal(parseExpr(`1 + 2 * 3`).type, "BinaryExpression");
  assert.throws(() => parseExpr(`1; 2`));
});

test("walk visits nested nodes", () => {
  const p = parse(`const f = (x) => x + 1;`);
  const kinds = new Set([...walk(p)].map((n) => n.type));
  assert.ok(kinds.has("ArrowFunctionExpression"));
  assert.ok(kinds.has("BinaryExpression"));
  assert.ok(kinds.has("Identifier"));
});

test("restrictions report accurate spans on ESTree", () => {
  const src = `const a = 1; const b = eval("2");`;
  const v = checkRestrictions(parse(src));
  assert.equal(v.length, 1);
  assert.equal(v[0]!.rule, "no-eval");
  assert.equal(src.slice(v[0]!.span.start, v[0]!.span.end), `eval("2")`);
});

test("restrictions catch new Function, Function(), and with", () => {
  assert.equal(checkRestrictions(parse(`new Function("x","return x");`))[0]!.rule, "no-new-function");
  assert.equal(checkRestrictions(parse(`Function("return 1");`))[0]!.rule, "no-function-constructor");
  assert.equal(checkRestrictions(parse(`with (o) { x; }`))[0]!.rule, "no-with");
});

test("normalize: multiple declarators bind left-to-right", () => {
  assert.deepEqual(concreteResult(`const a = 10, b = a + 5; b;`), [15]);
});

test("normalize: bare `undefined` and `null` literals", () => {
  assert.deepEqual(concreteResult(`undefined;`), ["undef"]);
  assert.deepEqual(concreteResult(`null;`), ["null"]);
  assert.deepEqual(concreteResult(`typeof 5;`), ["number"]);
});

test("normalize: empty statements are ignored", () => {
  assert.deepEqual(concreteResult(`;; const x = 3;; x;;`), [3]);
});

test("normalize rejects out-of-dialect constructs with clear errors", () => {
  const rejects: Array<[string, RegExp]> = [
    [`const f = (x) => x; f(...args);`, /spread/],
    [`const f = ({...r}) => r;`, /object rest/],
  ];
  for (const [src, re] of rejects) {
    assert.throws(() => normalizeProgram(parse(src)), re, `expected ${src} to be rejected`);
  }
});

test("normalize: nullish coalescing and optional chains", () => {
  assert.deepEqual(concreteResult(`null ?? 7;`), [7]);
  assert.deepEqual(concreteResult(`undefined ?? 7;`), [7]);
  assert.deepEqual(concreteResult(`0 ?? 7;`), [0]);
  assert.deepEqual(concreteResult(`"" ?? 7;`), [""]);
  assert.deepEqual(concreteResult(`false ?? 7;`), [false]);
  assert.deepEqual(concreteResult(`const o = { a: 1 }; o?.a;`), [1]);
  assert.deepEqual(concreteResult(`const o = null; o?.a;`), ["undef"]);
  assert.deepEqual(concreteResult(`const o = undefined; o?.a?.b;`), ["undef"]);
  // short-circuit covers the whole chain, not just the next link
  assert.deepEqual(concreteResult(`const o = null; o?.a.b;`), ["undef"]);
  assert.deepEqual(concreteResult(`const o = { a: { b: 3 } }; o?.a?.b;`), [3]);
  assert.deepEqual(concreteResult(`const o = { a: 5 }; o?.["a"];`), [5]);
  assert.deepEqual(concreteResult(`const f = null; f?.(1);`), ["undef"]);
  assert.deepEqual(concreteResult(`const f = (x) => x + 1; f?.(1);`), [2]);
  assert.deepEqual(concreteResult(`const o = { m() { return 9; } }; o.m?.();`), [9]);
  assert.deepEqual(concreteResult(`const o = {}; o.m?.();`), ["undef"]);
  assert.deepEqual(concreteResult(`const o = null; o?.m();`), ["undef"]);
});

test("end-to-end still correct through the ESTree pipeline", () => {
  assert.deepEqual(
    concreteResult(`function fact(n){ if (n < 1) return 1; return n * fact(n-1); } fact(5);`),
    [120],
  );
});
