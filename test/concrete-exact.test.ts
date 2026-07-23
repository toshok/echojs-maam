import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval, kCFA } from "../src/index.js";
import type { AnalysisSpec, Sensitivity } from "../src/index.js";
import type { AVal, CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

/**
 * Exact standard-library evaluation under the concrete domain — the contract
 * the differential harness (test/differential/harness.ts) rests on: with
 * `intrinsics: true`, a concrete run either computes the REAL JS result of an
 * intrinsic call (pure primitives: `Math.*`, `parseInt`, `String.prototype.*`,
 * …) or degrades VISIBLY through `metrics.unknownCalls` (heap-touching
 * intrinsics, nondeterminism) — never a summary, never a silent wrong value.
 *
 * Also pins the concrete-semantics bugs the harness work surfaced:
 * string-string relational comparison and `null` numeric coercion.
 */

const spec = (): AnalysisSpec<FinSet<CVal<Loc>>> & { intrinsics: boolean } => ({
  ...concreteEval(),
  intrinsics: true,
});

type Run = { values: unknown[]; unknownCalls: number };
const run = (src: string): Run => {
  const r = analyze(parse(src), spec());
  const set = r.result as FinSet<CVal<Loc>>;
  const values = [...set].map((v) => {
    switch (v.t) {
      case "num":
      case "bool":
      case "str":
        return v.v;
      case "null":
        return null;
      case "undef":
        return undefined;
      case "clo":
        return "<closure>";
      case "obj":
        return "<object>";
      case "intr":
        return `<intrinsic ${v.id}>`;
      case "top":
        return "⊤";
    }
  });
  return { values, unknownCalls: r.metrics.unknownCalls };
};

/** The program must evaluate EXACTLY (no degradation) to the one given value. */
const exact = (src: string, expected: unknown): void => {
  const r = run(src);
  assert.equal(r.unknownCalls, 0, `expected no degradation for ${JSON.stringify(src)}`);
  assert.deepEqual(r.values, [expected]);
};

/** The program must degrade visibly (unknownCalls > 0) — never a made-up value. */
const degrades = (src: string): void => {
  const r = run(src);
  assert.ok(r.unknownCalls > 0, `expected visible degradation for ${JSON.stringify(src)}`);
};

// --- pure statics compute their real results ---

test("Math statics are exact: floor/max/pow/abs", () => {
  exact(`Math.floor(3.7);`, 3);
  exact(`Math.max(1, 9, -3);`, 9);
  exact(`Math.pow(2, 10);`, 1024);
  exact(`Math.abs(-5.5);`, 5.5);
});

test("Math constants read exactly", () => {
  exact(`Math.PI;`, Math.PI);
  exact(`Number.MAX_SAFE_INTEGER;`, Number.MAX_SAFE_INTEGER);
});

test("bare-function intrinsics are exact: parseInt/parseFloat/Number/String/Boolean", () => {
  exact(`parseInt("42");`, 42);
  exact(`parseInt("ff", 16);`, 255);
  exact(`parseFloat("3.5x");`, 3.5);
  exact(`Number("3.5");`, 3.5);
  exact(`String(42);`, "42");
  exact(`Boolean(0);`, false);
  exact(`isNaN("abc");`, true);
  exact(`Number.isInteger(5.0);`, true);
});

test("an intrinsic stored in a variable still applies exactly", () => {
  exact(`var f = Math.floor; f(3.2);`, 3);
});

test("intrinsics compose through user code", () => {
  exact(`function h(x) { return Math.sqrt(x) + 1; } h(16);`, 5);
});

test("typeof an intrinsic is \"function\"", () => {
  exact(`typeof Math.floor;`, "function");
});

// --- string prototype methods are exact on concretized receivers ---

test("string methods are exact: toUpperCase/slice/indexOf/charCodeAt/repeat", () => {
  exact(`"abc".toUpperCase();`, "ABC");
  exact(`"hello".slice(1, 3);`, "el");
  exact(`"a,b,c".indexOf(",");`, 1);
  exact(`"A".charCodeAt(0);`, 65);
  exact(`"ab".repeat(3);`, "ababab");
  exact(`var s = "mixed"; s.charAt(2);`, "x");
});

test("string .length reads exactly (was a confident-undefined unsoundness)", () => {
  exact(`"abc".length;`, 3);
  exact(`var s = "hello" + "!"; s.length;`, 6);
});

test("abstract string .length is num, not undefined", () => {
  const on = kCFA(0, "flow-sensitive" as Sensitivity, "call-site", 0, false, false, false, 0, false, true);
  const v = analyze(parse(`var s = "abc"; s.length;`), on).result as AVal<Loc>;
  assert.equal(v.undefP, false, "a pure-string receiver's .length must not include undefined");
  assert.ok(v.nums.top || !v.nums.items.isEmpty(), ".length must be a number");
});

// --- concrete-semantics fixes the harness surfaced ---

test("string-string relational comparison is lexicographic (harness finding)", () => {
  exact(`"a" < "b";`, true);
  exact(`"10" < "9";`, true); // string compare, NOT numeric
  exact(`"b" <= "a";`, false);
  exact(`"z" > "y";`, true);
  exact(`1 < "2";`, true); // mixed operands stay numeric
});

test("null coerces to 0 in arithmetic, undefined to NaN (harness finding)", () => {
  exact(`1 + null;`, 1);
  exact(`null < 1;`, true);
  const r = run(`1 + undefined;`);
  assert.equal(r.unknownCalls, 0);
  assert.equal(r.values.length, 1);
  assert.ok(Number.isNaN(r.values[0]), "1 + undefined must be NaN");
});

// --- everything not exactly computable degrades VISIBLY ---

test("Math.random degrades (nondeterminism is never exact)", () => {
  degrades(`Math.random();`);
});

test("heap-touching intrinsics degrade: push/join/split/new Array", () => {
  degrades(`var a = [1]; a.push(2);`);
  degrades(`var a = [1, 2]; a.join(",");`);
  degrades(`"a,b".split(",");`);
  degrades(`var a = new Array(3); a.length;`);
});

test("higher-order array methods degrade under the concrete domain", () => {
  degrades(`var a = [1, 2]; a.map(function (x) { return x + 1; });`);
});

test("new of an intrinsic degrades (a Number wrapper object is not the primitive)", () => {
  degrades(`var n = new Number(3); n;`);
});

test("a throwing intrinsic application degrades rather than guessing", () => {
  degrades(`"ab".repeat(-1);`); // RangeError in JS: not modeled, must not fake a value
});

// --- the summary path is untouched for the abstract domain ---

test("abstract intrinsics still summarize (Math.floor is num, not a constant)", () => {
  const on = kCFA(0, "flow-sensitive" as Sensitivity, "call-site", 0, false, false, false, 0, false, true);
  const v = analyze(parse(`Math.floor(3.7);`), on).result as AVal<Loc>;
  assert.equal(v.nums.top, true, "abstract Math.floor stays anyNum — summaries, not exact folding");
});
