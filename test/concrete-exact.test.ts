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

// --- normalizer/machine fixes the differential harness surfaced -------------
// Unit pins per adversarial review (F3): each of these flips if its fix is
// reverted — they do NOT depend on the harness or its corpus.

const runPlain = (src: string): Run => {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return {
    values: [...set].map((v) =>
      v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t === "null" ? null : v.t === "undef" ? undefined : v.t,
    ),
    unknownCalls: r.metrics.unknownCalls,
  };
};

test("hoisted function declaration writes a later-declared same-scope var", () => {
  // Pre-fix: `g` inside t was un-renamed; the write went to an unbound name
  // and was silently dropped — the run reported "" with zero degradation.
  exact(`var g = ""; function t(x) { g = g + x; return 1; } t("a"); g;`, "a");
});

test("function EXPRESSION created before a later var writes it (review F1)", () => {
  exact(`var f = function () { n = "x"; }; var n = 0; f(); n;`, "x");
});

test("arrow created before a later var writes it (review F1)", () => {
  exact(`var f = () => { n = "y"; }; var n = 0; f(); n;`, "y");
});

test("object-literal method created before a later var writes it (review F1)", () => {
  exact(`var o = { m: function () { n = "z"; } }; var n = 0; o.m(); n;`, "z");
});

test("declare-then-capture keeps the precise path (no hoisted-undefined widening)", () => {
  // The capture scan is positional: a closure created AFTER the declaration
  // uses ordinary scoping, and the variable's nodeTypes join must not pick up
  // the hoisted pre-binding's `undefined`.
  const src = `var n = 0; var f = function () { n = n + 1; }; f(); n;`;
  const r = analyze(parse(src), concreteEval());
  assert.deepEqual([...(r.result as FinSet<CVal<Loc>>)], [{ t: "num", v: 1 }]);
  const prog = parse(src);
  const r2 = analyze(prog, concreteEval());
  const decl = (prog.body[0] as { declarations: Array<{ id: unknown }> }).declarations[0]!.id;
  assert.equal(r2.typeOfNode(decl as never), "num", "declare-then-capture var must stay exactly num");
});

test("nested-block var captured by a function DEGRADES visibly (review F2)", () => {
  // Function-scope hoisting out of blocks is not modeled; what matters is that
  // the gap is COUNTED (degradedBindings) so the harness precondition trips —
  // never a silent ⊥ computation.
  const r = analyze(parse(`function s() { n = "x"; } if (true) { var n = 0; } s(); n;`), concreteEval());
  assert.ok(r.metrics.degradedBindings > 0, "unmodeled nested-var capture must count as a degraded binding");
  assert.ok(
    r.warnings().some((w) => w.kind === "degraded-binding" && w.message.includes("nested-block")),
    "and surface as a degraded-binding warning",
  );
});

test("captured destructuring-pattern leaf DEGRADES visibly (review R1)", () => {
  // `var f = function () { a = 9; }; var [a, b] = [1, 2]; f(); a;` — real JS
  // says 9; hoisted pattern-leaf capture is not modeled, so without the
  // accounting the concrete run would answer 1 with ZERO degradation
  // (silently wrong). The accounting makes the harness precondition trip.
  const r = analyze(parse(`var f = function () { a = 9; }; var [a, b] = [1, 2]; f(); a;`), concreteEval());
  assert.ok(r.metrics.degradedBindings > 0, "pattern-leaf capture must count as a degraded binding");
  assert.ok(
    r.warnings().some((w) => w.kind === "degraded-binding" && w.message.includes("pattern")),
    "and surface as a degraded-binding warning",
  );
  // Declare-then-capture pattern leaves work through ordinary scoping and
  // must NOT degrade.
  const ok = analyze(parse(`var [a, b] = [1, 2]; var f = function () { a = 9; }; f(); a;`), concreteEval());
  assert.equal(ok.metrics.degradedBindings, 0, "declare-then-capture pattern leaf is fine");
});

test("dialect `defaults` closures participate in the capture scan (review R2)", () => {
  // echojs post-desugar trees carry old-esprima `defaults` (a parallel array,
  // NOT ES6 AssignmentPatterns — acorn cannot produce this shape). A closure
  // inside a default expression that writes a later same-scope var must be
  // detected by the capture scan; pre-fix its write was silently dropped.
  const prog = parse(`function t(p) { return p(); } var n = 0; var r = t(); r + n;`);
  const fnExpr = (parse(`(function () { n = 7; return 1; });`).body[0] as unknown as { expression: unknown })
    .expression;
  (prog.body[0] as unknown as { defaults: unknown[] }).defaults = [fnExpr];
  const r = analyze(prog, spec());
  assert.equal(r.metrics.unknownCalls, 0);
  assert.equal(r.metrics.degradedBindings, 0);
  assert.deepEqual(
    [...(r.result as FinSet<CVal<Loc>>)],
    [{ t: "num", v: 8 }],
    "default-closure write must reach the later var (1 + 7)",
  );
});

test("bare NaN / Infinity identifiers are dialect literals, not unbound reads", () => {
  const nan = runPlain(`NaN;`);
  assert.equal(nan.values.length, 1, "NaN must evaluate, not kill the path");
  assert.ok(Number.isNaN(nan.values[0]), "…to the number NaN");
  assert.deepEqual(runPlain(`Infinity;`).values, [Infinity]);
  assert.deepEqual(runPlain(`var x = -Infinity; 1 / x;`).values, [-0]);
});

test("a ⊥-receiver property read propagates ⊥, never a confident undefined", () => {
  // Intrinsics OFF: `Math` is unbound (⊥). Pre-fix the read reported exact
  // `undefined` — the ⊑-violation the containment lane caught.
  const conc = runPlain(`Math.PI;`);
  assert.deepEqual(conc.values, [], "concrete: the path must die, not yield undefined");
  const abs = analyze(
    parse(`Math.PI;`),
    kCFA(0, "flow-sensitive" as Sensitivity, "call-site", 0, false, false, false, 0, false, false),
  ).result as AVal<Loc>;
  assert.equal(abs.undefP, false, "abstract: no undefined component from an unbound receiver");
});

// --- the summary path is untouched for the abstract domain ---

test("abstract intrinsics still summarize (Math.floor is num, not a constant)", () => {
  const on = kCFA(0, "flow-sensitive" as Sensitivity, "call-site", 0, false, false, false, 0, false, true);
  const v = analyze(parse(`Math.floor(3.7);`), on).result as AVal<Loc>;
  assert.equal(v.nums.top, true, "abstract Math.floor stays anyNum — summaries, not exact folding");
});
