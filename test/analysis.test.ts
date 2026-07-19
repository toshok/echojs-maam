import { test } from "node:test";
import assert from "node:assert/strict";

import { analyze, analyzeCore, concreteEval, kCFA } from "../src/index.js";
import { parse } from "../src/lang/parse.js";
import { checkRestrictions } from "../src/lang/restrictions.js";
import { normalizeProgram, NormalizeError } from "../src/lang/normalize.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";
import type { Sensitivity } from "../src/index.js";

/** Extract the concrete result set as sorted primitives for comparison. */
function concreteResult(src: string): unknown[] {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set]
    .map((v) => {
      switch (v.t) {
        case "num":
          return v.v;
        case "bool":
          return v.v;
        case "str":
          return v.v;
        case "null":
          return null;
        case "undef":
          return "undefined";
        case "clo":
          return "<closure>";
        case "obj":
          return "<object>";
        case "top":
          return "⊤";
      }
    })
    .sort();
}

test("concrete: identity application", () => {
  assert.deepEqual(concreteResult(`const id = (x) => x; id(42);`), [42]);
});

test("concrete: arithmetic and precedence", () => {
  assert.deepEqual(concreteResult(`1 + 2 * 3;`), [7]);
  assert.deepEqual(concreteResult(`(1 + 2) * 3;`), [9]);
});

test("concrete: recursive factorial", () => {
  assert.deepEqual(
    concreteResult(`function fact(n){ if (n < 1) return 1; return n * fact(n-1); } fact(5);`),
    [120],
  );
});

test("concrete: mutual recursion (even/odd)", () => {
  const src = `
    function even(n){ if (n === 0) return true; return odd(n - 1); }
    function odd(n){ if (n === 0) return false; return even(n - 1); }
    even(10);`;
  assert.deepEqual(concreteResult(src), [true]);
});

test("concrete: higher-order functions", () => {
  const src = `
    const apply = (f, x) => f(x);
    const inc = (a) => a + 1;
    apply(inc, apply(inc, 40));`;
  assert.deepEqual(concreteResult(src), [42]);
});

test("concrete: closures capture their environment", () => {
  const src = `
    const adder = (n) => (m) => n + m;
    const add10 = adder(10);
    add10(5);`;
  assert.deepEqual(concreteResult(src), [15]);
});

test("concrete: conditionals and short-circuit", () => {
  assert.deepEqual(concreteResult(`const x = 3; if (x > 2) { 100; } else { 200; } x > 2 ? 1 : 0;`), [1]);
  assert.deepEqual(concreteResult(`true && 5;`), [5]);
  assert.deepEqual(concreteResult(`false || 9;`), [9]);
});

test("concrete: named function expression self-recursion", () => {
  const src = `
    const f = function loop(n) { if (n <= 0) return 0; return n + loop(n - 1); };
    f(4);`;
  assert.deepEqual(concreteResult(src), [10]); // 4+3+2+1
});

// --- restrictions ----------------------------------------------------------

test("restriction: eval is rejected", () => {
  const v = checkRestrictions(parse(`const x = eval("1+1");`));
  assert.equal(v.length, 1);
  assert.equal(v[0]!.rule, "no-eval");
});

test("restriction: new Function is rejected", () => {
  const v = checkRestrictions(parse(`const f = new Function("return 1");`));
  assert.equal(v.length, 1);
  assert.equal(v[0]!.rule, "no-new-function");
});

test("restriction: Function(...) call is rejected", () => {
  const v = checkRestrictions(parse(`const f = Function("return 1");`));
  assert.equal(v.length, 1);
  assert.equal(v[0]!.rule, "no-function-constructor");
});

test("restriction: with is rejected", () => {
  const v = checkRestrictions(parse(`with (obj) { x; }`));
  assert.equal(v.length, 1);
  assert.equal(v[0]!.rule, "no-with");
});

test("restriction: clean program has no violations", () => {
  assert.deepEqual(checkRestrictions(parse(`const f = (x) => x + 1; f(1);`)), []);
});

test("restriction: analyze() throws on a violating program", () => {
  assert.throws(() => analyze(parse(`eval("x");`), concreteEval()), /restricted-JS dialect violated/);
});

test("normalize: `new` on a member callee is supported (reads the constructor, then constructs)", () => {
  assert.doesNotThrow(() => normalizeProgram(parse(`const x = new a.B();`)));
});

// --- abstraction: termination & soundness ----------------------------------

test("k-CFA terminates on a concretely-infinite program", () => {
  // loops forever concretely; abstract state space is finite ⇒ must terminate.
  const src = `function loop(n){ return loop(n + 1); } loop(0);`;
  const r = analyze(parse(src), kCFA(0));
  assert.ok(r.collecting.iterations > 0);
  assert.ok(r.collecting.reached.size > 0);
});

test("soundness: path-sensitive result ⊑ flow-insensitive result", () => {
  const src = `
    const apply = (f, x) => f(x);
    const inc = (a) => a + 1;
    const dbl = (b) => b * 2;
    apply(inc, 10) + apply(dbl, 20);`;
  const prog = parse(src);
  const ps = analyze(prog, { ...kCFA(1), sensitivity: "path-sensitive" as Sensitivity });
  const fi = analyze(prog, { ...kCFA(1), sensitivity: "flow-insensitive" as Sensitivity });
  // more precise (path) approximates below less precise (flow-insensitive)
  assert.ok(
    ps.domain.lattice.lte(ps.result, fi.result),
    "path-sensitive must be at least as precise as flow-insensitive",
  );
});

test("all three sensitivities agree with the concrete result (are sound)", () => {
  const src = `const twice = (f) => (x) => f(f(x)); const inc = (a) => a + 1; twice(inc)(0);`;
  // concrete answer is 2
  assert.deepEqual(concreteResult(src), [2]);
  const prog = parse(src);
  for (const sensitivity of ["path-sensitive", "flow-sensitive", "flow-insensitive"] as const) {
    const r = analyze(prog, { ...kCFA(1), sensitivity });
    // 1-CFA should still nail this to exactly {2}
    const nums = r.result as { nums: { top: boolean; items: FinSet<number> } };
    assert.ok(!nums.nums.top, `${sensitivity}: expected a precise number, got ⊤`);
    assert.deepEqual(nums.nums.items.toArray(), [2], `${sensitivity}: expected {2}`);
  }
});

test("metrics report the abstract state space", () => {
  const r = analyze(parse(`const id = (x) => x; id(1); id(2);`), kCFA(1));
  assert.ok(r.metrics.reachedStates > 0);
  assert.ok(r.metrics.configs >= r.metrics.reachedStates);
  assert.ok(r.metrics.iterations > 0);
  assert.equal(r.metrics.reachedStates, r.collecting.reached.size);
  assert.equal(r.metrics.configs, r.collecting.configs.size);
});

test("more context (higher k) is at least as precise (polyvariance)", () => {
  const src = `
    function apply(f, x) { return f(x); }
    const inc = a => a + 1; const dbl = b => b * 2;
    const r1 = apply(inc, 10); const r2 = apply(dbl, 20); r1 + r2;`;
  const nums = (r: { result: unknown }) =>
    (r.result as { nums: { items: { toArray(): number[] } } }).nums.items.toArray().sort((a, b) => a - b);
  // 0-CFA merges the two uses of `apply`, admitting spurious combinations;
  // 1-CFA keeps the call sites apart and pins the answer to exactly {51}.
  const at0 = nums(analyze(parse(src), kCFA(0)));
  const at1 = nums(analyze(parse(src), kCFA(1)));
  assert.ok(at0.length > 1, `0-CFA should be imprecise, got ${JSON.stringify(at0)}`);
  assert.deepEqual(at1, [51], "1-CFA should be exact");
  assert.ok(at1.every((n) => at0.includes(n)), "higher-k result must be ⊑ lower-k (sound)");
});

test("analyzeCore works on a pre-normalized program", () => {
  const { core } = normalizeProgram(parse(`const id = (x) => x; id(7);`));
  const r = analyzeCore(core, concreteEval());
  assert.equal(r.collecting.reached.size > 0, true);
});
