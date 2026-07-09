/**
 * State-space telemetry: how big is the abstract analysis for a given program,
 * and how do the precision knobs move the numbers?
 *
 * Run with:  npm run bench
 *
 * The headline it demonstrates: more precision (higher `k`) can *shrink* the
 * state space and the iteration count, because removing spurious merges removes
 * the bogus successor states they generate.
 */

import { performance } from "node:perf_hooks";
import { analyze, kCFA, type ContextStrategy, type Sensitivity } from "../src/index.js";
import { parse } from "../src/lang/parse.js";
import type { AVal } from "../src/lang/values.js";
import type { Loc } from "../src/lang/core.js";

const PROGRAMS: Record<string, string> = {
  "higher-order polyvariance": `
    function apply(f, x) { return f(x); }
    function twice(g, y) { return apply(g, apply(g, y)); }
    const inc = a => a + 1; const dbl = b => b * 2;
    const r1 = twice(inc, 0); const r2 = twice(dbl, 1); r1 + r2;`,
  "factory objects": `
    function make(v) { const o = {}; o.val = v; return o; }
    const a = make(1); const b = make("s"); const c = make(true); a.val;`,
  "constructors + branching": `
    function Node(leaf, v) { if (leaf) { this.value = v; } else { this.l = 0; this.r = 0; } }
    const a = new Node(true, 1); const b = new Node(false, 2); a;`,
};

const rule = (s: string) => console.log(`\n\x1b[1m${s}\x1b[0m\n${"─".repeat(s.length)}`);

for (const [name, src] of Object.entries(PROGRAMS)) {
  rule(name);
  console.log(
    `  ${"k · sensitivity".padEnd(26)} ${"states".padStart(6)} ${"configs".padStart(7)} ${"iters".padStart(5)} ` +
      `${"objs".padStart(4)} ${"shapes".padStart(6)} ${"ms".padStart(7)}`,
  );
  for (const k of [0, 1, 2]) {
    for (const sensitivity of ["flow-sensitive", "path-sensitive", "flow-insensitive"] as const) {
      const t0 = performance.now();
      const r = analyze(parse(src), { ...kCFA(k), sensitivity: sensitivity as Sensitivity });
      const ms = performance.now() - t0;
      const m = r.metrics;
      const label = `k=${k} · ${sensitivity}`;
      console.log(
        `  ${label.padEnd(26)} ${String(m.reachedStates).padStart(6)} ${String(m.configs).padStart(7)} ` +
          `${String(m.iterations).padStart(5)} ${String(m.storeObjAddrs).padStart(4)} ${String(m.shapesInterned).padStart(6)} ` +
          `${ms.toFixed(1).padStart(7)}`,
      );
    }
  }
}

console.log(
  "\nNote how, for polyvariance, k=2 reaches *fewer* states and iterations than k=0" +
    "\nwhile also being more precise — precision removing spurious states.\n",
);

// --- object-sensitivity vs call-site, head to head -------------------------

rule("object sensitivity vs call-site (method dispatch)");

// `use` calls `.get()` from ONE site on receivers from two allocation sites.
const methodProg = `
  function Box(v) { this.v = v; this.get = function () { return this.v; }; }
  function use(box) { return box.get(); }
  const x = use(new Box(1));
  const y = use(new Box("s"));
  x;`;

const showX = (v: AVal<Loc>) => {
  const bits: string[] = [];
  if (v.nums.top) bits.push("num:⊤");
  else if (!v.nums.items.isEmpty()) bits.push(`{${v.nums.items.toArray().sort((a, b) => a - b).join(",")}}`);
  if (v.strs.top || !v.strs.items.isEmpty()) bits.push("str");
  return bits.join(" ") || "⊥";
};

console.log(methodProg.trim().replace(/^/gm, "  "));
console.log(`\n  ${"k · context".padEnd(20)} ${"x (value of use(Box(1)))".padEnd(26)} ${"states".padStart(6)}`);
for (const k of [1, 2]) {
  for (const context of ["call-site", "object"] as const) {
    const r = analyze(parse(methodProg), { ...kCFA(k), context: context as ContextStrategy });
    const precise = !r.valueOfVar("x") || showX(r.valueOfVar("x") as AVal<Loc>) === "{1}";
    console.log(
      `  ${`k=${k} · ${context}`.padEnd(20)} ${(showX(r.valueOfVar("x") as AVal<Loc>) + (precise ? "  ✓ precise" : "  ✗ imprecise")).padEnd(26)} ${String(r.metrics.reachedStates).padStart(6)}`,
    );
  }
}
console.log(
  "\n  Object sensitivity separates the two receivers at k=1 — call-site needs k=2,\n" +
    "  because it must thread context back through the `use` wrapper.\n",
);
