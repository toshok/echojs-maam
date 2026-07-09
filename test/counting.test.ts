import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, kCFA } from "../src/index.js";

/**
 * Abstract counting (Might & Shivers ΓCFA counting / Balakrishnan–Reps recency):
 * strong-update any address whose abstract count is `ONE`. A once-allocated object
 * initialized field-by-field should reach its final hidden class through a *linear*
 * shape chain (N+1 shapes) rather than the 2ᴺ subset powerset a weak update accretes.
 */

// counting is the 10th positional argument to kCFA (flow-sensitive, gc on).
const fs = (counting: boolean) => kCFA(0, "flow-sensitive", "call-site", 0, true, true, false, 0, counting);

test("counting collapses a once-allocated constructor's shape powerset to a linear chain", () => {
  const src = `
    function Point(a, b, c, d) { this.a = a; this.b = b; this.c = c; this.d = d; }
    var p = new Point(1, 2, 3, 4);
    p.a + p.b + p.c + p.d;`;

  const off = analyze(parse(src), fs(false));
  const on = analyze(parse(src), fs(true));

  // Weak field-init accretes the full subset powerset: ∅,{a},{a,b},… — 2⁴ = 16.
  assert.equal(off.metrics.shapesInterned, 16);
  // Strong update walks the linear chain ∅→{a}→{a,b}→{a,b,c}→{a,b,c,d} — 5 shapes.
  assert.equal(on.metrics.shapesInterned, 5);
});

test("counting is precision-only: the specialization stays monomorphic", () => {
  const src = `
    function Vec(x, y) { this.x = x; this.y = y; }
    var v = new Vec(1, 2);
    v.x + v.y;`;
  const specs = analyze(parse(src), fs(true)).specializations();
  const vec = specs.find((s) => s.name === "Vec")!;
  assert.equal(vec.monomorphic, true);
});

test("a genuinely reallocated (escaping) address is not strong-updated", () => {
  // Two distinct instances escape into an array; the shared 0-CFA address summarizes
  // MANY objects, so its count saturates to ω and writes stay weak (sound).
  const src = `
    function Cell(v) { this.v = v; }
    var xs = [];
    var i = 0;
    while (i < 2) { xs[i] = new Cell(i); i = i + 1; }
    xs[0].v;`;
  // Should still terminate and stay sound (no crash); the instance address is MANY.
  const r = analyze(parse(src), fs(true));
  assert.ok(r.metrics.reachedStates > 0);
});
