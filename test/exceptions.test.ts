import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval, kCFA } from "../src/index.js";
import { normalizeProgram } from "../src/lang/normalize.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

/** All concrete result values a program can yield (a `nondet` yields several). */
function results(src: string): unknown[] {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set].map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t)).sort();
}

// --- Phase D: exceptions ----------------------------------------------------
//
// `try/catch/finally` is modeled as a nondeterministic choice between normal
// completion and the handler. This over-approximates control flow (the handler
// is always treated as reachable) but is sound: a `throw` ends its own path,
// and a caught value is conservatively approximated.

test("try/catch: both the normal and handler paths are explored", () => {
  // The body doesn't actually throw, but the handler is still considered
  // reachable — so BOTH x=1 and x=2 are possible outcomes (sound over-approx).
  assert.deepEqual(results(`let x = 0; try { x = 1; } catch (e) { x = 2; } x;`), [1, 2]);
});

test("throw abandons the rest of the try body; only the handler survives", () => {
  // `x = 5` is dead (unreachable after the throw), so the only outcome is x=9.
  assert.deepEqual(results(`let x = 0; try { throw "boom"; x = 5; } catch (e) { x = 9; } x;`), [9]);
});

test("finally runs on the way out of try and catch", () => {
  assert.deepEqual(results(`let x = 0; try { x = 1; } catch (e) {} finally { x = 7; } x;`), [7]);
});

test("a bare throw aborts the program (no result value)", () => {
  assert.deepEqual(results(`let x = 1; throw x; 42;`), []);
});

test("the caught value is conservatively approximated (undefined)", () => {
  // We do not track thrown values, so the catch binding is treated as unknown.
  assert.deepEqual(results(`let x = 0; try { throw 1; } catch (e) { x = typeof e; } x;`), ["undefined"]);
});

test("try without catch: the finalizer still runs before the rest", () => {
  assert.deepEqual(results(`let x = 0; try { x = 3; } finally { x = x + 1; } x;`), [4]);
});

test("exceptions terminate under abstract interpretation", () => {
  const src = `
    function f(n) {
      try {
        if (n <= 0) throw "done";
        return f(n - 1);
      } catch (e) {
        return 0;
      }
    }
    f(50);`;
  const r = analyze(parse(src), kCFA(1));
  assert.ok(r.collecting.reached.size > 0);
});

// --- Phase D: modules (EchoJS desugars these; handled for robustness) -------

test("export named declaration is analyzed like a plain declaration", () => {
  // `export const` behaves as `const` for the analysis.
  assert.deepEqual(results(`export const a = 2; export const b = 3; a + b;`), [5]);
});

test("export default of an expression is accepted", () => {
  assert.deepEqual(results(`const v = 41; export default v + 1; 7;`), [7]);
});

test("import bindings are accepted (degraded to undefined)", () => {
  // Multi-module linking is future work; imported names read as undefined.
  const src = `import { thing } from "somewhere"; typeof thing;`;
  assert.deepEqual(results(src), ["undefined"]);
});

test("module syntax normalizes without error", () => {
  assert.doesNotThrow(() =>
    normalizeProgram(parse(`import def, { a, b } from "m"; export function f() { return a; } f;`)),
  );
});
