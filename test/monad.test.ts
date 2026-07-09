import { test } from "node:test";
import assert from "node:assert/strict";

import { primKey } from "../src/data/key.js";
import { FinSet, powersetLattice } from "../src/data/finset.js";
import { pathSensitiveMonad, flowInsensitiveMonad, type RunnableMonad } from "../src/monad/monads.js";
import { eachOf, guard, mplusAll, type Comp } from "../src/monad/monad.js";

const numK = primKey<number>();
type S = FinSet<number>;
const SL = powersetLattice(numK);
const s = (...xs: number[]) => FinSet.of(numK, ...xs);
const setOf = (fs: S) => fs.toArray().sort((a, b) => a - b);

// Normalize a run to [values[], storeContents[]] for comparison.
function runOut<A>(M: RunnableMonad<S>, m: Comp<A>, s0: S): { vals: A[]; stores: number[][] } {
  const pairs = M.run(m, s0);
  return {
    vals: pairs.map(([a]) => a),
    stores: pairs.map(([, st]) => setOf(st)),
  };
}

for (const [name, M] of [
  ["path-sensitive", pathSensitiveMonad<S>()],
  ["flow-insensitive", flowInsensitiveMonad<S>(SL)],
] as const) {
  test(`${name}: monad left identity  (unit a >>= f ≡ f a)`, () => {
    const f = (x: number) => M.unit(x + 1);
    const lhs = runOut(M, M.bind(M.unit(3), f), s());
    const rhs = runOut(M, f(3), s());
    assert.deepEqual(lhs.vals, rhs.vals);
  });

  test(`${name}: monad right identity  (m >>= unit ≡ m)`, () => {
    const m = M.unit(7);
    const lhs = runOut(M, M.bind(m, (x) => M.unit(x)), s());
    assert.deepEqual(lhs.vals, runOut(M, m, s()).vals);
  });

  test(`${name}: associativity`, () => {
    const m = M.unit(1);
    const f = (x: number) => M.unit(x + 1);
    const g = (x: number) => M.unit(x * 10);
    const lhs = M.bind(M.bind(m, f), g);
    const rhs = M.bind(m, (x) => M.bind(f(x), g));
    assert.deepEqual(runOut(M, lhs, s()).vals, runOut(M, rhs, s()).vals);
  });

  test(`${name}: mzero is a unit for mplus and annihilates`, () => {
    assert.deepEqual(runOut(M, M.mplus(M.unit(1), M.mzero<number>()), s()).vals, [1]);
    assert.deepEqual(runOut(M, M.mzero<number>(), s()).vals, []);
  });

  test(`${name}: eachOf yields every alternative`, () => {
    const m = eachOf(M, [1, 2, 3]);
    assert.deepEqual(runOut(M, m, s()).vals.sort(), [1, 2, 3]);
  });

  test(`${name}: guard prunes`, () => {
    const m = M.bind(guard(M, false), () => M.unit(1));
    assert.deepEqual(runOut(M, m, s()).vals, []);
  });

  test(`${name}: get/put thread state`, () => {
    const m = M.bind(M.put(s(5)), () => M.get());
    const out = runOut(M, m, s());
    assert.deepEqual(out.vals.map(setOf), [[5]]);
  });
}

test("SENSITIVITY: path-sensitive keeps per-branch stores separate", () => {
  const M = pathSensitiveMonad<S>();
  // two branches each write a different store, then read it back
  const branch = (n: number) => M.bind(M.put(s(n)), () => M.get());
  const m = mplusAll(M, [branch(1), branch(2)]);
  const out = runOut(M, m, s());
  // each result carries ITS OWN store — no cross-contamination
  assert.deepEqual(out.vals.map(setOf).sort(), [[1], [2]]);
  assert.deepEqual(out.stores.sort(), [[1], [2]]);
});

test("SENSITIVITY: flow-insensitive joins stores across branches", () => {
  const M = flowInsensitiveMonad<S>(SL);
  const branch = (n: number) => M.bind(M.put(s(n)), () => M.get());
  const m = mplusAll(M, [branch(1), branch(2)]);
  const out = runOut(M, m, s());
  // the two branches SHARE one store, which is the join {1,2}
  for (const st of out.stores) assert.deepEqual(st, [1, 2]);
});
