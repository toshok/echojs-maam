import { test } from "node:test";
import assert from "node:assert/strict";

import { POrdering, pcompare, discreteOrder } from "../src/order.js";
import { joinAll, lfp, type JoinSemilattice } from "../src/lattice.js";
import { flatLattice, flatKey, flatVal, FlatBot, FlatTop, productLattice } from "../src/lattices.js";
import { primKey } from "../src/data/key.js";
import { FinSet, powersetLattice } from "../src/data/finset.js";
import { FinMap, finMapLattice } from "../src/data/finmap.js";
import { idGalois, composeGalois, checkExtensive, checkReductive, galois } from "../src/galois.js";

const numK = primKey<number>();

test("partial order: pcompare yields NC for incomparable elements", () => {
  const P = discreteOrder<number>();
  assert.equal(pcompare(P, 1, 1), POrdering.EQ);
  assert.equal(pcompare(P, 1, 2), POrdering.NC);
});

test("powerset lattice: bot, join=union, lte=subset", () => {
  const L = powersetLattice(numK);
  assert.ok(L.bot.isEmpty());
  const a = FinSet.of<number>(numK, 1, 2);
  const b = FinSet.of<number>(numK, 2, 3);
  assert.deepEqual(L.join(a, b).toArray().sort(), [1, 2, 3]);
  assert.ok(L.lte(a, L.join(a, b)));
  assert.ok(!L.lte(a, b));
});

test("join laws: commutative, idempotent, bot identity", () => {
  const L = powersetLattice(numK);
  const a = FinSet.of<number>(numK, 1, 2);
  const b = FinSet.of<number>(numK, 3);
  const key = (s: FinSet<number>) => s.toArray().sort().join(",");
  assert.equal(key(L.join(a, b)), key(L.join(b, a)));
  assert.equal(key(L.join(a, a)), key(a));
  assert.equal(key(L.join(a, L.bot)), key(a));
});

test("flat lattice: distinct constants join to top", () => {
  const L = flatLattice(numK);
  assert.equal(L.join(flatVal(1), flatVal(1)).tag, "val");
  assert.equal(L.join(flatVal(1), flatVal(2)).tag, "top");
  assert.equal(L.join(FlatBot, flatVal(5)).tag, "val");
  assert.ok(L.lte(FlatBot, flatVal(5)));
  assert.ok(L.lte(flatVal(5), FlatTop));
  assert.ok(!L.lte(flatVal(1), flatVal(2)));
  // key distinguishes
  const K = flatKey(numK);
  assert.notEqual(K.key(flatVal(1)), K.key(flatVal(2)));
  assert.equal(K.key(FlatTop), K.key(FlatTop));
});

test("finMap pointwise lattice: joinAt is a weak update", () => {
  const VL = powersetLattice(numK);
  const L = finMapLattice(primKey<string>(), VL);
  let m = FinMap.empty<string, FinSet<number>>(primKey<string>());
  m = m.joinAt(VL, "x", FinSet.of<number>(numK, 1));
  m = m.joinAt(VL, "x", FinSet.of<number>(numK, 2)); // accumulates, not overwrite
  assert.deepEqual(m.getOr("x", VL.bot).toArray().sort(), [1, 2]);
  assert.ok(L.lte(FinMap.empty(primKey<string>()), m));
});

test("lfp computes least fixed point (finite height)", () => {
  // grow a set up to {0,1,2,3} then stop
  const L = powersetLattice(numK);
  const f = (s: FinSet<number>): FinSet<number> => {
    let out = s;
    for (const x of s) if (x < 3) out = out.add(x + 1);
    return out.add(0);
  };
  const fix = lfp(L, f);
  assert.deepEqual(fix.toArray().sort(), [0, 1, 2, 3]);
});

test("galois: identity connection satisfies both laws", () => {
  const g = idGalois(discreteOrder<number>());
  assert.equal(checkExtensive(g, [1, 2, 3]), null);
  assert.equal(checkReductive(g, [1, 2, 3]), null);
});

test("galois: powerset abstraction ℘(ℕ) ⇄ Flat is a valid connection and composes", () => {
  // α: a set of numbers ↦ flat (its single element, or ⊤ if many/none→⊥)
  const conc = powersetLattice(numK);
  const abst = flatLattice(numK);
  const g = galois({
    concrete: conc,
    abstract: abst,
    alpha: (s: FinSet<number>) =>
      s.isEmpty() ? FlatBot : s.size === 1 ? flatVal(s.toArray()[0]!) : FlatTop,
    gamma: (f) =>
      f.tag === "bot"
        ? FinSet.empty(numK)
        : f.tag === "val"
          ? FinSet.of<number>(numK, f.value)
          : FinSet.of<number>(numK, -1, 0, 1), // a stand-in for "all" over a finite sample
  });
  const samples = [FinSet.empty(numK), FinSet.of<number>(numK, 0), FinSet.of<number>(numK, 0, 1)];
  assert.equal(checkExtensive(g, samples), null, "c ⊑ γ(α(c))");
  // composition with identity is still a connection
  const g2 = composeGalois(g, idGalois(abst));
  assert.equal(checkExtensive(g2, samples), null);
});

test("product lattice is pointwise", () => {
  const L: JoinSemilattice<readonly [FinSet<number>, FinSet<number>]> = productLattice(
    powersetLattice(numK),
    powersetLattice(numK),
  );
  const a: readonly [FinSet<number>, FinSet<number>] = [FinSet.of<number>(numK, 1), FinSet.of<number>(numK, 9)];
  const b: readonly [FinSet<number>, FinSet<number>] = [FinSet.of<number>(numK, 2), FinSet.of<number>(numK, 9)];
  const j = L.join(a, b);
  assert.deepEqual(j[0].toArray().sort(), [1, 2]);
  assert.deepEqual(j[1].toArray().sort(), [9]);
  assert.ok(L.lte(a, j) && L.lte(b, j));
});

test("joinAll folds over a collection", () => {
  const L = powersetLattice(numK);
  const all = joinAll(L, [FinSet.of<number>(numK, 1), FinSet.of<number>(numK, 2), FinSet.of<number>(numK, 2, 3)]);
  assert.deepEqual(all.toArray().sort(), [1, 2, 3]);
});
