/**
 * Execution drivers — the `μX. X ⊔ ς₀ ⊔ γ(step)(X)` least-fixed-point that turns
 * a monadic `step : C → Comp<C>` into a terminating whole-program analysis.
 *
 * The paper packages this as `mstepγ : (a → m b) → (ς a → ς b)` plus `poiter`
 * (iterate-to-fixpoint). Here it is three concrete drivers, one per collecting
 * state-space shape (§7). The *same* `step` runs under all three; which driver
 * (paired with which monad) you choose is what selects path- / flow- /
 * flow-insensitive precision.
 *
 * `C` is the control state (everything except the store); `S` is the store.
 */

import { FinSet } from "./data/finset.js";
import type { Keyable } from "./data/key.js";
import { pairKey } from "./data/key.js";
import type { JoinSemilattice } from "./lattice.js";
import type { Comp } from "./monad/monad.js";
import type { RunnableMonad } from "./monad/monads.js";

/** The step relation: a control state maps, in the monad, to its successors. */
export type Step<C, S> = (c: C) => Comp<C>;

/** A normalized view of the reached state-space, uniform across all drivers. */
export interface Collecting<C, S> {
  /** Which driver/monad produced this (for reporting). */
  readonly strategy: string;
  /** Every control state reached (deduped structurally). */
  readonly reached: FinSet<C>;
  /** `(control, store)` configurations reached. */
  readonly configs: FinSet<readonly [C, S]>;
  /** The join of every store encountered — a single global summary. */
  readonly store: S;
  /** How many worklist steps (individual control-state transfers) it took. */
  readonly iterations: number;
}

/**
 * **Path-sensitive** driver. Explores `(control, store)` configurations, each
 * branch keeping its own store — the `℘(Exp × Store)` relation. Pair with
 * `pathSensitiveMonad`. Most precise, largest state space.
 */
export function exploreConfigs<C, S>(
  M: RunnableMonad<S>,
  CK: Keyable<C>,
  SK: Keyable<S>,
  SJ: JoinSemilattice<S>,
  step: Step<C, S>,
  c0: C,
  s0: S,
): Collecting<C, S> {
  const configKey = pairKey(CK, SK);
  let seen = FinSet.of<readonly [C, S]>(configKey, [c0, s0]);
  let frontier: Array<readonly [C, S]> = [[c0, s0]];
  let iterations = 0;

  while (frontier.length > 0) {
    iterations++;
    const next: Array<readonly [C, S]> = [];
    for (const [c, s] of frontier) {
      for (const [c1, s1] of M.run(step(c), s)) {
        const cfg: readonly [C, S] = [c1, s1];
        if (!seen.has(cfg)) {
          seen = seen.add(cfg);
          next.push(cfg);
        }
      }
    }
    frontier = next;
  }

  return {
    strategy: `path-sensitive · ${M.name}`,
    reached: dedupControls(CK, seen),
    configs: seen,
    store: joinStores(SJ, seen),
    iterations,
  };
}

/**
 * **Flow-sensitive** driver. Reuses the path-sensitive monad but widens the
 * collecting set: all configurations sharing a control state have their stores
 * joined, giving `[(Exp × Ψ) ↦ Store]` — one store per control point. This is
 * the code's realization of the paper's `Ft` transformer.
 */
export function exploreFlowSensitive<C, S>(
  M: RunnableMonad<S>,
  CK: Keyable<C>,
  SK: Keyable<S>,
  SJ: JoinSemilattice<S>,
  step: Step<C, S>,
  c0: C,
  s0: S,
  /** Optional abstract GC: restrict a successor's store to what its control state can reach. */
  gc?: (c: C, s: S) => S,
): Collecting<C, S> {
  // Per-control-point store: control-key → [control, joined store].
  const store = new Map<string, readonly [C, S]>();
  const merge = (c: C, s: S): boolean => {
    const k = CK.key(c);
    const prev = store.get(k);
    if (!prev) {
      store.set(k, [c, s]);
      return true;
    }
    if (SJ.joinChanged) {
      const r = SJ.joinChanged(prev[1], s);
      if (!r.changed) return false;
      store.set(k, [c, r.value]);
      return true;
    }
    const joined = SJ.join(prev[1], s);
    if (SJ.lte(joined, prev[1])) return false;
    store.set(k, [c, joined]);
    return true;
  };

  const worklist: C[] = [];
  const queued = new Set<string>();
  const enqueue = (c: C): void => {
    const k = CK.key(c);
    if (!queued.has(k)) {
      queued.add(k);
      worklist.push(c);
    }
  };

  merge(c0, s0);
  enqueue(c0);
  let iterations = 0;
  while (worklist.length > 0) {
    const c = worklist.pop()!;
    queued.delete(CK.key(c));
    iterations++;
    const s = store.get(CK.key(c))![1];
    for (const [c1, s1] of M.run(step(c), s)) {
      if (merge(c1, gc ? gc(c1, s1) : s1)) enqueue(c1);
    }
  }

  const configs = FinSet.fromIterable(pairKey(CK, SK), store.values());
  return {
    strategy: `flow-sensitive · ${M.name}`,
    reached: dedupControls(CK, configs),
    configs,
    store: joinStores(SJ, configs),
    iterations,
  };
}

/**
 * **Flow-insensitive** driver. Maintains a *single* global store, shared and
 * joined across every reachable control state — `℘(Exp × Ψ) × Store`. Pair with
 * `flowInsensitiveMonad`. Cheapest, least precise.
 */
export function exploreGlobal<C, S>(
  M: RunnableMonad<S>,
  CK: Keyable<C>,
  SK: Keyable<S>,
  SJ: JoinSemilattice<S>,
  step: Step<C, S>,
  c0: C,
  s0: S,
): Collecting<C, S> {
  let reached = FinSet.of<C>(CK, c0);
  let store = s0;

  // Worklist fixpoint. With a *single global* store every transfer reads the
  // whole store, so a store growth can invalidate any reached state — but we
  // only pay that when the store actually grows. The inner loop drains newly
  // discovered control states (pure BFS, no re-stepping); each time it empties
  // we re-seed the whole reached set *iff* the store grew during that sweep, and
  // stop at the first sweep that neither discovers a state nor grows the store.
  // This never does more work than the round-based version and skips the sweeps
  // that only added states without changing the store.
  const worklist: C[] = [c0];
  const queued = new Set<string>([CK.key(c0)]);
  const enqueue = (c: C): void => {
    const k = CK.key(c);
    if (!queued.has(k)) {
      queued.add(k);
      worklist.push(c);
    }
  };

  let iterations = 0;
  let storeGrew = false;
  for (;;) {
    while (worklist.length > 0) {
      const c = worklist.pop()!;
      queued.delete(CK.key(c));
      iterations++;
      for (const [c1, s1] of M.run(step(c), store)) {
        if (!reached.has(c1)) {
          reached = reached.add(c1);
          enqueue(c1);
        }
        // Fused join+growth-test when the lattice offers it (avoids a second full
        // `lte` traversal of the store per successor); else fall back.
        if (SJ.joinChanged) {
          const r = SJ.joinChanged(store, s1);
          if (r.changed) {
            store = r.value;
            storeGrew = true;
          }
        } else {
          const joined = SJ.join(store, s1);
          if (!SJ.lte(joined, store)) {
            store = joined;
            storeGrew = true;
          }
        }
      }
    }
    if (!storeGrew) break; // fixpoint: a full drain with no store growth
    storeGrew = false;
    for (const rc of reached) enqueue(rc); // store changed ⇒ re-examine everyone
  }

  const configs = reached.map(pairKey(CK, SK), (c) => [c, store] as const);
  return {
    strategy: `flow-insensitive · ${M.name}`,
    reached,
    configs,
    store,
    iterations,
  };
}

// --- helpers ---------------------------------------------------------------

function dedupControls<C, S>(CK: Keyable<C>, configs: FinSet<readonly [C, S]>): FinSet<C> {
  return FinSet.fromIterable(
    CK,
    (function* () {
      for (const [c] of configs) yield c;
    })(),
  );
}

function joinStores<C, S>(SJ: JoinSemilattice<S>, configs: FinSet<readonly [C, S]>): S {
  let acc = SJ.bot;
  for (const [, s] of configs) acc = SJ.join(acc, s);
  return acc;
}
