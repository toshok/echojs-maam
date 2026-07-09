/**
 * `FinMap<K, V>` — a finite map with *structural* keys, backed by a
 * {@link Keyable} dictionary. Stores (`Addr → Value`) and environments
 * (`Var → Addr`) are `FinMap`s.
 *
 * When `V` is itself a join-semilattice, `FinMap<K, V>` is the *pointwise*
 * join-semilattice used for abstract stores: an absent key denotes `⊥`, join
 * is key-wise join, and `joinAt` performs the crucial "weak update" that merges
 * a new value into an address rather than overwriting it.
 *
 * (A persistent HAMT backing was tried to share structure across the many stores
 * a flow-sensitive analysis keeps; it measured *slower* — abstract GC already
 * trims each store to its live footprint, so neighbouring stores overlap little,
 * and a JS trie loses to the native `Map` on the small maps that remain. So the
 * backing stays a copy-on-write `Map`, with the values shared by reference.)
 */

import type { JoinSemilattice } from "../lattice.js";
import type { Keyable } from "./key.js";

export class FinMap<K, V> implements Iterable<readonly [K, V]> {
  private constructor(
    private readonly KK: Keyable<K>,
    /** canonical key → [originalKey, value]. */
    private readonly entries_: ReadonlyMap<string, readonly [K, V]>,
  ) {}

  static empty<K, V>(KK: Keyable<K>): FinMap<K, V> {
    return new FinMap(KK, new Map());
  }

  static fromEntries<K, V>(KK: Keyable<K>, entries: Iterable<readonly [K, V]>): FinMap<K, V> {
    const m = new Map<string, readonly [K, V]>();
    for (const [k, v] of entries) m.set(KK.key(k), [k, v]);
    return new FinMap(KK, m);
  }

  get size(): number {
    return this.entries_.size;
  }

  isEmpty(): boolean {
    return this.entries_.size === 0;
  }

  has(k: K): boolean {
    return this.entries_.has(this.KK.key(k));
  }

  /** Lookup; returns `undefined` when absent. */
  get(k: K): V | undefined {
    return this.entries_.get(this.KK.key(k))?.[1];
  }

  /** Lookup with a default supplied for the absent case (e.g. `⊥`). */
  getOr(k: K, dflt: V): V {
    const e = this.entries_.get(this.KK.key(k));
    return e ? e[1] : dflt;
  }

  /** Strong update: set `k ↦ v`, replacing any prior binding. */
  set(k: K, v: V): FinMap<K, V> {
    const m = new Map(this.entries_);
    m.set(this.KK.key(k), [k, v]);
    return new FinMap(this.KK, m);
  }

  delete(k: K): FinMap<K, V> {
    const kk = this.KK.key(k);
    if (!this.entries_.has(kk)) return this;
    const m = new Map(this.entries_);
    m.delete(kk);
    return new FinMap(this.KK, m);
  }

  /**
   * Weak update: `k ↦ (old ⊔ v)` using the value lattice `VJ`. This is the
   * fundamental store operation of a store-widened abstract interpreter —
   * writing an address *accumulates* possible values rather than clobbering,
   * which is what makes finitely-many addresses sound for infinitely-many
   * concrete allocations.
   */
  joinAt(VJ: JoinSemilattice<V>, k: K, v: V): FinMap<K, V> {
    const kk = this.KK.key(k);
    const existing = this.entries_.get(kk);
    const merged = existing ? VJ.join(existing[1], v) : v;
    const m = new Map(this.entries_);
    m.set(kk, [k, merged]);
    return new FinMap(this.KK, m);
  }

  /**
   * Pointwise join with `other` in a **single** pass and a **single** copy —
   * O(|this| + |other|). The naive `for (k,v of other) acc = acc.joinAt(k,v)`
   * copies the whole backing map once *per entry* (O(n²) allocation); this copies
   * it once and merges in place. This is the hot path of every store join.
   */
  mergeJoin(VJ: JoinSemilattice<V>, other: FinMap<K, V>): FinMap<K, V> {
    if (other.entries_.size === 0) return this;
    if (this.entries_.size === 0) return other;
    const m = new Map(this.entries_);
    for (const [kk, e] of other.entries_) {
      const existing = m.get(kk);
      m.set(kk, existing ? [existing[0], VJ.join(existing[1], e[1])] : e);
    }
    return new FinMap(this.KK, m);
  }

  /**
   * Like {@link mergeJoin}, but also reports whether the result grew strictly
   * above `this` — a key only in `other`, or an overlapping key whose value is not
   * already `⊑` ours. Lets the driver skip the separate `lte` traversal.
   */
  mergeJoinChanged(VJ: JoinSemilattice<V>, other: FinMap<K, V>): { map: FinMap<K, V>; changed: boolean } {
    if (other.entries_.size === 0) return { map: this, changed: false };
    if (this.entries_.size === 0) return { map: other, changed: true };
    const m = new Map(this.entries_);
    let changed = false;
    for (const [kk, e] of other.entries_) {
      const existing = m.get(kk);
      if (!existing) {
        m.set(kk, e);
        changed = true;
      } else if (!VJ.lte(e[1], existing[1])) {
        m.set(kk, [existing[0], VJ.join(existing[1], e[1])]);
        changed = true;
      }
    }
    return changed ? { map: new FinMap(this.KK, m), changed } : { map: this, changed };
  }

  /**
   * Keep only entries whose (original) key is in `keep`. Used to trim a closure's
   * captured environment to the lambda's free variables. Reference-preserving when
   * nothing is dropped.
   */
  restrict(keep: ReadonlySet<K>): FinMap<K, V> {
    let dropped = false;
    const m = new Map<string, readonly [K, V]>();
    for (const [kk, e] of this.entries_) {
      if (keep.has(e[0])) m.set(kk, e);
      else dropped = true;
    }
    return dropped ? new FinMap(this.KK, m) : this;
  }

  /**
   * Keep only entries whose *canonical key string* is in `keep` — the restriction
   * abstract GC applies to a store. Reference-preserving when nothing is dropped.
   */
  filterKeys(keep: ReadonlySet<string>): FinMap<K, V> {
    if (this.entries_.size === 0) return this;
    let dropped = false;
    const m = new Map<string, readonly [K, V]>();
    for (const [kk, e] of this.entries_) {
      if (keep.has(kk)) m.set(kk, e);
      else dropped = true;
    }
    return dropped ? new FinMap(this.KK, m) : this;
  }

  map<W>(f: (v: V, k: K) => W): FinMap<K, W> {
    const m = new Map<string, readonly [K, W]>();
    for (const [kk, [k, v]] of this.entries_) m.set(kk, [k, f(v, k)]);
    return new FinMap(this.KK, m);
  }

  keys(): K[] {
    return [...this.entries_.values()].map(([k]) => k);
  }

  values(): V[] {
    return [...this.entries_.values()].map(([, v]) => v);
  }

  [Symbol.iterator](): Iterator<readonly [K, V]> {
    return this.entries_.values();
  }

  toString(): string {
    return `{${[...this.entries_.values()]
      .map(([k, v]) => `${this.KK.key(k)} ↦ ${String(v)}`)
      .join(", ")}}`;
  }
}

/**
 * The pointwise join-semilattice of finite maps into a value lattice `VJ`.
 * `⊥` is the empty map; `join` unions keys and joins colliding values; `lte`
 * is the pointwise order (every key of `a` is `⊑` the corresponding value of
 * `b`, treating absent as `⊥`).
 */
export function finMapLattice<K, V>(
  KK: Keyable<K>,
  VJ: JoinSemilattice<V>,
): JoinSemilattice<FinMap<K, V>> {
  return {
    bot: FinMap.empty(KK),
    join: (a, b) => a.mergeJoin(VJ, b),
    joinChanged: (a, b) => {
      const r = a.mergeJoinChanged(VJ, b);
      return { value: r.map, changed: r.changed };
    },
    lte: (a, b) => {
      for (const [k, va] of a) {
        const vb = b.getOr(k, VJ.bot);
        if (!VJ.lte(va, vb)) return false;
      }
      return true;
    },
  };
}
