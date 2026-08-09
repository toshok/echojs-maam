/**
 * `FinSet<A>` — a finite set with *structural* membership, backed by a
 * {@link Keyable} dictionary. This is the carrier of the powerset lattice
 * `℘(A)`, which is both the nondeterminism monad and the domain of "a set of
 * possible values" in k-CFA.
 *
 * Instances are immutable; every operation returns a fresh set.
 */

import type { JoinSemilattice } from "../lattice.js";
import type { Keyable } from "./key.js";

export class FinSet<A> implements Iterable<A> {
  /** map from canonical key → element (dedup by structural key). */
  private constructor(
    private readonly K: Keyable<A>,
    private readonly items: ReadonlyMap<string, A>,
  ) {}

  static empty<A>(K: Keyable<A>): FinSet<A> {
    return new FinSet(K, new Map());
  }

  static of<A>(K: Keyable<A>, ...elems: A[]): FinSet<A> {
    return FinSet.fromIterable(K, elems);
  }

  static fromIterable<A>(K: Keyable<A>, elems: Iterable<A>): FinSet<A> {
    const m = new Map<string, A>();
    for (const e of elems) m.set(K.key(e), e);
    return new FinSet(K, m);
  }

  get size(): number {
    return this.items.size;
  }

  isEmpty(): boolean {
    return this.items.size === 0;
  }

  has(a: A): boolean {
    return this.items.has(this.K.key(a));
  }

  add(a: A): FinSet<A> {
    const k = this.K.key(a);
    if (this.items.has(k)) return this;
    const m = new Map(this.items);
    m.set(k, a);
    return new FinSet(this.K, m);
  }

  delete(a: A): FinSet<A> {
    const k = this.K.key(a);
    if (!this.items.has(k)) return this;
    const m = new Map(this.items);
    m.delete(k);
    return new FinSet(this.K, m);
  }

  union(other: FinSet<A>): FinSet<A> {
    if (other === this) return this;
    if (other.isEmpty()) return this;
    if (this.isEmpty()) return other;
    // Reference-preserving: if `other ⊆ this` the union is a no-op — return `this`
    // instead of copying. Near a fixpoint most joins add nothing, so this avoids
    // both the map copy and the allocation (the hottest path in value joins), and
    // lets callers detect "no change" by identity.
    let grew = false;
    for (const k of other.items.keys())
      if (!this.items.has(k)) {
        grew = true;
        break;
      }
    if (!grew) return this;
    const m = new Map(this.items);
    for (const [k, v] of other.items) m.set(k, v);
    return new FinSet(this.K, m);
  }

  intersect(other: FinSet<A>): FinSet<A> {
    const m = new Map<string, A>();
    const [small, big] = this.size <= other.size ? [this, other] : [other, this];
    for (const [k, v] of small.items) if (big.items.has(k)) m.set(k, v);
    return new FinSet(this.K, m);
  }

  difference(other: FinSet<A>): FinSet<A> {
    if (this.isEmpty() || other.isEmpty()) return this;
    const m = new Map(this.items);
    for (const k of other.items.keys()) m.delete(k);
    return new FinSet(this.K, m);
  }

  /** `this ⊆ other` structurally. */
  isSubsetOf(other: FinSet<A>): boolean {
    // identity first: reference-preserving unions return their operand,
    // so near a fixpoint most subset checks compare a set to itself
    if (other === this) return true;
    const mine = this.items;
    const theirs = other.items;
    if (mine.size > theirs.size) return false;
    for (const k of mine.keys()) if (!theirs.has(k)) return false;
    return true;
  }

  /** Monadic bind for the nondeterminism (powerset) monad: flat-map, dedup by `KB`. */
  bind<B>(KB: Keyable<B>, f: (a: A) => FinSet<B>): FinSet<B> {
    const m = new Map<string, B>();
    for (const a of this.items.values()) {
      for (const [k, v] of (f(a) as FinSet<B>).items) m.set(k, v);
    }
    return new FinSet(KB, m);
  }

  map<B>(KB: Keyable<B>, f: (a: A) => B): FinSet<B> {
    const m = new Map<string, B>();
    for (const a of this.items.values()) {
      const b = f(a);
      m.set(KB.key(b), b);
    }
    return new FinSet(KB, m);
  }

  filter(pred: (a: A) => boolean): FinSet<A> {
    const m = new Map<string, A>();
    for (const [k, v] of this.items) if (pred(v)) m.set(k, v);
    return new FinSet(this.K, m);
  }

  /** Pick an arbitrary element, or `undefined` if empty (useful for singletons). */
  choose(): A | undefined {
    for (const v of this.items.values()) return v;
    return undefined;
  }

  toArray(): A[] {
    return [...this.items.values()];
  }

  [Symbol.iterator](): Iterator<A> {
    return this.items.values();
  }

  toString(): string {
    return `{${this.toArray().map((a) => this.K.key(a)).join(", ")}}`;
  }
}

/**
 * The powerset join-semilattice `℘(A)`: `⊥` is the empty set, `⊔` is union,
 * `⊑` is structural subset. This is the domain of nondeterminism.
 */
export function powersetLattice<A>(K: Keyable<A>): JoinSemilattice<FinSet<A>> {
  return {
    bot: FinSet.empty(K),
    join: (a, b) => a.union(b),
    lte: (a, b) => a.isSubsetOf(b),
  };
}
