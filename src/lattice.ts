/**
 * Lattices — the domains abstract interpreters compute over.
 *
 * Transliteration of MAAM's `JoinLattice` / `MeetLattice` / `Lattice` classes.
 * The workhorse for program analysis is the bounded join-semilattice
 * ({@link JoinSemilattice}): a least element `⊥` plus a least-upper-bound
 * operator `⊔`. Analyses "merge" information by joining, and `⊥` is the empty /
 * unreached value.
 */

import type { PartialOrder } from "./order.js";

/**
 * A bounded join-semilattice: a {@link PartialOrder} with a least element
 * `bot` (`⊥`) and a binary least-upper-bound `join` (`⊔`).
 *
 * Laws (assumed, not enforced):
 *  - `join` is associative, commutative, idempotent.
 *  - `bot` is the identity of `join`.
 *  - `lte(a, b) ⟺ join(a, b) == b`  (order agrees with join).
 */
export interface JoinSemilattice<A> extends PartialOrder<A> {
  readonly bot: A;
  readonly join: (a: A, b: A) => A;
  /**
   * Fused join + growth test: `a ⊔ b` together with whether the result is
   * *strictly* above `a`. Fixpoint drivers ask "did the store grow?" after every
   * join; computing it here avoids a second full `lte` traversal. Optional — a
   * driver falls back to `join` then `lte` when absent.
   */
  readonly joinChanged?: (a: A, b: A) => { value: A; changed: boolean };
}

/**
 * A bounded meet-semilattice: greatest element `top` (`⊤`) and greatest-lower-
 * bound `meet` (`⊓`).
 */
export interface MeetSemilattice<A> extends PartialOrder<A> {
  readonly top: A;
  readonly meet: (a: A, b: A) => A;
}

/** A bounded lattice: both a join- and a meet-semilattice. */
export interface Lattice<A> extends JoinSemilattice<A>, MeetSemilattice<A> {}

/** Least upper bound of a finite collection (`⊔` folded over `xs`, `⊥` if empty). */
export function joinAll<A>(J: JoinSemilattice<A>, xs: Iterable<A>): A {
  let acc = J.bot;
  for (const x of xs) acc = J.join(acc, x);
  return acc;
}

/** Greatest lower bound of a finite collection (`⊓` folded over `xs`, `⊤` if empty). */
export function meetAll<A>(M: MeetSemilattice<A>, xs: Iterable<A>): A {
  let acc = M.top;
  for (const x of xs) acc = M.meet(acc, x);
  return acc;
}

/**
 * Iterate `f` from `⊥` to a least fixed point, i.e. the least `x` with
 * `f(x) ⊑ x`. Assumes `f` is monotone and the ascending Kleene chain
 * `⊥ ⊑ f(⊥) ⊑ f(f(⊥)) ⊑ …` stabilises (true for finite-height lattices, which
 * is what widening/finite abstraction buys us).
 *
 * The chain is built with `join` so that even a non-extensive `f` still yields
 * an ascending sequence (`xₙ₊₁ = xₙ ⊔ f(xₙ)`), which is the usual worklist
 * accumulation strategy.
 */
export function lfp<A>(J: JoinSemilattice<A>, f: (x: A) => A, start: A = J.bot): A {
  let x = start;
  for (;;) {
    const next = J.join(x, f(x));
    if (J.lte(next, x)) return x;
    x = next;
  }
}

/**
 * Least fixed point with a safety bound on iterations; throws if the chain does
 * not stabilise within `maxIters`. Handy during development to catch a
 * non-terminating (infinite-height) abstraction rather than hanging.
 */
export function lfpBounded<A>(
  J: JoinSemilattice<A>,
  f: (x: A) => A,
  maxIters: number,
  start: A = J.bot,
): A {
  let x = start;
  for (let i = 0; i < maxIters; i++) {
    const next = J.join(x, f(x));
    if (J.lte(next, x)) return x;
    x = next;
  }
  throw new Error(`lfp did not converge within ${maxIters} iterations`);
}
