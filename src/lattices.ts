/**
 * Concrete lattice constructions: flat (constant-propagation) lattices,
 * products, and the two-point boolean lattice. These are the building blocks
 * from which the abstract value domains of the example language are assembled.
 */

import type { JoinSemilattice } from "./lattice.js";
import type { PartialOrder } from "./order.js";
import type { Keyable } from "./data/key.js";

/**
 * A flat lattice over a base set `A` (constant propagation):
 *
 *          ⊤            (Top — "any value / don't know")
 *        / | \
 *      a₁  a₂ a₃ …      (the base elements, pairwise incomparable)
 *        \ | /
 *          ⊥            (Bot — "no value / unreached")
 *
 * Joining two *different* base elements jumps to `⊤`; joining equal elements is
 * a no-op. This is exactly the domain you want to answer "is this variable
 * always the same constant?".
 */
export type Flat<A> =
  | { readonly tag: "bot" }
  | { readonly tag: "val"; readonly value: A }
  | { readonly tag: "top" };

export const FlatBot: Flat<never> = { tag: "bot" };
export const FlatTop: Flat<never> = { tag: "top" };
export function flatVal<A>(value: A): Flat<A> {
  return { tag: "val", value };
}

/** Build the flat join-semilattice, using `K` to decide base-element equality. */
export function flatLattice<A>(K: Keyable<A>): JoinSemilattice<Flat<A>> {
  const eq = (a: A, b: A) => K.key(a) === K.key(b);
  return {
    bot: FlatBot,
    join: (x, y) => {
      if (x.tag === "bot") return y;
      if (y.tag === "bot") return x;
      if (x.tag === "top" || y.tag === "top") return FlatTop;
      // both are "val"
      return eq(x.value, y.value) ? x : FlatTop;
    },
    lte: (x, y) => {
      if (x.tag === "bot") return true;
      if (y.tag === "top") return true;
      if (x.tag === "top") return false; // y is not top here
      if (y.tag === "bot") return false; // x is not bot here
      return eq(x.value, y.value); // both val
    },
  };
}

/** {@link Keyable} for a {@link Flat} value, given a key for the base set. */
export function flatKey<A>(K: Keyable<A>): Keyable<Flat<A>> {
  return {
    key: (f) => (f.tag === "val" ? `v:${K.key(f.value)}` : f.tag),
  };
}

/**
 * The product join-semilattice `A × B` with the pointwise order and componentwise
 * join. `⊥ = (⊥ₐ, ⊥_b)`.
 */
export function productLattice<A, B>(
  JA: JoinSemilattice<A>,
  JB: JoinSemilattice<B>,
): JoinSemilattice<readonly [A, B]> {
  return {
    bot: [JA.bot, JB.bot],
    join: ([a1, b1], [a2, b2]) => [JA.join(a1, a2), JB.join(b1, b2)],
    lte: ([a1, b1], [a2, b2]) => JA.lte(a1, a2) && JB.lte(b1, b2),
  };
}

/** Partial order on a product from the component orders (pointwise). */
export function productOrder<A, B>(
  PA: PartialOrder<A>,
  PB: PartialOrder<B>,
): PartialOrder<readonly [A, B]> {
  return { lte: ([a1, b1], [a2, b2]) => PA.lte(a1, a2) && PB.lte(b1, b2) };
}

/**
 * The two-point boolean lattice `false ⊑ true` — a plain lattice ordered by
 * implication. Occasionally handy for "reached?" flags.
 */
export const boolLattice: JoinSemilattice<boolean> = {
  bot: false,
  join: (a, b) => a || b,
  lte: (a, b) => !a || b,
};

/**
 * Lift any set with decidable equality into a flat lattice value directly from
 * a base value (`⊥ ⊑ base ⊑ ⊤`), the common way abstract primitives are made.
 */
export function liftFlat<A>(a: A): Flat<A> {
  return flatVal(a);
}
