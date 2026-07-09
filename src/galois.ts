/**
 * Galois connections — the semantic contract that makes an abstraction *sound*.
 *
 * A Galois connection between a concrete poset `C` and an abstract poset `A`
 * is a pair of monotone maps
 *
 *     α : C → A   (abstraction)
 *     γ : A → C   (concretization)
 *
 * satisfying the adjunction  `α(c) ⊑ a  ⟺  c ⊑ γ(a)`. Equivalently the two
 * "round trip" laws hold:
 *
 *     c ⊑ γ(α(c))        (extensive:   abstracting then concretizing loses info)
 *     α(γ(a)) ⊑ a        (reductive:   concretizing then abstracting is tighter)
 *
 * This is the central object of the paper "Galois Transformers and Modular
 * Abstract Interpreters": if every layer of a monad-transformer stack carries a
 * Galois connection, the connections *compose*, and the soundness of the whole
 * abstract interpreter follows from the soundness of each layer — soundness
 * "for free".
 *
 * We cannot check the laws at runtime in general, but the {@link galois} smart
 * constructor documents them and {@link checkExtensive}/{@link checkReductive}
 * spot-check them on finite samples in tests.
 */

import type { PartialOrder } from "./order.js";

/**
 * A Galois connection from concrete domain `C` to abstract domain `A`.
 * Carries the two posets so that the laws can be stated (and spot-checked)
 * against them.
 */
export interface Galois<C, A> {
  readonly concrete: PartialOrder<C>;
  readonly abstract: PartialOrder<A>;
  /** Abstraction `α : C → A`. */
  readonly alpha: (c: C) => A;
  /** Concretization `γ : A → C`. */
  readonly gamma: (a: A) => C;
}

/** Smart constructor; purely documentary but keeps call sites tidy. */
export function galois<C, A>(g: Galois<C, A>): Galois<C, A> {
  return g;
}

/** The identity Galois connection on a poset (`α = γ = id`). */
export function idGalois<A>(order: PartialOrder<A>): Galois<A, A> {
  return { concrete: order, abstract: order, alpha: (x) => x, gamma: (x) => x };
}

/**
 * Compose Galois connections `C ⇄ M` and `M ⇄ A` into `C ⇄ A`. This is the
 * operation that lets soundness propagate through a transformer stack: the
 * outer analysis is just the composite of the per-layer connections.
 */
export function composeGalois<C, M, A>(f: Galois<C, M>, g: Galois<M, A>): Galois<C, A> {
  return {
    concrete: f.concrete,
    abstract: g.abstract,
    alpha: (c) => g.alpha(f.alpha(c)),
    gamma: (a) => f.gamma(g.gamma(a)),
  };
}

/** The dual connection `A ⇄ C` (swap α and γ, swap the posets). */
export function invertGalois<C, A>(g: Galois<C, A>): Galois<A, C> {
  return { concrete: g.abstract, abstract: g.concrete, alpha: g.gamma, gamma: g.alpha };
}

/**
 * Spot-check the extensive law `c ⊑ γ(α(c))` on a finite sample of concrete
 * values. Returns the first counterexample, or `null` if all pass.
 */
export function checkExtensive<C, A>(g: Galois<C, A>, samples: Iterable<C>): C | null {
  for (const c of samples) {
    if (!g.concrete.lte(c, g.gamma(g.alpha(c)))) return c;
  }
  return null;
}

/**
 * Spot-check the reductive law `α(γ(a)) ⊑ a` on a finite sample of abstract
 * values. Returns the first counterexample, or `null` if all pass.
 */
export function checkReductive<C, A>(g: Galois<C, A>, samples: Iterable<A>): A | null {
  for (const a of samples) {
    if (!g.abstract.lte(g.alpha(g.gamma(a)), a)) return a;
  }
  return null;
}
