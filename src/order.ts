/**
 * Partial orders.
 *
 * Transliteration of MAAM's `PartialOrder` class. Because TypeScript has no
 * type classes, a "class instance" is an explicit dictionary value that we
 * pass around by hand (dictionary-passing style — exactly how a Haskell
 * compiler desugars type classes). Every algebraic structure in this library
 * follows the same convention: an `interface Foo<A>` describes the operations,
 * and values of that interface are the instances.
 */

/**
 * The result of comparing two elements of a partially ordered set. Unlike a
 * total order there is a fourth case, {@link POrdering.NC} ("not comparable"),
 * for elements that are incomparable (neither `a ⊑ b` nor `b ⊑ a`).
 */
export enum POrdering {
  LT = "LT",
  EQ = "EQ",
  GT = "GT",
  NC = "NC",
}

/**
 * A partial order on `A`. The single primitive operation is `lte` (`⊑`,
 * "less than or equal to" / "approximates"). In abstract interpretation
 * `a ⊑ b` reads as "`a` is at least as precise as `b`" — `b` over-approximates
 * `a`.
 */
export interface PartialOrder<A> {
  /** `a ⊑ b`: does `a` approximate-below `b`? */
  readonly lte: (a: A, b: A) => boolean;
}

/** `a ⊒ b` — the dual of {@link PartialOrder.lte}. */
export function gte<A>(P: PartialOrder<A>, a: A, b: A): boolean {
  return P.lte(b, a);
}

/** Poset equality: `a ⊑ b` and `b ⊑ a`. */
export function poEq<A>(P: PartialOrder<A>, a: A, b: A): boolean {
  return P.lte(a, b) && P.lte(b, a);
}

/** Strictly below: `a ⊑ b` but not `b ⊑ a`. */
export function poLt<A>(P: PartialOrder<A>, a: A, b: A): boolean {
  return P.lte(a, b) && !P.lte(b, a);
}

/** Full {@link POrdering} comparison derived from `lte`. */
export function pcompare<A>(P: PartialOrder<A>, a: A, b: A): POrdering {
  const le = P.lte(a, b);
  const ge = P.lte(b, a);
  if (le && ge) return POrdering.EQ;
  if (le) return POrdering.LT;
  if (ge) return POrdering.GT;
  return POrdering.NC;
}

/**
 * Build a {@link PartialOrder} from a JS equality-comparable "discrete" order:
 * distinct elements are incomparable and each element approximates only itself.
 * Useful for flat domains (variable names, primitive constants, ...).
 */
export function discreteOrder<A>(eq: (a: A, b: A) => boolean = Object.is): PartialOrder<A> {
  return { lte: (a, b) => eq(a, b) };
}

/** The partial order on the dual poset (`⊑` reversed). */
export function dualOrder<A>(P: PartialOrder<A>): PartialOrder<A> {
  return { lte: (a, b) => P.lte(b, a) };
}
