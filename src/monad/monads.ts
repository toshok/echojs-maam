/**
 * Concrete analysis monads — the "Galois transformer stacks" of the paper,
 * transliterated as explicit representations. Each one implements the same
 * {@link AnalysisMonad} interface, so the single definitional interpreter runs
 * against any of them; they differ only in *how nondeterminism and the store
 * compose*, and that difference is exactly what turns the knob between
 * path-sensitive and flow-insensitive analysis.
 *
 * The two canonical points:
 *
 *  - **Path-sensitive** — `StateT S` sitting *inside* nondeterminism. A
 *    computation is `S → ℘(A × S)`: every nondeterministic result carries *its
 *    own* store. Branches never share store, so the analysis distinguishes
 *    program paths. (Represented here with arrays instead of sets; the driver
 *    dedups.)
 *
 *  - **Flow-insensitive** — nondeterminism sitting *inside* `StateT S`. A
 *    computation is `S → (℘(A) × S)`: a *single* store threads through and is
 *    joined across all branches. Every path reads and writes one shared store.
 *
 * Swapping which layer is on the outside is precisely the paper's claim that
 * the *order* of Galois transformers determines the analysis property.
 */

import type { JoinSemilattice } from "../lattice.js";
import type { AnalysisMonad, Comp } from "./monad.js";

/**
 * A monad whose {@link run} normalizes any computation to a flat list of
 * `(value, store)` outcomes, so drivers can treat every monad uniformly.
 */
export interface RunnableMonad<S> extends AnalysisMonad<S> {
  run<A>(m: Comp<A>, s0: S): Array<readonly [A, S]>;
}

// ===========================================================================
// Path-sensitive:  Comp<A> ≅ (S) => Array<[A, S]>
// ===========================================================================

type PS<S, A> = (s: S) => Array<readonly [A, S]>;

const asPS = <S, A>(f: PS<S, A>): Comp<A> => f as unknown as Comp<A>;
const runPS = <S, A>(m: Comp<A>): PS<S, A> => m as unknown as PS<S, A>;

/**
 * The path-sensitive monad. Nondeterminism is the *outer* layer: each result
 * keeps its own store, so different branches cannot pollute each other. This is
 * the most precise (and most expensive) point on the spectrum.
 */
export function pathSensitiveMonad<S>(): RunnableMonad<S> {
  return {
    name: "path-sensitive (℘(A × Store))",
    unit: <A>(a: A) => asPS<S, A>((s) => [[a, s]]),
    bind: <A, B>(m: Comp<A>, f: (a: A) => Comp<B>) =>
      asPS<S, B>((s) => {
        const out: Array<readonly [B, S]> = [];
        for (const [a, s1] of runPS<S, A>(m)(s)) {
          for (const pair of runPS<S, B>(f(a))(s1)) out.push(pair);
        }
        return out;
      }),
    mzero: <A>() => asPS<S, A>(() => []),
    mplus: <A>(a: Comp<A>, b: Comp<A>) =>
      asPS<S, A>((s) => [...runPS<S, A>(a)(s), ...runPS<S, A>(b)(s)]),
    get: () => asPS<S, S>((s) => [[s, s]]),
    put: (s1: S) => asPS<S, void>(() => [[undefined, s1]]),
    run: <A>(m: Comp<A>, s0: S) => runPS<S, A>(m)(s0),
  };
}

// ===========================================================================
// Flow-insensitive:  Comp<A> ≅ (S) => [Array<A>, S]   (one shared store)
// ===========================================================================

type FI<S, A> = (s: S) => readonly [ReadonlyArray<A>, S];

const asFI = <S, A>(f: FI<S, A>): Comp<A> => f as unknown as Comp<A>;
const runFI = <S, A>(m: Comp<A>): FI<S, A> => m as unknown as FI<S, A>;

/**
 * The flow-insensitive monad. Nondeterminism is the *inner* layer under a
 * single `StateT`: one store threads through the whole computation and is
 * joined (via `SJ`) wherever branches meet. All program points effectively
 * read and write one global store — the least precise, cheapest point.
 */
export function flowInsensitiveMonad<S>(SJ: JoinSemilattice<S>): RunnableMonad<S> {
  return {
    name: "flow-insensitive (℘(A) × Store)",
    unit: <A>(a: A) => asFI<S, A>((s) => [[a], s]),
    bind: <A, B>(m: Comp<A>, f: (a: A) => Comp<B>) =>
      asFI<S, B>((s) => {
        const [as, s1] = runFI<S, A>(m)(s);
        let store = s1;
        const out: B[] = [];
        for (const a of as) {
          const [bs, s2] = runFI<S, B>(f(a))(store);
          out.push(...bs);
          store = SJ.join(store, s2); // accumulate store across branches
        }
        return [out, store];
      }),
    mzero: <A>() => asFI<S, A>((s) => [[], s]),
    mplus: <A>(a: Comp<A>, b: Comp<A>) =>
      asFI<S, A>((s) => {
        const [as, s1] = runFI<S, A>(a)(s);
        const [bs, s2] = runFI<S, A>(b)(s);
        return [[...as, ...bs], SJ.join(s1, s2)]; // branches SHARE (join) their store
      }),
    get: () => asFI<S, S>((s) => [[s], s]),
    put: (s1: S) => asFI<S, void>(() => [[undefined], s1]),
    run: <A>(m: Comp<A>, s0: S) => {
      const [as, s1] = runFI<S, A>(m)(s0);
      return as.map((a) => [a, s1] as const);
    },
  };
}
