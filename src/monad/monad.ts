/**
 * The monadic interface the abstract interpreter is written against.
 *
 * This is the heart of the "Monadic Abstract Abstracting Machines" idea: a
 * *single* definitional interpreter is written against an abstract monad `M`
 * that provides (a) sequencing, (b) nondeterministic choice, and (c) a mutable
 * store (`MonadState`). Instantiating `M` at different concrete monads — which
 * differ only in the *order* their nondeterminism and state layers compose —
 * yields analyses of different precision (path- / flow-sensitive /
 * flow-insensitive) from the same interpreter text.
 *
 * ## How we encode this without higher-kinded types
 *
 * TypeScript cannot abstract over a type constructor `M`, so we use a single
 * **opaque** computation type {@link Comp}. The interpreter only ever builds and
 * combines `Comp` values through an {@link AnalysisMonad} dictionary; it never
 * inspects one. Each concrete monad implements {@link AnalysisMonad} by casting
 * its own representation to and from `Comp`. The unsafety is therefore confined
 * to the few lines inside each monad implementation, while the interpreter and
 * all client code stay fully type-checked in terms of `Comp<A>`.
 *
 * `S` is the type of the threaded state — for us always the abstract store.
 */

declare const CompBrand: unique symbol;

/**
 * An opaque monadic computation producing an `A`. Only an {@link AnalysisMonad}
 * knows how to construct, sequence, or run one. Treat it as a black box.
 */
export interface Comp<A> {
  readonly [CompBrand]: A;
}

/**
 * The capability dictionary bundling the monadic operations the interpreter
 * needs. Corresponds to the type-class constraints on the MAAM interpreter:
 * `Monad m`, a nondeterminism class (`MonadPlus`/`MonadBot`), and
 * `MonadState S m` for the store.
 */
export interface AnalysisMonad<S> {
  /** Name of this analysis monad — for reporting which stack produced a result. */
  readonly name: string;

  // --- Monad ---------------------------------------------------------------
  /** `return`/`pure`: inject a pure value. */
  unit<A>(a: A): Comp<A>;
  /** `>>=`: sequence, feeding the result of `m` into `f`. */
  bind<A, B>(m: Comp<A>, f: (a: A) => Comp<B>): Comp<B>;

  // --- Nondeterminism (MonadPlus / MonadBot) -------------------------------
  /** `mzero`/`⊥`: the computation with no results (a dead branch). */
  mzero<A>(): Comp<A>;
  /** `mplus`/`⟨+⟩`: nondeterministic choice between two computations. */
  mplus<A>(a: Comp<A>, b: Comp<A>): Comp<A>;

  // --- State (MonadState S) ------------------------------------------------
  /** `get`: read the current threaded state (store). */
  get(): Comp<S>;
  /** `put`: replace the threaded state (store). */
  put(s: S): Comp<void>;
}

// ---------------------------------------------------------------------------
// Derived operations — defined once, in terms of the primitives above, so
// every concrete monad gets them for free.
// ---------------------------------------------------------------------------

/** `m >> k`: sequence, discarding `m`'s result. */
export function then<S, A, B>(M: AnalysisMonad<S>, m: Comp<A>, k: Comp<B>): Comp<B> {
  return M.bind(m, () => k);
}

/** `fmap`: apply a pure function under the monad. */
export function fmap<S, A, B>(M: AnalysisMonad<S>, m: Comp<A>, f: (a: A) => B): Comp<B> {
  return M.bind(m, (a) => M.unit(f(a)));
}

/** `modify`: read-modify-write the threaded state. */
export function modify<S>(M: AnalysisMonad<S>, f: (s: S) => S): Comp<void> {
  return M.bind(M.get(), (s) => M.put(f(s)));
}

/** `gets`: read a projection of the threaded state. */
export function gets<S, A>(M: AnalysisMonad<S>, f: (s: S) => A): Comp<A> {
  return M.bind(M.get(), (s) => M.unit(f(s)));
}

/** Nondeterministic choice over a finite list of alternatives (`⊥` if empty). */
export function mplusAll<S, A>(M: AnalysisMonad<S>, xs: Iterable<Comp<A>>): Comp<A> {
  let acc: Comp<A> | undefined;
  for (const x of xs) acc = acc === undefined ? x : M.mplus(acc, x);
  return acc ?? M.mzero<A>();
}

/** Nondeterministically yield each element of a finite collection of values. */
export function eachOf<S, A>(M: AnalysisMonad<S>, xs: Iterable<A>): Comp<A> {
  return mplusAll(
    M,
    (function* () {
      for (const x of xs) yield M.unit(x);
    })(),
  );
}

/** Assert a condition; continue with `unit(undefined)` if true, else `mzero`. */
export function guard<S>(M: AnalysisMonad<S>, cond: boolean): Comp<void> {
  return cond ? M.unit(undefined) : M.mzero<void>();
}

/** Kleisli left-to-right sequencing of a list, collecting results into an array. */
export function sequence<S, A>(M: AnalysisMonad<S>, ms: ReadonlyArray<Comp<A>>): Comp<A[]> {
  let acc: Comp<A[]> = M.unit<A[]>([]);
  for (const m of ms) {
    acc = M.bind(acc, (xs) => M.bind(m, (x) => M.unit([...xs, x])));
  }
  return acc;
}

/** Map a monadic function over a list and collect the results. */
export function mapM<S, A, B>(
  M: AnalysisMonad<S>,
  xs: ReadonlyArray<A>,
  f: (a: A) => Comp<B>,
): Comp<B[]> {
  return sequence(
    M,
    xs.map((x) => f(x)),
  );
}
