/**
 * Structural keys.
 *
 * Abstract interpretation identifies values structurally: two addresses
 * `(x, t)` are "the same" when their components are equal, not when they are
 * the same JS object. Native `Set`/`Map` key on reference identity, so we route
 * everything through a {@link Keyable} dictionary that renders a value to a
 * canonical `string` key. Equal values must produce equal strings.
 */

/** A dictionary that assigns each `A` a canonical string identity. */
export interface Keyable<A> {
  readonly key: (a: A) => string;
}

/**
 * Memoize a {@link Keyable} per value object.  Canonical keys are pure
 * functions of immutable structural values, but the hot dictionaries
 * (avals, konts, abstract objects) re-render them on every set/map
 * probe — the self-hosted oracle's dominant allocation, hash, and
 * compare load.  The memo keys on object identity (a plain `Map`:
 * object keys hash by identity in both hosts), so the same value
 * object always returns the SAME string instance and downstream map
 * probes hit the pointer-equality fast path.  Primitives pass through
 * unmemoized.  Lifetime: the memo lives exactly as long as the
 * Keyable instance — the factories mint per-analysis instances, and
 * the keyed values are retained by the analysis's own seen-sets
 * anyway, so the memo adds no new retention class.
 */
export function memoKey<A>(K: Keyable<A>): Keyable<A> {
  const memo = new Map<object, string>();
  return {
    key: (a) => {
      if ((typeof a !== "object" || a === null) && typeof a !== "function") return K.key(a);
      const o = a as unknown as object;
      let k = memo.get(o);
      if (k === undefined) {
        k = K.key(a);
        memo.set(o, k);
      }
      return k;
    },
  };
}

/** Key by JSON serialization with sorted object keys (order-independent). */
export function jsonKey<A>(): Keyable<A> {
  return { key: (a) => canonicalJson(a) };
}

/** Key primitives (string/number/boolean/bigint/null) by their string form, tagged by type. */
export function primKey<A extends string | number | boolean | bigint | null>(): Keyable<A> {
  return { key: (a) => `${typeof a}:${String(a)}` };
}

/** Derive a key for a pair from keys for its components. */
export function pairKey<A, B>(ka: Keyable<A>, kb: Keyable<B>): Keyable<readonly [A, B]> {
  return { key: ([a, b]) => `(${ka.key(a)},${kb.key(b)})` };
}

/** Derive a key by first projecting to something already keyable. */
export function contramapKey<A, B>(kb: Keyable<B>, f: (a: A) => B): Keyable<A> {
  return { key: (a) => kb.key(f(a)) };
}

/**
 * A deterministic JSON encoding: object keys are emitted in sorted order so
 * that two structurally-equal objects serialize identically regardless of
 * insertion order. Handles the JSON-hostile cases (`undefined`, `bigint`) that
 * appear in ASTs and values.
 */
export function canonicalJson(value: unknown): string {
  return encode(value);
}

function encode(v: unknown): string {
  if (v === null) return "null";
  if (v === undefined) return "undef";
  switch (typeof v) {
    case "string":
      return JSON.stringify(v);
    case "number":
      return Number.isFinite(v) ? String(v) : `#${String(v)}`; // NaN/±Infinity
    case "boolean":
      return v ? "true" : "false";
    case "bigint":
      return `${v.toString()}n`;
    case "function":
      return `fn:${v.name || "anon"}`;
    case "symbol":
      return `sym:${String(v)}`;
    case "object": {
      if (Array.isArray(v)) return `[${v.map(encode).join(",")}]`;
      const obj = v as Record<string, unknown>;
      const keys = Object.keys(obj).sort();
      return `{${keys.map((k) => `${JSON.stringify(k)}:${encode(obj[k])}`).join(",")}}`;
    }
    default:
      return String(v);
  }
}
