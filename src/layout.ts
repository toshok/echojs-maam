/**
 * Object layout — turning inferred hidden classes into concrete memory layouts.
 *
 * This is the bridge from the analysis to codegen: given the heap the analysis
 * produced, it reports, per allocation site, the **terminal hidden classes** the
 * site's objects settle into and lays each one out as a struct (field offsets +
 * total size) using a caller-supplied size model. A **monomorphic** site (one
 * terminal shape) is a `malloc(sizeof(struct))` + fixed-offset-access candidate;
 * a polymorphic site (several terminal shapes) is where the compiler must pick a
 * tagged union / largest-struct / expando-fallback strategy.
 *
 * "Terminal" filters out the intermediate shapes an object passes through while
 * it is being built (`{}`, `{a}`, …) so only the finished layouts remain —
 * a shape is terminal unless it is a proper prefix of another shape at the site.
 */

import type { Span } from "./lang/ast.js";
import type { Loc } from "./lang/core.js";
import type { Shape, TypeSig } from "./lang/shapes.js";

/** A concrete size model: bytes occupied by a field of a given representation. */
export type SizeOf = (type: TypeSig) => number;

/**
 * A reasonable default 64-bit size model: unboxed number = 8 (f64), pointers
 * (string/object/function) = 8, bool = 1, and any *union* or unknown
 * representation = 16 (a tagged slot: discriminant + payload). Override it to
 * match your ABI.
 */
export const defaultSizeOf: SizeOf = (type) => {
  if (type.includes("|")) return 16; // union ⇒ tagged slot
  switch (type) {
    case "num":
      return 8;
    case "str":
    case "obj":
    case "fn":
      return 8;
    case "bool":
      return 1;
    case "null":
    case "undefined":
      return 8;
    case "never":
      return 0;
    default:
      return 16; // unknown / ⊤ ⇒ tagged
  }
};

/** One field placed in a struct. */
export interface FieldLayout {
  readonly name: string;
  readonly type: TypeSig;
  readonly sizeBytes: number;
  readonly offsetBytes: number;
}

/** A struct layout for one hidden class. */
export interface StructLayout {
  readonly shape: Shape;
  readonly fields: ReadonlyArray<FieldLayout>;
  /** Total size, padded to the struct's maximum field alignment. */
  readonly sizeBytes: number;
}

/** Everything known about the objects allocated at one site. */
export interface SiteLayout {
  /** The allocation-site location (the object-literal core node). */
  readonly site: Loc;
  /** Source span of the site, if the tree carried ranges. */
  readonly span?: Span;
  /** The terminal (finished) hidden classes objects here settle into. */
  readonly shapes: ReadonlyArray<Shape>;
  /** True when there is exactly one terminal class — a `malloc`-able struct. */
  readonly monomorphic: boolean;
  /** A struct layout per terminal class (offsets computed with `sizeOf`). */
  readonly layouts: ReadonlyArray<StructLayout>;
}

function align(cursor: number, alignment: number): number {
  return alignment <= 1 ? cursor : Math.ceil(cursor / alignment) * alignment;
}

/** Lay out a single shape as a struct: natural alignment, declaration order. */
export function structOf(shape: Shape, sizeOf: SizeOf = defaultSizeOf): StructLayout {
  let cursor = 0;
  let maxAlign = 1;
  const fields: FieldLayout[] = shape.fields.map((f) => {
    const sizeBytes = sizeOf(f.type);
    const a = sizeBytes >= 8 ? 8 : Math.max(1, sizeBytes);
    maxAlign = Math.max(maxAlign, a);
    const offsetBytes = align(cursor, a);
    cursor = offsetBytes + sizeBytes;
    return { name: f.name, type: f.type, sizeBytes, offsetBytes };
  });
  return { shape, fields, sizeBytes: align(cursor, maxAlign) };
}

/**
 * Does `small` merge into `big` — i.e. is every field of `small` present in `big`
 * with the *same* representation, and `big` strictly larger? Such a `small` is a
 * construction intermediate (or a compatible subset) that the superset struct
 * `big` already covers, so it is not a distinct terminal layout.
 *
 * Crucially this is by *field set*, not prefix order, so out-of-order intermediate
 * shapes left behind by weak updates (e.g. a stale `{y}` beside `{x, y}`) are
 * absorbed — while genuinely incompatible classes (`{a}` vs `{b}`, or a field whose
 * representation differs like `{v: num}` vs `{v: str}`) stay distinct and surface.
 */
function subsumedBy(small: Shape, big: Shape): boolean {
  if (small.fields.length >= big.fields.length) return false;
  const bigTypes = new Map(big.fields.map((f) => [f.name, f.type]));
  for (const f of small.fields) {
    if (bigTypes.get(f.name) !== f.type) return false;
  }
  return true;
}

/** The terminal hidden classes — those not merge-subsumed by a larger compatible one. */
export function terminalShapes(shapes: ReadonlyArray<Shape>): Shape[] {
  const byId = new Map<number, Shape>();
  for (const s of shapes) byId.set(s.id, s);
  const all = [...byId.values()];
  return all.filter((s) => !all.some((t) => t.id !== s.id && subsumedBy(s, t)));
}

/** The shapes an object may have, keyed by anything with a `.shapes` iterable. */
export interface HasShapes {
  readonly shapes: Iterable<Shape>;
}

/**
 * Group heap objects by allocation site and compute a {@link SiteLayout} for each.
 * `objs` is any iterable of `(address, object)` where the address has a `.loc`
 * (the allocation site) and the object exposes `.shapes`.
 */
export function computeSiteLayouts(
  objs: Iterable<readonly [{ loc: Loc }, HasShapes]>,
  sizeOf: SizeOf = defaultSizeOf,
  siteSpans?: ReadonlyMap<Loc, Span>,
): SiteLayout[] {
  const bySite = new Map<Loc, Shape[]>();
  for (const [addr, obj] of objs) {
    const acc = bySite.get(addr.loc) ?? [];
    for (const s of obj.shapes) acc.push(s);
    bySite.set(addr.loc, acc);
  }
  const out: SiteLayout[] = [];
  for (const [site, shapes] of bySite) {
    const terminals = terminalShapes(shapes);
    const span = siteSpans?.get(site);
    out.push({
      site,
      ...(span ? { span } : {}),
      shapes: terminals,
      monomorphic: terminals.length === 1,
      layouts: terminals.map((s) => structOf(s, sizeOf)),
    });
  }
  out.sort((a, b) => a.site - b.site);
  return out;
}

/** Pretty-print a struct layout, C-ish. */
export function structToString(s: StructLayout): string {
  const fields = s.fields
    .map((f) => `  +${String(f.offsetBytes).padStart(2)}  ${f.type.padEnd(10)} ${f.name}`)
    .join("\n");
  return `struct (${s.sizeBytes} bytes) {\n${fields}\n}`;
}
