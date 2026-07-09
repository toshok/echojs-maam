/**
 * Hidden classes (a.k.a. shapes / maps, in the V8 sense) — **type-aware**.
 *
 * A {@link Shape} describes the *structure* of an object: a set of properties,
 * each with a **representation** (its abstract type). Unlike a runtime engine —
 * which can start with structural-only maps and re-specialize field
 * representations later via a JIT (deprecate/migrate) — an ahead-of-time
 * optimizing compiler has no second chance, so the representation must be part of
 * the class identity from the start. Consequently `{x: number}` and
 * `{x: string}` are *different* hidden classes here, and type polymorphism at a
 * site shows up as multiple shapes in an object's shape set.
 *
 * Interning is **order-INSENSITIVE**: a discovered class is a *set* of typed
 * fields, so shapes are hash-consed by their fields sorted by name — `{x, y}` and
 * `{y, x}` are the *same* class. A V8 map keeps insertion order (its property
 * offsets are baked into inline caches), but an AOT compiler chooses its own
 * layout for a statically-known class, so it gains nothing from tracking order and
 * loses a great deal: without this, an object built up field-by-field (e.g. a
 * prototype whose N methods are assigned in a fixpoint-explored interleaving)
 * interns all N! orderings — the splay benchmark went from 109,603 shapes to 258.
 * Each `Shape` still stores its fields in canonical (sorted) order so every class
 * has a deterministic struct layout. Adding a property, or changing a field's
 * representation, **transitions** to a new shape; the reachable graph is finite
 * (finitely many names × a finite set of type tags), keeping it terminating.
 */

import type { Keyable } from "../data/key.js";

/** A property name. Computed/dynamic keys are not modeled (see `normalize.ts`). */
export type PropName = string;

/**
 * A field's representation — a canonical rendering of its abstract type, e.g.
 * `"num"`, `"str"`, `"num|str"` (a field that may hold either), `"obj"`, or
 * `"⊤"`. Produced by a value domain's `typeSig`. Two shapes differ if any field's
 * `type` differs, even when the property names match.
 */
export type TypeSig = string;

/** One typed slot of a hidden class. */
export interface Field {
  readonly name: PropName;
  readonly type: TypeSig;
}

/** An interned, type-aware hidden class with a stable id. */
export interface Shape {
  readonly id: number;
  readonly fields: readonly Field[];
  /**
   * `⊤`: a **megamorphic** class — "structure unknown, may have any field". An
   * object's shape set widens to this once it exceeds the per-address cap (see
   * {@link ShapeTable.cap}), bounding the powerset blowup a field-by-field built
   * object (e.g. a prototype accruing N methods → 2ᴺ subsets) would otherwise
   * cause. The object's *field map* stays precise, so property reads are unaffected;
   * only the set-of-hidden-classes is over-approximated (no fixed struct layout).
   */
  readonly megamorphic?: boolean;
}

/** Is `s` the megamorphic `⊤` shape? */
export function isMegamorphic(s: Shape): boolean {
  return s.megamorphic === true;
}

/** Structure+representation key for an already-canonicalized (sorted) field list. */
function shapeStructureKey(fields: readonly Field[]): string {
  return fields.map((f) => `${JSON.stringify(f.name)}:${f.type}`).join(",");
}

/** Sort fields by name — the canonical order in which a discovered class is stored. */
function canonicalize(fields: readonly Field[]): Field[] {
  return [...fields].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}

/**
 * The global, monotonically-growing shape graph. Interns shapes by
 * structure+representation and memoizes transitions. One table per analysis run
 * (created in `makeMachine`) and shared; growing it never affects soundness — it
 * is just hash-consing.
 */
export class ShapeTable {
  private readonly byStructure = new Map<string, Shape>();
  private nextId = 0;
  /** memoized transition edges: `${fromId}|name:type` → toShape */
  private readonly edges = new Map<string, Shape>();
  private readonly emptyShape: Shape;
  private readonly topShape: Shape;

  constructor() {
    this.emptyShape = this.intern([]);
    this.topShape = { id: this.nextId++, fields: [], megamorphic: true };
  }

  /** The megamorphic `⊤` class — "may have any field" (see {@link Shape.megamorphic}). */
  top(): Shape {
    return this.topShape;
  }

  /**
   * Widen a shape set to at most `cap` distinct classes: if it exceeds `cap`,
   * collapse the whole set to `{⊤}`. Sound (⊤ over-approximates every shape) and
   * idempotent, so an address that goes megamorphic stays there — bounding
   * shapes-per-address and killing the field-subset powerset blowup.
   */
  capShapeSet(shapes: readonly Shape[], cap: number): readonly Shape[] {
    if (cap <= 0 || shapes.length <= cap) return shapes;
    return [this.topShape];
  }

  private intern(fields: readonly Field[]): Shape {
    // Order-INSENSITIVE interning: a discovered class is a *set* of typed fields,
    // so we canonicalize to sorted order before hashing. Permutations of the same
    // fields (e.g. a prototype whose methods are assigned in any interleaving)
    // collapse to ONE class instead of blowing up to N! ordered shapes. V8 keeps
    // insertion order for inline-cache reasons; an AOT layout we control does not
    // need it, and the sorted order gives every class a deterministic struct.
    const canonical = canonicalize(fields);
    const k = shapeStructureKey(canonical);
    let s = this.byStructure.get(k);
    if (!s) {
      s = { id: this.nextId++, fields: canonical };
      this.byStructure.set(k, s);
    }
    return s;
  }

  /** The empty hidden class (a fresh `{}` object). */
  empty(): Shape {
    return this.emptyShape;
  }

  /** Build a shape from an ordered list of `(name, type)` fields. */
  fromFields(fields: ReadonlyArray<readonly [PropName, TypeSig]>): Shape {
    let s = this.emptyShape;
    for (const [name, type] of fields) s = this.transition(s, name, type);
    return s;
  }

  /**
   * Follow (or create) the transition for assigning property `name` with
   * representation `type`:
   *  - a *new* property is appended (structural transition);
   *  - re-assigning an existing property with the *same* representation is a
   *    no-op;
   *  - re-assigning with a *different* representation replaces that field's type
   *    (a representation transition) — the AOT analogue of V8's map
   *    generalization.
   */
  transition(s: Shape, name: PropName, type: TypeSig): Shape {
    if (s.megamorphic) return s; // ⊤ already "has any field" — absorbs writes
    const idx = s.fields.findIndex((f) => f.name === name);
    if (idx >= 0 && s.fields[idx]!.type === type) return s;
    const ek = `${s.id}|${JSON.stringify(name)}:${type}`;
    let to = this.edges.get(ek);
    if (!to) {
      let next: Field[];
      if (idx < 0) {
        next = [...s.fields, { name, type }];
      } else {
        next = s.fields.slice();
        next[idx] = { name, type };
      }
      to = this.intern(next);
      this.edges.set(ek, to);
    }
    return to;
  }

  /** How many distinct shapes have been interned (for reporting/metrics). */
  get size(): number {
    return this.byStructure.size;
  }
}

/** Structural key for a shape — its interned id is canonical. */
export const shapeKey: Keyable<Shape> = { key: (s) => `S${s.id}` };

/** Does this shape carry a property with the given name (at any type)? */
export function shapeHas(s: Shape, name: PropName): boolean {
  return s.fields.some((f) => f.name === name);
}

/** A readable rendering like `{x: num, y: str}` for reports; `{⊤}` for megamorphic. */
export function shapeToString(s: Shape): string {
  if (s.megamorphic) return "{⊤}";
  return `{${s.fields.map((f) => `${f.name}: ${f.type}`).join(", ")}}`;
}
