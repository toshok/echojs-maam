/**
 * Value domains — the paper's `Val` class (`lit`/`clo`/`binop`/`elimBool`/
 * `elimClo`) and its concrete/abstract instances. This is the *value* knob,
 * orthogonal to time (context) and to the monad (sensitivity):
 *
 *  - {@link concreteDomain} — exact values; with concrete time it is a precise
 *    interpreter. `Power CVal` in the paper.
 *  - {@link abstractDomain} — a constant-propagation lattice (numbers/strings
 *    collapse to `⊤` past a widening bound) plus a precise set of closures.
 *    `Power AVal` in the paper. This is what makes a k-CFA terminate.
 *
 * Introduction (`lit`, `clo`) and elimination (`elimBool`, `elimClo`) form a
 * Galois connection between `℘(base)` and the value lattice — the soundness
 * obligation the paper leaves to the domain author.
 */

import type { Keyable } from "../data/key.js";
import { FinSet, powersetLattice } from "../data/finset.js";
import type { JoinSemilattice } from "../lattice.js";
import type { BinOp, Lit, UnOp } from "./core.js";
import type { Closure, OAddr } from "./state.js";
import type { TypeSig } from "./shapes.js";

/** Canonical field-type ordering, so representations render/compare stably. */
const TAG_ORDER = ["num", "str", "bool", "null", "undefined", "fn", "obj"] as const;

function renderTags(tags: ReadonlySet<string>): TypeSig {
  if (tags.has("⊤")) return "⊤"; // top absorbs every other tag
  if (tags.size === 0) return "never";
  const present = TAG_ORDER.filter((t) => tags.has(t));
  return present.join("|");
}

/**
 * The value-domain dictionary the machine is written against. `D` is the value
 * lattice element; `Ctx` is the time-context (closures embed environments that
 * embed addresses that embed time).
 */
export interface ValDomain<Ctx, D> {
  readonly name: string;
  readonly lattice: JoinSemilattice<D>;
  readonly key: Keyable<D>;

  /** `int-I`/`clo-I` introductions. */
  lit(l: Lit): D;
  /**
   * `⊤` — "any value, no information".  The degradation element: unknown-call
   * results, unmodeled imports, and unmodeled iteration bind this instead of
   * a made-up `undefined`.  One canonical value (join-absorbing), so degraded
   * bindings never multiply the state space.  `elimClo`/`elimObj` on ⊤ are
   * empty (its closures/objects cannot be enumerated) — call and property-walk
   * sites must check {@link isTop} and take their degrade paths.
   */
  readonly top: D;
  /** Is `d` (at least) the ⊤ element — i.e. may it be *any* value? */
  isTop(d: D): boolean;
  /**
   * The `⊤` of the string type — "any string". Used to enumerate an object's
   * *unknown* keys (array indices under `for-in`). Unrepresentable in the concrete
   * collecting domain (⊤ is infinite), which returns `⊥` there.
   */
  topString(): D;
  /** The `⊤` of the numeric / boolean types — "any number" / "any boolean". Like
   * {@link topString}, unrepresentable in the concrete domain (returns `⊥` there);
   * used by the standard-library intrinsic models (`Math.floor : … → anyNum`). */
  anyNum(): D;
  anyBool(): D;
  clo(c: Closure<Ctx>): D;
  /** Introduce an object reference (points to a heap `OAddr`) — cf. `clo`. */
  objRef(addr: OAddr<Ctx>): D;
  /** Introduce a modeled standard-library intrinsic (a callable global identified
   * by `id`, e.g. `"Math.floor"` or `"Array"`) — cf. `clo`, dispatched in the call
   * path via {@link elimIntrinsic}. */
  intrinsic(id: string): D;

  /** `δ⟦⊕⟧`: abstract binary/unary primitives. */
  binop(op: BinOp, l: D, r: D): D;
  unop(op: UnOp, a: D): D;

  /** `if0-E`: which truth values this abstract value can take (for branching). */
  elimBool(d: D): FinSet<boolean>;
  /** `clo-E`: which closures this abstract value can be (for calls). */
  elimClo(d: D): FinSet<Closure<Ctx>>;
  /** Which heap objects this value may point to (for property get/put) — cf. `elimClo`. */
  elimObj(d: D): FinSet<OAddr<Ctx>>;
  /** Which modeled intrinsics this value may be (for calls) — cf. `elimClo`. */
  elimIntrinsic(d: D): FinSet<string>;

  /**
   * The representation (type signature) of a value — used as the field type in a
   * type-aware hidden class, so `{x: number}` and `{x: string}` are distinct
   * classes. e.g. `"num"`, `"num|str"`, `"obj"`, or `"never"` for `⊥`.
   */
  typeSig(d: D): TypeSig;

  /** Is this the empty value (a stuck / unreachable result)? */
  isBottom(d: D): boolean;

  /**
   * EXACT concretization — the capability that separates a *reference
   * interpreter* from an *analysis*.  When defined, `concretize(d)` returns the
   * single primitive JS value `d` denotes (boxed, so `undefined` is
   * distinguishable from "not concretizable"), or `null` when `d` is not a
   * singleton primitive (⊥, a set of several values, ⊤, a closure, an object
   * reference).  The machine uses its presence as the *exactness contract*:
   * a domain that defines it demands exact standard-library evaluation — a
   * modeled intrinsic call either computes its real JS result from fully
   * concretized inputs or **degrades visibly** (`unknownCalls`), never applies
   * a summary transfer function.  The concrete domain defines it; the abstract
   * domain leaves it undefined and keeps the sound summaries.
   */
  concretize?(d: D): { readonly v: Prim } | null;
}

/** The primitive JS values exact intrinsic evaluation traffics in. */
export type Prim = number | string | boolean | null | undefined;

// ===========================================================================
// Concrete domain:  D = ℘(CVal)
// ===========================================================================

/**
 * A concrete value.  `top` is the degradation element: it appears only when
 * an analysis over the concrete domain hits an unmodeled construct (an unknown
 * call, an unmodeled import) — a run that produced a `top` is not an exact
 * evaluation and is excluded from differential comparisons anyway.
 */
export type CVal<Ctx> =
  | { readonly t: "num"; readonly v: number }
  | { readonly t: "bool"; readonly v: boolean }
  | { readonly t: "str"; readonly v: string }
  | { readonly t: "null" }
  | { readonly t: "undef" }
  | { readonly t: "clo"; readonly c: Closure<Ctx> }
  | { readonly t: "obj"; readonly addr: OAddr<Ctx> }
  /** A modeled standard-library intrinsic (`Math.floor`, `parseInt`, …) — a
   * callable value, so seeded globals are representable concretely and the
   * machine's exact-evaluation path can dispatch on the id. */
  | { readonly t: "intr"; readonly id: string }
  | { readonly t: "top" };

function cvalKey<Ctx>(closureK: Keyable<Closure<Ctx>>, oaddrK: Keyable<OAddr<Ctx>>): Keyable<CVal<Ctx>> {
  return {
    key: (v) => {
      switch (v.t) {
        case "num":
          // `String(-0)` is `"0"`: key −0 distinctly so a set holding both zeros
          // does not silently drop one (exactness, not just soundness).
          return `n:${Number.isFinite(v.v) ? (Object.is(v.v, -0) ? "-0" : v.v) : `#${v.v}`}`;
        case "bool":
          return `b:${v.v}`;
        case "str":
          return `s:${JSON.stringify(v.v)}`;
        case "null":
          return "null";
        case "undef":
          return "undef";
        case "clo":
          return `c:${closureK.key(v.c)}`;
        case "obj":
          return `o:${oaddrK.key(v.addr)}`;
        case "intr":
          return `i:${v.id}`;
        case "top":
          return "⊤";
      }
    },
  };
}

function truthyC<Ctx>(v: CVal<Ctx>): boolean {
  switch (v.t) {
    case "num":
      return v.v !== 0 && !Number.isNaN(v.v);
    case "bool":
      return v.v;
    case "str":
      return v.v !== "";
    case "null":
    case "undef":
      return false;
    case "clo":
    case "obj":
    case "intr":
      return true;
    case "top":
      return true; // never asked: elimBool special-cases ⊤ to {true, false}
  }
}

function applyBinC<Ctx>(op: BinOp, a: CVal<Ctx>, b: CVal<Ctx>): CVal<Ctx> {
  // A ⊤ operand poisons the result — the concrete domain has no partial tops.
  if (a.t === "top" || b.t === "top") return { t: "top" };
  // ToNumber (differential-harness finding): `null` coerces to 0, not NaN —
  // `1 + null` is 1 in JS. `undefined` (and uncoercible values) stay NaN.
  const num = (x: CVal<Ctx>): number =>
    x.t === "num" ? x.v : x.t === "bool" ? (x.v ? 1 : 0) : x.t === "str" ? Number(x.v) : x.t === "null" ? 0 : NaN;
  // JS relational comparison: when BOTH operands are strings the comparison is
  // lexicographic (`"a" < "b"` is true); numeric coercion otherwise
  // (differential-harness finding: the numeric-only version said false).
  const cmp = (lt: (x: number | string, y: number | string) => boolean): CVal<Ctx> =>
    a.t === "str" && b.t === "str" ? { t: "bool", v: lt(a.v, b.v) } : { t: "bool", v: lt(num(a), num(b)) };
  switch (op) {
    case "+":
      // JS string-or-numeric addition
      if (a.t === "str" || b.t === "str") return { t: "str", v: `${cvalToJs(a)}${cvalToJs(b)}` };
      return { t: "num", v: num(a) + num(b) };
    case "-":
      return { t: "num", v: num(a) - num(b) };
    case "*":
      return { t: "num", v: num(a) * num(b) };
    case "/":
      return { t: "num", v: num(a) / num(b) };
    case "%":
      return { t: "num", v: num(a) % num(b) };
    case "<":
      return cmp((x, y) => x < y);
    case "<=":
      return cmp((x, y) => x <= y);
    case ">":
      return cmp((x, y) => x > y);
    case ">=":
      return cmp((x, y) => x >= y);
    case "**":
      return { t: "num", v: num(a) ** num(b) };
    case "===":
      return { t: "bool", v: cvalStrictEq(a, b) };
    case "!==":
      return { t: "bool", v: !cvalStrictEq(a, b) };
    case "==":
      return { t: "bool", v: cvalLooseEq(a, b) };
    case "!=":
      return { t: "bool", v: !cvalLooseEq(a, b) };
    case "&":
      return { t: "num", v: (num(a) | 0) & (num(b) | 0) };
    case "|":
      return { t: "num", v: (num(a) | 0) | (num(b) | 0) };
    case "^":
      return { t: "num", v: (num(a) | 0) ^ (num(b) | 0) };
    case "<<":
      return { t: "num", v: (num(a) | 0) << (num(b) | 0) };
    case ">>":
      return { t: "num", v: (num(a) | 0) >> (num(b) | 0) };
    case ">>>":
      return { t: "num", v: (num(a) >>> 0) >>> (num(b) | 0) };
    case "instanceof":
      return { t: "bool", v: false }; // conservative: prototype-chain test not modeled concretely
    case "in":
      return { t: "bool", v: false }; // conservative
    case "&&":
      return truthyC(a) ? b : a;
    case "||":
      return truthyC(a) ? a : b;
  }
}

function applyUnC<Ctx>(op: UnOp, a: CVal<Ctx>): CVal<Ctx> {
  if (a.t === "top") return op === "void" ? { t: "undef" } : { t: "top" };
  const num = (x: CVal<Ctx>): number =>
    x.t === "num" ? x.v : x.t === "bool" ? (x.v ? 1 : 0) : x.t === "str" ? Number(x.v) : x.t === "null" ? 0 : NaN;
  switch (op) {
    case "-":
      return { t: "num", v: -num(a) };
    case "+":
      return { t: "num", v: num(a) };
    case "~":
      return { t: "num", v: ~(num(a) | 0) };
    case "!":
      return { t: "bool", v: !truthyC(a) };
    case "typeof":
      return { t: "str", v: cvalTypeof(a) };
    case "void":
      return { t: "undef" };
    case "toStr":
      return { t: "str", v: cvalToJs(a) };
  }
}

function cvalLooseEq<Ctx>(a: CVal<Ctx>, b: CVal<Ctx>): boolean {
  if (a.t === b.t) return cvalStrictEq(a, b);
  // null == undefined; number/string/bool coerce numerically; else not equal.
  const nullish = (x: CVal<Ctx>) => x.t === "null" || x.t === "undef";
  if (nullish(a) && nullish(b)) return true;
  if (nullish(a) || nullish(b)) return false;
  const num = (x: CVal<Ctx>): number =>
    x.t === "num" ? x.v : x.t === "bool" ? (x.v ? 1 : 0) : x.t === "str" ? Number(x.v) : NaN;
  if ((a.t === "num" || a.t === "str" || a.t === "bool") && (b.t === "num" || b.t === "str" || b.t === "bool"))
    return num(a) === num(b);
  return false;
}

function cvalStrictEq<Ctx>(a: CVal<Ctx>, b: CVal<Ctx>): boolean {
  if (a.t !== b.t) return false;
  switch (a.t) {
    case "num":
      return a.v === (b as typeof a).v;
    case "bool":
      return a.v === (b as typeof a).v;
    case "str":
      return a.v === (b as typeof a).v;
    case "null":
    case "undef":
      return true;
    case "clo":
      return a.c === (b as typeof a).c;
    case "intr":
      return a.id === (b as typeof a).id; // one seeded value per id — identity coincides with the id
    case "obj": {
      const bo = b as typeof a;
      return (
        a.addr.loc === bo.addr.loc &&
        a.addr.time.length === bo.addr.time.length &&
        a.addr.time.every((x, i) => x === bo.addr.time[i])
      );
    }
    case "top":
      return false; // unreachable: applyBinC short-circuits ⊤ operands
  }
}

function cvalToJs<Ctx>(a: CVal<Ctx>): string {
  switch (a.t) {
    case "num":
      return String(a.v);
    case "bool":
      return String(a.v);
    case "str":
      return a.v;
    case "null":
      return "null";
    case "undef":
      return "undefined";
    case "clo":
      return "function";
    case "intr":
      // Native functions stringify as `function <name>() { [native code] }`.
      return `function ${a.id.split(".").pop()}() { [native code] }`;
    case "obj":
      return "[object Object]";
    case "top":
      return "⊤"; // unreachable: callers short-circuit ⊤ operands
  }
}

function cvalTypeof<Ctx>(a: CVal<Ctx>): string {
  switch (a.t) {
    case "num":
      return "number";
    case "bool":
      return "boolean";
    case "str":
      return "string";
    case "undef":
      return "undefined";
    case "null":
      return "object";
    case "clo":
    case "intr":
      return "function";
    case "obj":
      return "object";
    case "top":
      return "⊤"; // unreachable: applyUnC short-circuits ⊤ operands
  }
}

/** The concrete value domain `℘(CVal)`. */
export function concreteDomain<Ctx>(
  closureK: Keyable<Closure<Ctx>>,
  oaddrK: Keyable<OAddr<Ctx>>,
): ValDomain<Ctx, FinSet<CVal<Ctx>>> {
  const K = cvalKey(closureK, oaddrK);
  const lattice = powersetLattice(K);
  const topSet = FinSet.of<CVal<Ctx>>(K, { t: "top" });
  return {
    name: "concrete (℘CVal)",
    lattice,
    key: { key: (s) => `{${[...s].map(K.key).sort().join(",")}}` },
    lit: (l) => FinSet.of(K, litToCVal<Ctx>(l)),
    top: topSet,
    isTop: (d) => [...d].some((v) => v.t === "top"),
    // ⊤-typed values are not representable concretely (the concrete interpreter
    // models the standard library by exact evaluation, not summaries).
    topString: () => FinSet.empty<CVal<Ctx>>(K),
    anyNum: () => FinSet.empty<CVal<Ctx>>(K),
    anyBool: () => FinSet.empty<CVal<Ctx>>(K),
    clo: (c) => FinSet.of<CVal<Ctx>>(K, { t: "clo", c }),
    objRef: (addr) => FinSet.of<CVal<Ctx>>(K, { t: "obj", addr }),
    intrinsic: (id) => FinSet.of<CVal<Ctx>>(K, { t: "intr", id }),
    binop: (op, l, r) => {
      let out = FinSet.empty<CVal<Ctx>>(K);
      for (const a of l) for (const b of r) out = out.add(applyBinC(op, a, b));
      return out;
    },
    unop: (op, a) => {
      let out = FinSet.empty<CVal<Ctx>>(K);
      for (const v of a) out = out.add(applyUnC(op, v));
      return out;
    },
    elimBool: (d) => {
      let out = FinSet.of<boolean>({ key: String });
      for (const v of d) {
        if (v.t === "top") out = out.add(true).add(false);
        else out = out.add(truthyC(v));
      }
      return out;
    },
    elimClo: (d) => {
      let out = FinSet.empty<Closure<Ctx>>(closureK);
      for (const v of d) if (v.t === "clo") out = out.add(v.c);
      return out;
    },
    elimObj: (d) => {
      let out = FinSet.empty<OAddr<Ctx>>(oaddrK);
      for (const v of d) if (v.t === "obj") out = out.add(v.addr);
      return out;
    },
    elimIntrinsic: (d) => {
      let out = FinSet.empty<string>({ key: (s) => s });
      for (const v of d) if (v.t === "intr") out = out.add(v.id);
      return out;
    },
    typeSig: (d) => {
      const tags = new Set<string>();
      for (const v of d) tags.add(cvalTag(v));
      return renderTags(tags);
    },
    isBottom: (d) => d.isEmpty(),
    concretize: (d) => {
      const items = d.toArray();
      if (items.length !== 1) return null;
      const v = items[0]!;
      switch (v.t) {
        case "num":
        case "bool":
        case "str":
          return { v: v.v };
        case "null":
          return { v: null };
        case "undef":
          return { v: undefined };
        case "clo":
        case "obj":
        case "intr":
        case "top":
          return null;
      }
    },
  };
}

function cvalTag<Ctx>(v: CVal<Ctx>): string {
  switch (v.t) {
    case "num":
      return "num";
    case "str":
      return "str";
    case "bool":
      return "bool";
    case "null":
      return "null";
    case "undef":
      return "undefined";
    case "clo":
    case "intr":
      return "fn";
    case "obj":
      return "obj";
    case "top":
      return "⊤";
  }
}

function litToCVal<Ctx>(l: Lit): CVal<Ctx> {
  switch (l.kind) {
    case "num":
      return { t: "num", v: l.value };
    case "bool":
      return { t: "bool", v: l.value };
    case "str":
      return { t: "str", v: l.value };
    case "null":
      return { t: "null" };
    case "undef":
      return { t: "undef" };
    case "top":
      return { t: "top" };
  }
}

// ===========================================================================
// Abstract domain:  D = AVal  (constant propagation + precise closures)
// ===========================================================================

/**
 * A `⊤`-or-finite-set abstraction: track a finite set of constants until it
 * exceeds `bound`, then widen to `⊤` ("any value of this type"). This keeps
 * numeric/string domains finite while retaining constant-propagation precision
 * for small programs.
 */
interface ConstSet<A> {
  readonly top: boolean;
  readonly items: FinSet<A>;
}

function constSetLattice<A>(K: Keyable<A>, bound: number): JoinSemilattice<ConstSet<A>> {
  const ps = powersetLattice(K);
  const norm = (top: boolean, items: FinSet<A>): ConstSet<A> =>
    top || items.size > bound ? { top: true, items: FinSet.empty(K) } : { top, items };
  return {
    bot: { top: false, items: FinSet.empty(K) },
    // Reference-preserving: return `a` unchanged when `b ⊑ a`.
    join: (a, b) => {
      if (a.top || (!b.top && b.items.isSubsetOf(a.items))) return a;
      return norm(a.top || b.top, a.items.union(b.items));
    },
    lte: (a, b) => (b.top ? true : a.top ? false : a.items.isSubsetOf(b.items)),
  };
}

/** An abstract value: a component per base type, plus closures and objects. */
export interface AVal<Ctx> {
  /**
   * `⊤` — may be ANY value (the degradation element). When set, every other
   * component is normalized to bottom, so ⊤ is one canonical value (not a
   * product) and joins involving it can never grow the state space.
   */
  readonly topP: boolean;
  readonly nums: ConstSet<number>;
  readonly strs: ConstSet<string>;
  readonly bools: FinSet<boolean>;
  readonly nullP: boolean;
  readonly undefP: boolean;
  readonly clos: FinSet<Closure<Ctx>>;
  readonly objs: FinSet<OAddr<Ctx>>;
  /** Modeled standard-library intrinsics this value may be (ids like `"Math.floor"`). */
  readonly intrinsics: FinSet<string>;
}

/** Widening bound for numeric/string constant sets before collapsing to `⊤`. */
export const DEFAULT_WIDEN_BOUND = 4;

export function abstractDomain<Ctx>(
  closureK: Keyable<Closure<Ctx>>,
  oaddrK: Keyable<OAddr<Ctx>>,
  bound: number = DEFAULT_WIDEN_BOUND,
): ValDomain<Ctx, AVal<Ctx>> {
  const numK: Keyable<number> = { key: (n) => (Number.isFinite(n) ? String(n) : `#${n}`) };
  const strK: Keyable<string> = { key: (s) => JSON.stringify(s) };
  const boolK: Keyable<boolean> = { key: String };
  const numsL = constSetLattice(numK, bound);
  const strsL = constSetLattice(strK, bound);
  const boolsL = powersetLattice(boolK);
  const closL = powersetLattice(closureK);
  const objsL = powersetLattice(oaddrK);
  const intrK: Keyable<string> = { key: (s) => s };
  const intrL = powersetLattice(intrK);

  const bot: AVal<Ctx> = {
    topP: false,
    nums: numsL.bot,
    strs: strsL.bot,
    bools: boolsL.bot,
    nullP: false,
    undefP: false,
    clos: closL.bot,
    objs: objsL.bot,
    intrinsics: intrL.bot,
  };

  /** The one canonical ⊤ value — every join that involves ⊤ returns exactly this. */
  const TOP: AVal<Ctx> = { ...bot, topP: true };

  const lattice: JoinSemilattice<AVal<Ctx>> = {
    bot,
    // Reference-preserving: every component join returns its left arg on a no-op,
    // so if none changed we return `a` itself — no allocation, and callers get
    // identity-based "did it grow?" for free. This is the hottest join in the run.
    join: (a, b) => {
      // ⊤ absorbs: the result collapses to the canonical TOP (never a product).
      if (a.topP) return a;
      if (b.topP) return TOP;
      const nums = numsL.join(a.nums, b.nums);
      const strs = strsL.join(a.strs, b.strs);
      const bools = boolsL.join(a.bools, b.bools);
      const clos = closL.join(a.clos, b.clos);
      const objs = objsL.join(a.objs, b.objs);
      const intrinsics = intrL.join(a.intrinsics, b.intrinsics);
      const nullP = a.nullP || b.nullP;
      const undefP = a.undefP || b.undefP;
      if (
        nums === a.nums &&
        strs === a.strs &&
        bools === a.bools &&
        clos === a.clos &&
        objs === a.objs &&
        intrinsics === a.intrinsics &&
        nullP === a.nullP &&
        undefP === a.undefP
      )
        return a;
      return { topP: false, nums, strs, bools, nullP, undefP, clos, objs, intrinsics };
    },
    lte: (a, b) =>
      b.topP ||
      (!a.topP &&
        numsL.lte(a.nums, b.nums) &&
        strsL.lte(a.strs, b.strs) &&
        boolsL.lte(a.bools, b.bools) &&
        (!a.nullP || b.nullP) &&
        (!a.undefP || b.undefP) &&
        closL.lte(a.clos, b.clos) &&
        objsL.lte(a.objs, b.objs) &&
        intrL.lte(a.intrinsics, b.intrinsics)),
  };

  const key: Keyable<AVal<Ctx>> = {
    key: (v) =>
      v.topP
        ? "⊤"
        : [
        v.nums.top ? "n:⊤" : `n:{${[...v.nums.items].map(numK.key).sort().join(",")}}`,
        v.strs.top ? "s:⊤" : `s:{${[...v.strs.items].map(strK.key).sort().join(",")}}`,
        `b:{${[...v.bools].map(boolK.key).sort().join(",")}}`,
        v.nullP ? "null" : "",
        v.undefP ? "undef" : "",
        `c:{${[...v.clos].map(closureK.key).sort().join(",")}}`,
        `o:{${[...v.objs].map(oaddrK.key).sort().join(",")}}`,
        `i:{${[...v.intrinsics].sort().join(",")}}`,
      ].join("|"),
  };

  const num = (n: number): AVal<Ctx> => ({ ...bot, nums: { top: false, items: FinSet.of(numK, n) } });
  const anyNum: AVal<Ctx> = { ...bot, nums: { top: true, items: FinSet.empty(numK) } };
  const str = (s: string): AVal<Ctx> => ({ ...bot, strs: { top: false, items: FinSet.of(strK, s) } });
  const anyStr: AVal<Ctx> = { ...bot, strs: { top: true, items: FinSet.empty(strK) } };
  const boolV = (b: boolean): AVal<Ctx> => ({ ...bot, bools: FinSet.of(boolK, b) });
  const anyBool: AVal<Ctx> = { ...bot, bools: FinSet.of(boolK, true, false) };

  const numbersOf = (v: AVal<Ctx>): "top" | number[] | null =>
    v.nums.top ? "top" : v.nums.items.isEmpty() ? null : v.nums.items.toArray();

  const binop = (op: BinOp, l: AVal<Ctx>, r: AVal<Ctx>): AVal<Ctx> => {
    // A ⊤ operand: refine by what the operator can produce (numeric operators
    // yield numbers, comparisons yield booleans, …) — sound, and keeps a single
    // degraded operand from erasing the whole expression's type.
    if (l.topP || r.topP) {
      switch (op) {
        case "-": case "*": case "/": case "%": case "**":
        case "&": case "|": case "^": case "<<": case ">>": case ">>>":
          return anyNum;
        case "<": case "<=": case ">": case ">=":
        case "===": case "!==": case "==": case "!=":
        case "instanceof": case "in":
          return anyBool;
        case "+":
          return lattice.join(anyNum, anyStr); // number or string, never anything else
        case "&&":
        case "||":
          return lattice.join(l, r); // one of the operands — ⊤ absorbs
      }
    }
    switch (op) {
      case "+": {
        // string if either side can be a string; numeric otherwise
        const canStr = l.strs.top || !l.strs.items.isEmpty() || r.strs.top || !r.strs.items.isEmpty();
        const numeric = liftNum2(l, r, (a, b) => a + b, num, anyNum);
        return canStr ? lattice.join(numeric, anyStr) : numeric;
      }
      case "-":
        return liftNum2(l, r, (a, b) => a - b, num, anyNum);
      case "*":
        return liftNum2(l, r, (a, b) => a * b, num, anyNum);
      case "/":
        return liftNum2(l, r, (a, b) => a / b, num, anyNum);
      case "%":
        return liftNum2(l, r, (a, b) => a % b, num, anyNum);
      case "<":
        return liftCmp(l, r, (a, b) => a < b, boolV, anyBool);
      case "<=":
        return liftCmp(l, r, (a, b) => a <= b, boolV, anyBool);
      case ">":
        return liftCmp(l, r, (a, b) => a > b, boolV, anyBool);
      case ">=":
        return liftCmp(l, r, (a, b) => a >= b, boolV, anyBool);
      case "**":
        return liftNum2(l, r, (a, b) => a ** b, num, anyNum);
      case "&":
        return liftNum2(l, r, (a, b) => (a | 0) & (b | 0), num, anyNum);
      case "|":
        return liftNum2(l, r, (a, b) => (a | 0) | (b | 0), num, anyNum);
      case "^":
        return liftNum2(l, r, (a, b) => (a | 0) ^ (b | 0), num, anyNum);
      case "<<":
        return liftNum2(l, r, (a, b) => (a | 0) << (b | 0), num, anyNum);
      case ">>":
        return liftNum2(l, r, (a, b) => (a | 0) >> (b | 0), num, anyNum);
      case ">>>":
        return liftNum2(l, r, (a, b) => (a >>> 0) >>> (b | 0), num, anyNum);
      case "===":
      case "!==":
      case "==":
      case "!=":
      case "instanceof":
      case "in":
        return anyBool; // sound and simple
      case "&&":
        // result is either l (when falsy) or r (when truthy) — join both possibilities
        return lattice.join(l, r);
      case "||":
        return lattice.join(l, r);
    }
  };

  function liftNum2(
    l: AVal<Ctx>,
    r: AVal<Ctx>,
    f: (a: number, b: number) => number,
    mk: (n: number) => AVal<Ctx>,
    top: AVal<Ctx>,
  ): AVal<Ctx> {
    const ln = numbersOf(l);
    const rn = numbersOf(r);
    if (ln === null || rn === null) return bot; // no numeric operands ⇒ nothing (may be joined elsewhere)
    if (ln === "top" || rn === "top") return top;
    let acc = lattice.bot;
    for (const a of ln) for (const b of rn) acc = lattice.join(acc, mk(f(a, b)));
    return acc;
  }

  function liftCmp(
    l: AVal<Ctx>,
    r: AVal<Ctx>,
    f: (a: number, b: number) => boolean,
    mk: (b: boolean) => AVal<Ctx>,
    top: AVal<Ctx>,
  ): AVal<Ctx> {
    const ln = numbersOf(l);
    const rn = numbersOf(r);
    if (ln === null || rn === null) return anyBool;
    if (ln === "top" || rn === "top") return top;
    let acc = lattice.bot;
    for (const a of ln) for (const b of rn) acc = lattice.join(acc, mk(f(a, b)));
    return acc;
  }

  return {
    name: `abstract (AVal, widen=${bound})`,
    lattice,
    key,
    lit: (l) => {
      switch (l.kind) {
        case "num":
          return num(l.value);
        case "bool":
          return boolV(l.value);
        case "str":
          return str(l.value);
        case "null":
          return { ...bot, nullP: true };
        case "undef":
          return { ...bot, undefP: true };
        case "top":
          return TOP;
      }
    },
    top: TOP,
    isTop: (d) => d.topP,
    topString: () => anyStr,
    anyNum: () => anyNum,
    anyBool: () => anyBool,
    clo: (c) => ({ ...bot, clos: FinSet.of(closureK, c) }),
    objRef: (addr) => ({ ...bot, objs: FinSet.of(oaddrK, addr) }),
    intrinsic: (id) => ({ ...bot, intrinsics: FinSet.of(intrK, id) }),
    binop,
    unop: (op, a) => {
      // ⊤ operand: every unary operator still has a known result type.
      if (a.topP) {
        switch (op) {
          case "-": case "+": case "~":
            return anyNum;
          case "!":
            return anyBool;
          case "typeof":
            return anyStr; // typeof of anything is SOME string
          case "void":
            return { ...bot, undefP: true };
          case "toStr":
            return anyStr;
        }
      }
      switch (op) {
        case "-":
          return liftNum2(a, num(0), (x) => -x, num, anyNum);
        case "+":
          return liftNum2(a, num(0), (x) => x, num, anyNum);
        case "~":
          return liftNum2(a, num(0), (x) => ~(x | 0), num, anyNum);
        case "void":
          return { ...bot, undefP: true };
        case "toStr": {
          // The implicit ToString of a template literal: constant-fold what we
          // can, widen the rest — the result is always ⊆ string.
          let out = lattice.bot;
          if (a.nums.top) out = lattice.join(out, anyStr);
          else for (const n of a.nums.items) out = lattice.join(out, str(String(n)));
          if (a.strs.top) out = lattice.join(out, anyStr);
          else for (const s of a.strs.items) out = lattice.join(out, str(s));
          for (const b of a.bools) out = lattice.join(out, str(String(b)));
          if (a.nullP) out = lattice.join(out, str("null"));
          if (a.undefP) out = lattice.join(out, str("undefined"));
          if (!a.clos.isEmpty() || !a.intrinsics.isEmpty() || !a.objs.isEmpty())
            out = lattice.join(out, anyStr);
          return out;
        }
        case "!": {
          let out = lattice.bot;
          for (const b of elimBoolA(a)) out = lattice.join(out, boolV(!b));
          return out.bools.isEmpty() ? anyBool : out;
        }
        case "typeof": {
          let out = lattice.bot;
          if (!a.nums.items.isEmpty() || a.nums.top) out = lattice.join(out, str("number"));
          if (!a.strs.items.isEmpty() || a.strs.top) out = lattice.join(out, str("string"));
          if (!a.bools.isEmpty()) out = lattice.join(out, str("boolean"));
          if (a.undefP) out = lattice.join(out, str("undefined"));
          if (a.nullP) out = lattice.join(out, str("object"));
          if (!a.clos.isEmpty() || !a.intrinsics.isEmpty()) out = lattice.join(out, str("function"));
          if (!a.objs.isEmpty()) out = lattice.join(out, str("object"));
          return out;
        }
      }
    },
    elimBool: elimBoolA,
    elimClo: (d) => d.clos,
    elimObj: (d) => d.objs,
    elimIntrinsic: (d) => d.intrinsics,
    typeSig: (v) => {
      if (v.topP) return "⊤";
      const tags = new Set<string>();
      if (v.nums.top || !v.nums.items.isEmpty()) tags.add("num");
      if (v.strs.top || !v.strs.items.isEmpty()) tags.add("str");
      if (!v.bools.isEmpty()) tags.add("bool");
      if (v.nullP) tags.add("null");
      if (v.undefP) tags.add("undefined");
      if (!v.clos.isEmpty() || !v.intrinsics.isEmpty()) tags.add("fn");
      if (!v.objs.isEmpty()) tags.add("obj");
      return renderTags(tags);
    },
    isBottom: (d) => lattice.lte(d, bot),
  };

  function elimBoolA(v: AVal<Ctx>): FinSet<boolean> {
    let out = FinSet.empty<boolean>({ key: String });
    if (v.topP) return out.add(true).add(false);
    // numbers: 0/NaN falsy, others truthy; without exact value assume both when non-empty
    if (v.nums.top) out = out.add(true).add(false);
    else
      for (const n of v.nums.items) out = out.add(n !== 0 && !Number.isNaN(n));
    if (v.strs.top) out = out.add(true).add(false);
    else for (const s of v.strs.items) out = out.add(s !== "");
    for (const b of v.bools) out = out.add(b);
    if (v.nullP || v.undefP) out = out.add(false);
    if (!v.clos.isEmpty()) out = out.add(true);
    if (!v.objs.isEmpty()) out = out.add(true);
    if (!v.intrinsics.isEmpty()) out = out.add(true); // a function object is truthy
    return out;
  }
}
