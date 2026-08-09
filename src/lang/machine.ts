/**
 * The CESK* abstract machine — the single definitional interpreter.
 *
 * `step : ControlState → Comp<ControlState>` is written *once*, against the
 * abstract {@link AnalysisMonad} (sequencing + nondeterminism + a store in
 * `MonadState`), the {@link ValDomain} (the value knob) and the {@link TimeDict}
 * (the context knob). Running it under different monads/domains/times is what
 * yields concrete evaluation, k-CFA, path/flow sensitivity, etc. — all from this
 * one text. This is the "M" in MAAM.
 *
 * Nondeterminism appears in exactly the two places the paper predicts:
 *  - `elimClo` at a call — every closure the operator might be.
 *  - `elimBool` at an `if` — every branch the condition might take.
 *
 * The store is written with `joinAt` (weak update), so finitely many abstract
 * addresses soundly summarize unboundedly many concrete allocations.
 */

import type { Keyable } from "../data/key.js";
import { FinMap } from "../data/finmap.js";
import { FinSet, powersetLattice } from "../data/finset.js";
import type { JoinSemilattice } from "../lattice.js";
import type { AnalysisMonad, Comp } from "../monad/monad.js";
import { mplusAll } from "../monad/monad.js";
import type { TimeDict, Time } from "../time.js";
import type { AExp, Expr, Loc, Name, RHS } from "./core.js";
import { freeVarsOfLam, litBool, litNull, litNum, litStr, litUndef, thisVarName } from "./core.js";
import type { FnSummary, Prim, ValDomain } from "./values.js";
import type { ACount, Addr, AbsObject, Closure, KAddr, Kont, OAddr, Store } from "./state.js";
import {
  Env,
  EnvInterner,
  MANY,
  ONE,
  absObjectLattice,
  addrKey,
  closureKey,
  emptyStore,
  envKey,
  kaddrKey,
  kontKey,
  oaddrKey,
  storeKey,
  storeLattice,
} from "./state.js";
import type { PropName, Shape } from "./shapes.js";
import { ShapeTable, isMegamorphic, shapeHas, shapeKey } from "./shapes.js";

/**
 * The context-increment type for this language is a program location (a call
 * site) — the paper's `ψ = LocNum`. Fixing `Ctx = Loc` here keeps the generic
 * state-space machinery (`Addr<Ctx>`, `Store<Ctx, D>`, …) reusable while the
 * machine commits to locations as the unit of context.
 */
type Ctx = Loc;

/**
 * How a call's calling-context increment is chosen:
 *  - `"call-site"` — the classic k-CFA increment is the call site (works for all
 *    calls; the machine's default).
 *  - `"object"` — object sensitivity: a *method* call's increment is the
 *    receiver's allocation site, so the same method is analyzed per receiver
 *    class. Non-method calls fall back to the call site.
 */
export type ContextStrategy = "call-site" | "object";

/** The machine's control state — everything except the store (which the monad threads). */
export interface ControlState<Ctx> {
  readonly control: Expr;
  readonly env: Env<Ctx>;
  readonly kaddr: KAddr<Ctx>;
  readonly time: Time<Ctx>;
}

/** Everything an analysis needs, bundled by {@link makeMachine}. */
export interface Machine<Ctx, D> {
  readonly domain: ValDomain<Ctx, D>;
  readonly time: TimeDict<Ctx>;
  readonly controlKey: Keyable<ControlState<Ctx>>;
  readonly storeKey: Keyable<Store<Ctx, D>>;
  readonly storeLattice: JoinSemilattice<Store<Ctx, D>>;
  readonly closureKey: Keyable<Closure<Ctx>>;
  /** The hidden-class transition graph interned during this run. */
  readonly shapes: ShapeTable;
  /** Constructor call graph: constructor-function loc → the `new`-site locs invoking it. */
  readonly constructorTargets: ReadonlyMap<Loc, ReadonlySet<Loc>>;
  /** Property-read site loc → the getter-function locs it dispatches to. */
  readonly accessorGetSites: ReadonlyMap<Loc, ReadonlySet<Loc>>;
  /** Property-write site loc → the setter-function locs it dispatches to. */
  readonly accessorSetSites: ReadonlyMap<Loc, ReadonlySet<Loc>>;
  /** Raw per-(function, context) parameter/return type observations (keyed `loc@ctx`). */
  readonly specObservations: ReadonlyMap<string, { loc: Loc; params: D[]; ret: D }>;
  /**
   * Call/`new` sites whose callee resolved to no closure — an unmodeled external
   * (runtime builtin, missing module, harness). In a closed-world AOT setting this
   * set should be *empty*; a non-empty set is a soundness caveat, not a fact.
   */
  readonly unknownCallSites: ReadonlySet<Loc>;
  /** The subset of open-world call sites that bound a cross-module summary's result. */
  readonly summarizedCallSites: ReadonlySet<Loc>;
  /**
   * Cap-saturation telemetry: how often (and where) convergence was *forced* by
   * a widening cap rather than reached naturally. `stateCapHits` counts calls
   * routed through a widened continuation address (with the functions affected);
   * `shapeCapHits` counts shape-set collapses to the megamorphic ⊤ shape.
   */
  readonly capStats: {
    stateCapHits: number;
    readonly stateCapFuncs: ReadonlySet<Loc>;
    shapeCapHits: number;
  };
  /** Build the initial control state and store for a whole program. */
  inject(program: Expr): { c0: ControlState<Ctx>; s0: Store<Ctx, D> };
  /** The step relation, written against the monad `M`. */
  step(M: AnalysisMonad<Store<Ctx, D>>): (c: ControlState<Ctx>) => Comp<ControlState<Ctx>>;
  /** Abstract garbage collection: restrict a store to what `c` can still reach. */
  gcStore(c: ControlState<Ctx>, store: Store<Ctx, D>): Store<Ctx, D>;
  /** Is this a final state (a `return` to the top-level `Halt`)? */
  isFinal(c: ControlState<Ctx>, store: Store<Ctx, D>): boolean;
  /** The value(s) a final state returns to `Halt`. */
  finalValue(c: ControlState<Ctx>, store: Store<Ctx, D>): D;
}

/** Assemble a machine from a value domain and a time abstraction. */
export function makeMachine<D>(
  domain: ValDomain<Ctx, D>,
  time: TimeDict<Ctx>,
  context: ContextStrategy = "call-site",
  retOwner: ReadonlyMap<Loc, Loc> = new Map(),
  /** Max distinct hidden classes per object address before widening to `⊤` (0 = off). */
  shapeCap = 0,
  /**
   * Recency: strong-update statically-known singleton objects (function
   * prototypes) instead of weak-accumulating their shapes. Only sound/effective
   * under flow-sensitive analysis (a flow-insensitive global-store join re-unions
   * and undoes the strong update).
   */
  recency = false,
  /**
   * **Abstract counting** (Might & Shivers ΓCFA + Balakrishnan–Reps recency) — the
   * *generalization* of `recency`'s prototype-only strong update to **any** address
   * whose abstract count is `ONE`. Tracks `OAddr → ONE|MANY` in the store, bumps on
   * (re)allocation, and pairs with abstract GC (a collected address resets to `0`,
   * so a non-escaping allocation stays `ONE`). Collapses a once-allocated object's
   * field-init from a 2ᴺ shape powerset to a linear chain. Sound, but adds a store
   * component: a net win for allocation-*light* / constructor code, a net cost on
   * allocation-*heavy* looped code (whose objects reach `MANY` regardless, at k=0).
   */
  counting = false,
  /**
   * Pushdown (P4F): allocate continuation addresses on the caller's environment so
   * call/return is exactly matched — eliminating the return-flow smearing that
   * inflates the state space on deep/recursive call graphs.
   */
  pushdown = false,
  /**
   * **State-widening cap** — the safety valve that makes the analysis *total*
   * (always terminates in bounded time) on any input. At most `stateCap` distinct
   * calling contexts per function; beyond that a function's calls collapse to a
   * single *widened* continuation (its returns smear to every caller), and
   * environments are canonicalized per program point (sound at k=0). Bounds the
   * state space to `locations × (cap+1)`, trading precision for a guaranteed
   * result. 0 = off.
   */
  stateCap = 0,
  /**
   * **Standard-library intrinsics.** When on, seed the initial store with modeled
   * JS globals (`Math`, `Array`, `parseInt`, `String.fromCharCode`, …) as callable
   * *intrinsic* values with sound summary transfer functions, instead of leaving
   * them unbound and *degrading* every call to `⊤`. Sharpens value types (e.g. a
   * `Math.floor` result is `num`, not unknown) — a precision/soundness win that
   * removes the degradation over-approximation. Abstract-domain only (the concrete
   * interpreter models the library by exact evaluation). 0/false = off.
   */
  intrinsics = false,
): Machine<Ctx, D> {
  const DJ = domain.lattice;
  const ak = addrKey<Ctx>(time.key);
  const kak = kaddrKey<Ctx>(time.key);
  const oak = oaddrKey<Ctx>(time.key);
  const envInterner = new EnvInterner();
  const envK = envKey<Ctx>();
  const closureK = closureKey<Ctx>(envK);
  const kontK = kontKey<Ctx>(envK, kak, time.key, oak);
  const kontSetL = powersetLattice(kontK);
  const objLat = absObjectLattice<Ctx, D>(oak, DJ);

  /** The canonical prototype-object address for a function (lambda) location — a singleton. */
  const protoAddr = (lambdaLoc: Loc): OAddr<Ctx> => ({ loc: lambdaLoc, time: time.tzero, proto: true });

  // Synthetic singleton addresses for the seeded standard-library objects (only
  // populated when `intrinsics` is on). Negative locs never collide with program
  // locs. `Array.prototype`/`String.prototype` back the array/string methods (§Phase 2).
  const ARRAY_PROTO_ADDR: OAddr<Ctx> = { loc: -110, time: time.tzero };
  const STRING_PROTO_ADDR: OAddr<Ctx> = { loc: -111, time: time.tzero };
  /** The prototype link a freshly-allocated array carries — `Array.prototype` when
   * intrinsics are modeled (so `arr.push`/`arr.slice` resolve), else empty. */
  const arrayProtoLink = (): FinSet<OAddr<Ctx>> =>
    intrinsics ? FinSet.of(oak, ARRAY_PROTO_ADDR) : FinSet.empty(oak);

  /** Accessor dispatch: property-access-site loc → the getter/setter functions it resolves to. */
  const accessorGetSites = new Map<Loc, Set<Loc>>();
  const accessorSetSites = new Map<Loc, Set<Loc>>();
  const recordAccessor = (m: Map<Loc, Set<Loc>>, site: Loc, cloLoc: Loc): void => {
    let s = m.get(site);
    if (!s) {
      s = new Set();
      m.set(site, s);
    }
    s.add(cloLoc);
  };
  const skey = storeKey<Ctx, D>(ak, kak, oak, domain.key, kontK);
  const sLat = storeLattice<Ctx, D>(ak, kak, oak, DJ, kontK);

  /** The hidden-class transition graph, shared (interned) across this run. */
  const shapes = new ShapeTable();

  /** State-cap: distinct continuation-address keys seen per function (loc). */
  const funcContexts = new Map<Loc, Set<string>>();

  /** Call/`new`/method/`apply`/tail-call sites that hit an unmodeled (closureless) callee — see the interface field. */
  const unknownCallSites = new Set<Loc>();

  /** Cap-saturation telemetry — see the interface field. */
  const capStats = { stateCapHits: 0, stateCapFuncs: new Set<Loc>(), shapeCapHits: 0 };
  function recordUnknownCall(loc: Loc): void {
    unknownCallSites.add(loc);
  }

  /**
   * Sites that dispatched through a cross-module callable summary.  These
   * ALSO count as unknown calls (the callee's effects on its arguments are
   * unmodeled — the open-world bit must stay honest); this set tracks how
   * many of the open-world calls at least bound a summarized result.
   */
  const summarizedCallSites = new Set<Loc>();
  function recordSummarizedCall(loc: Loc): void {
    recordUnknownCall(loc);
    summarizedCallSites.add(loc);
  }

  /** Constructor call graph: constructor-function loc → the `new`-site locs invoking it. */
  const constructorTargets = new Map<Loc, Set<Loc>>();
  function recordConstructor(ctorLoc: Loc, newLoc: Loc): void {
    let s = constructorTargets.get(ctorLoc);
    if (!s) {
      s = new Set();
      constructorTargets.set(ctorLoc, s);
    }
    s.add(newLoc);
  }

  /**
   * Per-(function, calling-context) observations of parameter and return types.
   * Params are recorded at call entry, the return at each `ret`; both key on the
   * same `(owning-lambda, entry-context)`, so they line up into a
   * `(param types) → return type` row per specialization.
   */
  const specObs = new Map<string, { loc: Loc; params: D[]; ret: D }>();
  const specKey = (loc: Loc, t: Time<Ctx>): string => `${loc}@${time.key.key(t)}`;
  function recordSpecParams(loc: Loc, t: Time<Ctx>, argVals: ReadonlyArray<D>, arity: number): void {
    const key = specKey(loc, t);
    let rec = specObs.get(key);
    if (!rec) {
      rec = { loc, params: [], ret: DJ.bot };
      specObs.set(key, rec);
    }
    for (let i = 0; i < arity; i++) {
      const v = i < argVals.length ? argVals[i]! : domain.lit(litUndef);
      rec.params[i] = DJ.join(rec.params[i] ?? DJ.bot, v);
    }
  }
  function recordSpecReturn(owner: Loc, t: Time<Ctx>, v: D): void {
    const key = specKey(owner, t);
    let rec = specObs.get(key);
    if (!rec) {
      rec = { loc: owner, params: [], ret: DJ.bot };
      specObs.set(key, rec);
    }
    rec.ret = DJ.join(rec.ret, v);
  }

  const controlKey: Keyable<ControlState<Ctx>> = {
    // Under the state cap, drop the environment id from the key: at k=0 the
    // environment is determined by the control location, so distinct (path-dependent)
    // env ids at the same point are spurious — merging them is sound and removes a
    // multiplier. (Value differences live in the store, which is joined per key.)
    key: (c) =>
      stateCap > 0
        ? `‹${c.control.loc}|${kak.key(c.kaddr)}|${time.key.key(c.time)}›`
        : `‹${c.control.loc}|${envK.key(c.env)}|${kak.key(c.kaddr)}|${time.key.key(c.time)}›`,
  };

  /** Pure atomic evaluation — never steps, never branches. */
  function atomEval(a: AExp, env: Env<Ctx>, store: Store<Ctx, D>): D {
    switch (a.tag) {
      case "lit":
        return domain.lit(a.lit);
      case "var": {
        const addr = env.get(a.name);
        if (!addr) return DJ.bot; // free variable ⇒ ⊥ (stuck)
        return store.vals.getOr(addr, DJ.bot);
      }
      case "lam":
        // Trim the captured env to the lambda's free variables — a closure can't
        // reference anything else, and small envs keep control-state keys cheap.
        return domain.clo({ loc: a.loc, params: a.params, body: a.body, env: env.restrict(freeVarsOfLam(a)) });
    }
  }

  /** Environments are keyed by variable name (a string), not by address. */
  const nameK: Keyable<Name> = { key: (n) => n };
  const kaddr0: KAddr<Ctx> = { loc: -1, time: time.tzero };

  function inject(program: Expr): { c0: ControlState<Ctx>; s0: Store<Ctx, D> } {
    const empty = emptyStore<Ctx, D>(ak, kak, oak);
    const halt: Kont<Ctx> = { tag: "halt" };
    // Seed the standard-library globals when modeling is on; otherwise start empty
    // (free globals resolve to ⊥ and their calls degrade, as before).
    const seeded = intrinsics
      ? seedGlobals(Env.empty<Ctx>(envInterner, ak), empty.vals, empty.objs)
      : { env: Env.empty<Ctx>(envInterner, ak), vals: empty.vals, objs: empty.objs };
    const s0: Store<Ctx, D> = {
      vals: seeded.vals,
      konts: empty.konts.joinAt(kontSetL, kaddr0, FinSet.of<Kont<Ctx>>(kontK, halt)),
      objs: seeded.objs,
      counts: empty.counts,
    };
    const c0: ControlState<Ctx> = {
      control: program,
      env: seeded.env,
      kaddr: kaddr0,
      time: time.tzero,
    };
    return { c0, s0 };
  }

  /** Bind `name ↦ value` at the current time, weakly updating the store. */
  function bindVar(
    env: Env<Ctx>,
    vals: FinMap<Addr<Ctx>, D>,
    name: Name,
    value: D,
    t: Time<Ctx>,
  ): { env: Env<Ctx>; vals: FinMap<Addr<Ctx>, D> } {
    const addr: Addr<Ctx> = { name, time: t };
    return { env: env.set(name, addr), vals: vals.joinAt(DJ, addr, value) };
  }

  /** Bind `name ↦ value` and step to `body` in the same continuation (no frame). */
  function bindAndContinue(
    M: AnalysisMonad<Store<Ctx, D>>,
    name: Name,
    value: D,
    body: Expr,
    env: Env<Ctx>,
    kaddr: KAddr<Ctx>,
    t: Time<Ctx>,
    store: Store<Ctx, D>,
  ): Comp<ControlState<Ctx>> {
    const bound = bindVar(env, store.vals, name, value, t);
    const store2: Store<Ctx, D> = { ...store, vals: bound.vals };
    return M.bind(M.put(store2), () => M.unit({ control: body, env: bound.env, kaddr, time: t }));
  }

  /** Property names are keyed structurally (must match `state.ts`'s propK). */
  const propK: Keyable<PropName> = { key: (p) => JSON.stringify(p) };

  /** Abstract-count bump on (re)allocation: `0 → ONE → MANY` (`MANY` is a fixpoint). */
  const bumpCount = (c: ACount): ACount => (c === 0 ? ONE : MANY);

  /**
   * Install a freshly-allocated object at `oaddr`, threading the abstract-count map.
   * Under concrete time an `OAddr` names one object, so we `set` (strong); under
   * k-CFA the address summarizes many, so we `joinAt` (weak). With **abstract
   * counting** on (recency), a bump to `ONE` (the address was absent — a genuinely
   * fresh singleton, possibly because GC just collected the prior object) permits a
   * strong `set`; a bump to `MANY` (the address is already live) forces the weak join.
   */
  function installObj(
    objs: FinMap<OAddr<Ctx>, AbsObject<Ctx, D>>,
    counts: FinMap<OAddr<Ctx>, ACount>,
    oaddr: OAddr<Ctx>,
    obj: AbsObject<Ctx, D>,
  ): { objs: FinMap<OAddr<Ctx>, AbsObject<Ctx, D>>; counts: FinMap<OAddr<Ctx>, ACount> } {
    if (time.singletonAddrs) return { objs: objs.set(oaddr, obj), counts };
    if (!counting) return { objs: objs.joinAt(objLat, oaddr, obj), counts };
    const n = bumpCount(counts.getOr(oaddr, 0));
    return {
      objs: n === ONE ? objs.set(oaddr, obj) : objs.joinAt(objLat, oaddr, obj),
      counts: counts.set(oaddr, n),
    };
  }

  /**
   * The value a call through a callable summary binds: the summary's
   * ⊤-argument result.  An OBJECT result (shape form) materializes as an
   * OPEN object at the CALL SITE — a per-site allocation, so each caller's
   * own mutations are tracked locally; aliasing BETWEEN callers is the
   * checked-tier story (shape facts are runtime-guarded, field values are
   * already `⊤`).  A primitive result maps through the summary lit; no
   * result payload means `⊤`.
   */
  function fnSummaryResult(
    fs: FnSummary,
    loc: Loc,
    t: Time<Ctx>,
    objs0: FinMap<OAddr<Ctx>, AbsObject<Ctx, D>>,
    counts0: FinMap<OAddr<Ctx>, ACount>,
  ): { v: D; objs: FinMap<OAddr<Ctx>, AbsObject<Ctx, D>>; counts: FinMap<OAddr<Ctx>, ACount> } {
    const r = fs.result;
    if (r === undefined || r.fields !== undefined)
      return { v: domain.top, objs: objs0, counts: counts0 };
    if (r.shape !== undefined) {
      const oaddr: OAddr<Ctx> = { loc, time: t };
      let fields = FinMap.empty<PropName, D>(propK);
      for (const f of r.shape) fields = fields.joinAt(DJ, f.name, domain.top);
      const shape = shapes.fromFields(r.shape.map((f) => [f.name, f.sig] as const));
      const alloc = installObj(objs0, counts0, oaddr, {
        shapes: FinSet.of(shapeKey, shape),
        fields,
        accessors: FinMap.empty(propK),
        proto: FinSet.empty(oak),
        elements: DJ.bot,
        open: true, // the callee (or another caller) may have added fields
      });
      return { v: domain.objRef(oaddr), objs: alloc.objs, counts: alloc.counts };
    }
    return { v: domain.lit({ kind: "summary", summary: r }), objs: objs0, counts: counts0 };
  }

  // --- standard-library intrinsics (Phase 1: pure statics + Array/Object alloc) ---

  /**
   * The effect of calling a modeled intrinsic: its result value, plus any heap it
   * allocated (`Array`/`Object` build a fresh object; pure `Math.*`/`parseInt`
   * leave the store untouched). `null` ⇒ not a modeled intrinsic (fall through to
   * the usual degrade).
   */
  type IntrinsicEffect = {
    value: D;
    objs: FinMap<OAddr<Ctx>, AbsObject<Ctx, D>>;
    counts: FinMap<OAddr<Ctx>, ACount>;
  };
  /**
   * The context a modeled intrinsic is applied in: its argument values, the
   * *receiver* value (`⊥` for statics/bare functions; the array/string for
   * prototype methods), a fresh allocation site for constructors/result arrays,
   * and the current heap + counts (for reads and mutations).
   */
  type IntrinsicCtx = {
    args: ReadonlyArray<D>;
    recv: D;
    oaddr: OAddr<Ctx>;
    objs: FinMap<OAddr<Ctx>, AbsObject<Ctx, D>>;
    counts: FinMap<OAddr<Ctx>, ACount>;
  };
  type IntrinsicFn = (ctx: IntrinsicCtx) => IntrinsicEffect;

  const pure = (make: () => D): IntrinsicFn => (ctx) => ({ value: make(), objs: ctx.objs, counts: ctx.counts });
  const NUM = pure(() => domain.anyNum());
  const BOOLN = pure(() => domain.anyBool());
  const STRN = pure(() => domain.topString());
  const joinArgs = (args: ReadonlyArray<D>): D => args.reduce((acc, a) => DJ.join(acc, a), DJ.bot);
  /** The join of the `elements` buckets of every object `recv` may point to. */
  const recvElements = (recv: D, objs: FinMap<OAddr<Ctx>, AbsObject<Ctx, D>>): D => {
    let e = DJ.bot;
    for (const a of domain.elimObj(recv)) e = DJ.join(e, objs.getOr(a, objLat.bot).elements);
    return e;
  };
  /** Weak-add `add` into the `elements` bucket of every object `recv` may point to. */
  const pushElements = (
    recv: D,
    add: D,
    objs: FinMap<OAddr<Ctx>, AbsObject<Ctx, D>>,
  ): FinMap<OAddr<Ctx>, AbsObject<Ctx, D>> => {
    let out = objs;
    for (const a of domain.elimObj(recv)) {
      const o = out.getOr(a, objLat.bot);
      out = out.set(a, { ...o, elements: DJ.join(o.elements, add) });
    }
    return out;
  };

  /** Allocate a fresh array (given elements) or plain object at the call site. */
  function allocIntrinsicObj(array: D | null, ctx: IntrinsicCtx): IntrinsicEffect {
    const obj: AbsObject<Ctx, D> =
      array !== null
        ? {
            shapes: FinSet.of(shapeKey, shapes.fromFields([["length", "num"]])),
            fields: FinMap.fromEntries<PropName, D>(propK, [["length", domain.anyNum()]]),
            accessors: FinMap.empty(propK),
            proto: arrayProtoLink(),
            elements: array, // holes read as `undefined` via getDyn; fills accumulate on write
          }
        : {
            shapes: FinSet.of(shapeKey, shapes.empty()),
            fields: FinMap.empty(propK),
            accessors: FinMap.empty(propK),
            proto: FinSet.empty(oak),
            elements: DJ.bot,
          };
    const r = installObj(ctx.objs, ctx.counts, ctx.oaddr, obj);
    return { value: domain.objRef(ctx.oaddr), objs: r.objs, counts: r.counts };
  }

  /** id → summary transfer function. Extend this table to widen library coverage. */
  const intrinsicModels = new Map<string, IntrinsicFn>();
  const registerAll = (ids: ReadonlyArray<string>, fn: IntrinsicFn): void => {
    for (const id of ids) intrinsicModels.set(id, fn);
  };
  // --- Phase 1: pure statics + constructors ---
  // Number-returning pure statics.
  registerAll(
    [
      "Math.floor", "Math.ceil", "Math.round", "Math.trunc", "Math.abs", "Math.sign",
      "Math.sqrt", "Math.cbrt", "Math.pow", "Math.exp", "Math.expm1", "Math.log",
      "Math.log2", "Math.log10", "Math.log1p", "Math.min", "Math.max", "Math.hypot",
      "Math.sin", "Math.cos", "Math.tan", "Math.asin", "Math.acos", "Math.atan",
      "Math.atan2", "Math.sinh", "Math.cosh", "Math.tanh", "Math.random", "Math.fround",
      "Math.clz32", "Math.imul",
      "parseInt", "parseFloat", "Number", "Number.parseInt", "Number.parseFloat",
    ],
    NUM,
  );
  // Boolean-returning pure statics.
  registerAll(
    [
      "isNaN", "isFinite", "Boolean", "Array.isArray",
      "Number.isNaN", "Number.isFinite", "Number.isInteger", "Number.isSafeInteger",
    ],
    BOOLN,
  );
  // String-returning pure statics.
  registerAll(["String", "String.fromCharCode", "String.fromCodePoint"], STRN);
  // Allocating constructors (`Array(n)` / `new Array(n)`, `Object()` / `new Object()`).
  intrinsicModels.set("Array", (ctx) => allocIntrinsicObj(DJ.bot, ctx));
  intrinsicModels.set("Object", (ctx) => allocIntrinsicObj(null, ctx));

  // --- Phase 2: Array.prototype methods (heap effects on the receiver's elements) ---
  // Mutating: append args to the shared elements bucket; return the new length (num).
  registerAll(["Array.prototype.push", "Array.prototype.unshift"], (ctx) => ({
    value: domain.anyNum(),
    objs: pushElements(ctx.recv, joinArgs(ctx.args), ctx.objs),
    counts: ctx.counts,
  }));
  // Removing: return an element (or `undefined`); we do not shrink `length` precisely.
  registerAll(["Array.prototype.pop", "Array.prototype.shift"], (ctx) => ({
    value: DJ.join(recvElements(ctx.recv, ctx.objs), domain.lit(litUndef)),
    objs: ctx.objs,
    counts: ctx.counts,
  }));
  // Copying: a fresh array whose elements ⊔ the receiver's (and, for concat, the args').
  registerAll(["Array.prototype.slice", "Array.prototype.concat", "Array.prototype.flat"], (ctx) => {
    let elems = recvElements(ctx.recv, ctx.objs);
    for (const a of ctx.args) elems = DJ.join(elems, DJ.join(a, recvElements(a, ctx.objs)));
    return allocIntrinsicObj(elems, ctx);
  });
  // In-place, returns the receiver. `sort`'s comparator (if any) is ignored soundly
  // for the ordering (elements are index-insensitive); it is *not* invoked (Phase 3).
  registerAll(["Array.prototype.reverse", "Array.prototype.sort"], (ctx) => ({
    value: ctx.recv,
    objs: ctx.objs,
    counts: ctx.counts,
  }));
  intrinsicModels.set("Array.prototype.fill", (ctx) => ({
    value: ctx.recv,
    objs: pushElements(ctx.recv, joinArgs(ctx.args), ctx.objs),
    counts: ctx.counts,
  }));
  registerAll(["Array.prototype.indexOf", "Array.prototype.lastIndexOf"], NUM);
  registerAll(["Array.prototype.includes"], BOOLN);
  registerAll(["Array.prototype.join", "Array.prototype.toString"], STRN);

  // --- Phase 2: String.prototype methods (immutable receiver — no heap effect) ---
  registerAll(
    [
      "String.prototype.charCodeAt", "String.prototype.codePointAt", "String.prototype.indexOf",
      "String.prototype.lastIndexOf", "String.prototype.search", "String.prototype.localeCompare",
    ],
    NUM,
  );
  registerAll(
    [
      "String.prototype.charAt", "String.prototype.slice", "String.prototype.substring",
      "String.prototype.substr", "String.prototype.toUpperCase", "String.prototype.toLowerCase",
      "String.prototype.trim", "String.prototype.trimStart", "String.prototype.trimEnd",
      "String.prototype.replace", "String.prototype.replaceAll", "String.prototype.concat",
      "String.prototype.repeat", "String.prototype.padStart", "String.prototype.padEnd",
      "String.prototype.normalize", "String.prototype.toString", "String.prototype.at",
    ],
    STRN,
  );
  registerAll(["String.prototype.includes", "String.prototype.startsWith", "String.prototype.endsWith"], BOOLN);
  // `split` → a fresh array of (unknown) strings.
  intrinsicModels.set("String.prototype.split", (ctx) => allocIntrinsicObj(domain.topString(), ctx));

  // --- Phase 3: higher-order Array methods (invoke the callback through the machine) ---
  // These are NOT synchronous (no entry in `intrinsicModels`): they spawn a real
  // call to the user callback. Because elements are index-insensitive, the callback
  // is entered *once* with the smashed element value; the abstract fixpoint covers
  // every concrete element. Seeded as intrinsic fields on `Array.prototype` below.
  const HIGHER_ORDER_ARRAY = [
    "map", "flatMap", "forEach", "filter", "find", "findIndex", "findLast",
    "some", "every", "reduce", "reduceRight", "sort",
  ] as const;
  const higherOrderArray = new Set<string>(HIGHER_ORDER_ARRAY);

  // --- Exact intrinsic evaluation (the differential-oracle contract) ---
  //
  // A domain that defines `concretize` (the concrete domain) demands *exact*
  // standard-library results: summaries like `anyNum()` are unrepresentable
  // there (⊥), so applying a summary model would silently kill or widen a path.
  // Under such a domain an intrinsic call either (a) is a **pure function of
  // primitives** whose inputs all concretize — then we compute the real JS
  // result and inject it as a literal — or (b) **degrades visibly** through the
  // unknown-call path (`recordUnknownCall` + ⊤), so `metrics.unknownCalls`
  // flags the run as non-exact and the differential harness skips the file.
  // Heap-touching intrinsics (`Array`, `arr.push`, `arr.join`, higher-order
  // methods) always take (b): the smashed `elements` bucket makes their exact
  // result unknowable. `Math.random` also takes (b): nondeterminism is never
  // "exact".
  const exactMode = domain.concretize !== undefined;
  /** Pure-primitive intrinsics: exact result = the real JS function applied to
   * the concretized receiver/arguments. Everything not listed degrades. */
  const EXACT_PURE_STATICS: Readonly<Record<string, unknown>> = {
    parseInt, parseFloat, isNaN, isFinite,
    Number, String, Boolean,
    "Number.parseInt": Number.parseInt, "Number.parseFloat": Number.parseFloat,
    "Number.isNaN": Number.isNaN, "Number.isFinite": Number.isFinite,
    "Number.isInteger": Number.isInteger, "Number.isSafeInteger": Number.isSafeInteger,
    "String.fromCharCode": String.fromCharCode, "String.fromCodePoint": String.fromCodePoint,
    // On a *primitive* argument `Array.isArray` is exactly `false`; object
    // arguments do not concretize, so the true case degrades rather than lies.
    "Array.isArray": Array.isArray,
    ...Object.fromEntries(
      [...intrinsicModels.keys()]
        .filter((id) => id.startsWith("Math.") && id !== "Math.random")
        .map((id) => [id, (Math as unknown as Record<string, unknown>)[id.slice("Math.".length)]]),
    ),
  };
  /** `String.prototype.*` models that are pure `(string receiver, primitive
   * args) → primitive` — everything registered except `split` (returns an
   * array). `replace`/`replaceAll` with a *function* replacer degrade anyway
   * (a closure never concretizes). */
  const exactStringMethod = (id: string): unknown => {
    if (!id.startsWith("String.prototype.")) return undefined;
    const m = id.slice("String.prototype.".length);
    if (m === "split" || !intrinsicModels.has(id)) return undefined;
    return (String.prototype as unknown as Record<string, unknown>)[m];
  };
  const primToLit = (v: Prim): D | null => {
    switch (typeof v) {
      case "number":
        return domain.lit(litNum(v));
      case "string":
        return domain.lit(litStr(v));
      case "boolean":
        return domain.lit(litBool(v));
      case "undefined":
        return domain.lit(litUndef);
      default:
        return v === null ? domain.lit(litNull) : null; // non-primitive result: not exact
    }
  };
  /**
   * Try to evaluate intrinsic `id` exactly: every argument (and, for
   * `String.prototype.*`, the receiver) must concretize to a primitive, the id
   * must be in the pure table, and the real JS application must return a
   * primitive. `null` ⇒ caller must degrade visibly.
   */
  const tryExactIntrinsic = (id: string, recv: D | null, argVals: ReadonlyArray<D>): D | null => {
    const cz = domain.concretize;
    if (!cz) return null;
    let recvP: Prim = undefined;
    let fn: unknown;
    if (recv !== null) {
      fn = exactStringMethod(id);
      const c = cz.call(domain, recv);
      if (typeof fn !== "function" || !c || typeof c.v !== "string") return null;
      recvP = c.v;
    } else {
      fn = EXACT_PURE_STATICS[id];
      if (typeof fn !== "function") return null;
    }
    const args: Prim[] = [];
    for (const a of argVals) {
      const c = cz.call(domain, a);
      if (!c) return null;
      args.push(c.v);
    }
    try {
      return primToLit((fn as (this: unknown, ...xs: Prim[]) => Prim).apply(recvP, args));
    } catch {
      return null; // a throwing intrinsic (bad `repeat` count, …) is not modeled: degrade
    }
  };

  /** Allocate a fresh array with the given elements, threading the store. */
  function allocArrayWith(
    elems: D,
    oaddr: OAddr<Ctx>,
    store: Store<Ctx, D>,
  ): { ref: D; store: Store<Ctx, D> } {
    const obj: AbsObject<Ctx, D> = {
      shapes: FinSet.of(shapeKey, shapes.fromFields([["length", "num"]])),
      fields: FinMap.fromEntries<PropName, D>(propK, [["length", domain.anyNum()]]),
      accessors: FinMap.empty(propK),
      proto: arrayProtoLink(),
      elements: elems,
    };
    const r = installObj(store.objs, store.counts, oaddr, obj);
    return { ref: domain.objRef(oaddr), store: { ...store, objs: r.objs, counts: r.counts } };
  }

  /**
   * A higher-order Array method (`arr.map(f)`, `arr.reduce(f, init)`, …). Enters the
   * callback `f` with the receiver's (smashed) element value; the *result* is either
   * collected from `f`'s return (`map`), threaded (`reduce`), or produced
   * synchronously while `f` is called for effect (`forEach`/`filter`/…).
   */
  function higherOrderBranch(
    M: AnalysisMonad<Store<Ctx, D>>,
    method: string,
    thisVal: D,
    argVals: ReadonlyArray<D>,
    callLoc: Loc,
    name: Name,
    body: Expr,
    c: ControlState<Ctx>,
    store: Store<Ctx, D>,
  ): Array<Comp<ControlState<Ctx>>> {
    const element = recvElements(thisVal, store.objs);
    const idx = domain.anyNum();
    const undef = domain.lit(litUndef);
    const cbClos = domain.elimClo(argVals[0] ?? DJ.bot).toArray();

    // `map`/`flatMap`: collect the callback's returns into a fresh result array.
    if (method === "map" || method === "flatMap") {
      const raddr: OAddr<Ctx> = { loc: callLoc, time: c.time };
      const { store: st } = allocArrayWith(DJ.bot, raddr, store);
      if (cbClos.length === 0) {
        // Unknown callback: sound fallback — result array of unknown elements.
        const fb = allocArrayWith(DJ.join(element, undef), raddr, store);
        return [bindAndContinue(M, name, fb.ref, body, c.env, c.kaddr, c.time, fb.store)];
      }
      const frame: Kont<Ctx> = { tag: "frame", name, body, env: c.env, time: c.time, next: c.kaddr, collect: raddr };
      return cbClos.map((cl) =>
        enterClosure(M, cl, [element, idx, thisVal], callLoc, callLoc, c.time, st, frame, c.kaddr, null),
      );
    }

    // `reduce`/`reduceRight`: acc = init ⊔ element; the callback's return is the result.
    if (method === "reduce" || method === "reduceRight") {
      const init = argVals.length > 1 ? argVals[1]! : element;
      const acc = DJ.join(init, element);
      if (cbClos.length === 0) return [bindAndContinue(M, name, acc, body, c.env, c.kaddr, c.time, store)];
      const frame: Kont<Ctx> = { tag: "frame", name, body, env: c.env, time: c.time, next: c.kaddr };
      return cbClos.map((cl) =>
        enterClosure(M, cl, [acc, element, idx, thisVal], callLoc, callLoc, c.time, store, frame, c.kaddr, null),
      );
    }

    // The rest: a synchronous result, with the callback called purely for effect
    // (its return discarded). `sort` passes two elements to a comparator.
    let result: D;
    let cbArgs: ReadonlyArray<D>;
    let st = store;
    switch (method) {
      case "forEach":
        result = undef;
        cbArgs = [element, idx, thisVal];
        break;
      case "filter": {
        const a = allocArrayWith(element, { loc: callLoc, time: c.time }, store);
        result = a.ref;
        st = a.store;
        cbArgs = [element, idx, thisVal];
        break;
      }
      case "find":
      case "findLast":
        result = DJ.join(element, undef);
        cbArgs = [element, idx, thisVal];
        break;
      case "findIndex":
        result = domain.anyNum();
        cbArgs = [element, idx, thisVal];
        break;
      case "some":
      case "every":
        result = domain.anyBool();
        cbArgs = [element, idx, thisVal];
        break;
      case "sort":
        result = thisVal;
        cbArgs = [element, element];
        break;
      default:
        return [];
    }
    // Pre-bind the result to `name`, then run the callback with a discard frame that
    // continues to `body` (mirrors setter dispatch); or, with no callback, just bind.
    const addr: Addr<Ctx> = { name, time: c.time };
    const env2 = c.env.set(name, addr);
    const st2: Store<Ctx, D> = { ...st, vals: st.vals.joinAt(DJ, addr, result) };
    if (cbClos.length === 0)
      return [M.bind(M.put(st2), () => M.unit({ control: body, env: env2, kaddr: c.kaddr, time: c.time }))];
    const frame: Kont<Ctx> = { tag: "frame", name: "%discard", body, env: env2, time: c.time, next: c.kaddr };
    return cbClos.map((cl) =>
      enterClosure(M, cl, cbArgs, callLoc, callLoc, c.time, st2, frame, c.kaddr, null),
    );
  }

  /** Numeric constants exposed as data properties on the namespace objects. */
  const MATH_CONSTS: Record<string, number> = {
    PI: Math.PI, E: Math.E, LN2: Math.LN2, LN10: Math.LN10,
    LOG2E: Math.LOG2E, LOG10E: Math.LOG10E, SQRT2: Math.SQRT2, SQRT1_2: Math.SQRT1_2,
  };
  const NUMBER_CONSTS: Record<string, number> = {
    MAX_SAFE_INTEGER: Number.MAX_SAFE_INTEGER, MIN_SAFE_INTEGER: Number.MIN_SAFE_INTEGER,
    MAX_VALUE: Number.MAX_VALUE, MIN_VALUE: Number.MIN_VALUE, EPSILON: Number.EPSILON,
    POSITIVE_INFINITY: Number.POSITIVE_INFINITY, NEGATIVE_INFINITY: Number.NEGATIVE_INFINITY, NaN: NaN,
  };

  /**
   * Seed the initial environment and store with modeled JS globals. Callable-plus-
   * namespace globals (`Number`, `String`, `Array`, `Object`) are the *join* of an
   * intrinsic (so `Number(x)` dispatches) and a statics object (so `Number.isInteger`
   * reads) — the abstract value's independent components make this a non-issue.
   * Pure namespaces (`Math`) are objects only; bare functions (`parseInt`) are
   * intrinsics only. Namespace/statics objects live at synthetic negative locs.
   */
  function seedGlobals(
    env0: Env<Ctx>,
    vals0: FinMap<Addr<Ctx>, D>,
    objs0: FinMap<OAddr<Ctx>, AbsObject<Ctx, D>>,
  ): { env: Env<Ctx>; vals: FinMap<Addr<Ctx>, D>; objs: FinMap<OAddr<Ctx>, AbsObject<Ctx, D>> } {
    let env = env0;
    let vals = vals0;
    let objs = objs0;
    const intr = (id: string): D => domain.intrinsic(id);
    const numC = (n: number): D => domain.lit(litNum(n));
    /** Model ids under `prefix.` become that namespace's method fields (`floor`, …).
     * Only the *immediate* segment matches, so `methodsOf("Array")` is `isArray` and
     * excludes the nested `Array.prototype.*`. */
    const methodsOf = (prefix: string): Array<readonly [string, D]> =>
      [...intrinsicModels.keys()]
        .filter((k) => k.startsWith(`${prefix}.`) && !k.slice(prefix.length + 1).includes("."))
        .map((k) => [k.slice(prefix.length + 1), intr(k)] as const);
    // The seeded library objects are read-only scaffolding — a compiler never lays
    // out `Math`. Give them the megamorphic (⊤) shape so building them does not
    // intern a chain of intermediate shapes (which would otherwise inflate the
    // shape metric by a fixed ~100). Field *values* are still exact, so reads of
    // `Math.PI` / `arr.push` resolve precisely; only the *shape* is coarsened.
    // EXCEPT under a concretizing domain: a ⊤ shape "may lack any key", so every
    // read would join a spurious `undefined` (`Math.PI` ⇒ {π, undefined}) and
    // exactness dies. There the seeded objects get their precise one-shot shape
    // (one interned shape per namespace — no transition chain, and the shape
    // metric is not a measurement artifact for concrete runs).
    const mkObj = (fields: ReadonlyArray<readonly [string, D]>): AbsObject<Ctx, D> => {
      let fmap = FinMap.empty<PropName, D>(propK);
      for (const [k, v] of fields) fmap = fmap.set(k, v);
      const shape = exactMode ? shapes.fromFields(fields.map(([k, v]) => [k, domain.typeSig(v)] as const)) : shapes.top();
      return {
        shapes: FinSet.of(shapeKey, shape),
        fields: fmap,
        accessors: FinMap.empty(propK),
        proto: FinSet.empty(oak),
        elements: DJ.bot,
      };
    };
    const consts = (rec: Record<string, number>): Array<readonly [string, D]> =>
      Object.entries(rec).map(([k, v]) => [k, numC(v)] as const);
    const at = (loc: Loc, obj: AbsObject<Ctx, D>): OAddr<Ctx> => {
      const a: OAddr<Ctx> = { loc, time: time.tzero };
      objs = objs.set(a, obj);
      return a;
    };
    const bind = (name: Name, v: D): void => {
      const addr: Addr<Ctx> = { name, time: time.tzero };
      env = env.set(name, addr);
      vals = vals.joinAt(DJ, addr, v);
    };

    // Prototype objects backing the array/string methods (Phase 2/3), at their fixed
    // synthetic addresses so freshly-allocated arrays can proto-link to them. The
    // higher-order array methods (Phase 3) are added as intrinsic fields even though
    // they have no synchronous `intrinsicModels` entry — the dispatch routes them.
    const hoArrayFields = HIGHER_ORDER_ARRAY.map((m) => [m, intr(`Array.prototype.${m}`)] as const);
    objs = objs.set(ARRAY_PROTO_ADDR, mkObj([...methodsOf("Array.prototype"), ...hoArrayFields]));
    objs = objs.set(STRING_PROTO_ADDR, mkObj(methodsOf("String.prototype")));
    const protoField = (a: OAddr<Ctx>): readonly [string, D] => ["prototype", domain.objRef(a)];

    const mathA = at(-101, mkObj([...methodsOf("Math"), ...consts(MATH_CONSTS)]));
    const numberA = at(-102, mkObj([...methodsOf("Number"), ...consts(NUMBER_CONSTS)]));
    const stringA = at(-103, mkObj([...methodsOf("String"), protoField(STRING_PROTO_ADDR)]));
    const arrayA = at(-104, mkObj([...methodsOf("Array"), protoField(ARRAY_PROTO_ADDR)]));
    const objectA = at(-105, mkObj([]));

    bind("Math", domain.objRef(mathA));
    bind("Number", DJ.join(intr("Number"), domain.objRef(numberA)));
    bind("String", DJ.join(intr("String"), domain.objRef(stringA)));
    bind("Array", DJ.join(intr("Array"), domain.objRef(arrayA)));
    bind("Object", DJ.join(intr("Object"), domain.objRef(objectA)));
    bind("Boolean", intr("Boolean"));
    for (const g of ["parseInt", "parseFloat", "isNaN", "isFinite"]) bind(g, intr(g));
    return { env, vals, objs };
  }

  /**
   * Read `key` from a value, walking the prototype chain: own properties shadow
   * inherited ones; when a property may be absent on an object, the read
   * continues into that object's `proto` link(s). `F.prototype` on a function
   * value resolves to that function's prototype object. A visited-set bounds the
   * walk (the abstract heap is finite, so cycles terminate).
   */
  function readProp(objVal: D, key: PropName, store: Store<Ctx, D>): D {
    // A ⊤ receiver: its objects cannot be enumerated, so any property may hold
    // any value.
    if (domain.isTop(objVal)) return domain.top;
    let result = DJ.bot;

    // An imported function (callable summary): its properties live in another
    // module — any read is any value, never a confident `undefined`.
    if (!domain.elimFnSummary(objVal).isEmpty()) result = DJ.join(result, domain.top);

    // `F.prototype` — a property read on a function value.
    if (key === "prototype") {
      for (const clo of domain.elimClo(objVal)) result = DJ.join(result, domain.objRef(protoAddr(clo.loc)));
    }

    const roots = domain.elimObj(objVal);
    // A ⊥ receiver is no value at all — propagate ⊥, never a made-up `undefined`.
    if (domain.isBottom(objVal)) return DJ.bot;
    // A non-object receiver (with no matching prototype) reads as `undefined`.
    if (roots.isEmpty()) return DJ.lte(result, DJ.bot) ? domain.lit(litUndef) : result;

    const visited = new Set<string>();
    const lookup = (oaddr: OAddr<Ctx>): D => {
      const vk = oak.key(oaddr);
      if (visited.has(vk)) return DJ.bot;
      visited.add(vk);
      const obj = store.objs.getOr(oaddr, objLat.bot);
      let r = DJ.bot;
      // A megamorphic (⊤) shape may have any key AND may lack it — read the (still
      // precise) field map, and also continue up the chain / to undefined.
      const hasKey = obj.shapes.toArray().some((s) => isMegamorphic(s) || shapeHas(s, key));
      const mayLack = obj.shapes.isEmpty() || obj.shapes.toArray().some((s) => isMegamorphic(s) || !shapeHas(s, key));
      if (hasKey) r = DJ.join(r, obj.fields.getOr(key, DJ.bot)); // own property shadows the chain
      if (mayLack) {
        // An OPEN object may carry untracked fields (a checked-tier import —
        // other modules can mutate it): a miss is any value, never a
        // closed-world `undefined`.
        if (obj.open) r = DJ.join(r, domain.top);
        else if (obj.proto.isEmpty()) r = DJ.join(r, domain.lit(litUndef)); // end of chain, not found
        else for (const p of obj.proto) r = DJ.join(r, lookup(p));
      }
      return r;
    };
    for (const oaddr of roots) result = DJ.join(result, lookup(oaddr));
    return result;
  }

  /**
   * Resolve a property over the prototype chain, separating **data** contributions
   * from **accessor** getters/setters — the machine dispatches to accessors as
   * calls, so `get`/`put` need to know which kind they hit. Own properties (data
   * or accessor) shadow inherited ones.
   */
  function resolveProp(
    objVal: D,
    key: PropName,
    store: Store<Ctx, D>,
  ): { data: D; sawUndefined: boolean; getters: D; setters: D } {
    // A ⊤ receiver reads as ⊤ (any property, any value); accessor dispatch on it
    // is not enumerable — the data path carries the whole approximation.
    if (domain.isTop(objVal)) return { data: domain.top, sawUndefined: false, getters: DJ.bot, setters: DJ.bot };
    // A ⊥ receiver is NO value — an unreachable/unbound read, not a real one.
    // Reporting `undefined` here invented a confident value out of nothing
    // (differential-harness containment finding: with intrinsics off, `Math.PI`
    // read as exact `undefined` — a ⊑-direction unsoundness). ⊥ in, ⊥ out: the
    // path dies, downstream nodes report unreached, consumers fail-soft to ⊤.
    if (domain.isBottom(objVal)) return { data: DJ.bot, sawUndefined: false, getters: DJ.bot, setters: DJ.bot };
    let data = DJ.bot;
    let getters = DJ.bot;
    let setters = DJ.bot;
    let sawUndefined = false;

    // an imported function's properties live in another module: any value
    if (!domain.elimFnSummary(objVal).isEmpty()) data = DJ.join(data, domain.top);

    // `F.prototype` on a function value resolves to that function's prototype object.
    if (key === "prototype") {
      for (const clo of domain.elimClo(objVal)) data = DJ.join(data, domain.objRef(protoAddr(clo.loc)));
    }
    if (domain.elimObj(objVal).isEmpty()) {
      // a non-object receiver reads as `undefined`, unless it is `fn.prototype`
      if (!(key === "prototype" && !domain.elimClo(objVal).isEmpty())) sawUndefined = true;
      return { data, sawUndefined, getters, setters };
    }

    const visited = new Set<string>();
    const walk = (oaddr: OAddr<Ctx>): void => {
      const vk = oak.key(oaddr);
      if (visited.has(vk)) return;
      visited.add(vk);
      const obj = store.objs.getOr(oaddr, objLat.bot);
      const hasData = obj.shapes.toArray().some((s) => isMegamorphic(s) || shapeHas(s, key));
      const acc = obj.accessors.getOr(key, { get: DJ.bot, set: DJ.bot });
      const hasAcc = !DJ.lte(acc.get, DJ.bot) || !DJ.lte(acc.set, DJ.bot);
      if (hasData) data = DJ.join(data, obj.fields.getOr(key, DJ.bot));
      if (hasAcc) {
        getters = DJ.join(getters, acc.get);
        setters = DJ.join(setters, acc.set);
      }
      // continue up the chain only if the key may be absent here (no accessor and
      // some shape lacks the data property; a megamorphic shape always may-lack)
      const mayLack =
        !hasAcc && (obj.shapes.isEmpty() || obj.shapes.toArray().some((s) => isMegamorphic(s) || !shapeHas(s, key)));
      if (mayLack) {
        // open object: a miss reads as ⊤, never the closed-world `undefined`
        if (obj.open) data = DJ.join(data, domain.top);
        else if (obj.proto.isEmpty()) sawUndefined = true;
        else for (const p of obj.proto) walk(p);
      }
    };
    for (const oaddr of domain.elimObj(objVal)) walk(oaddr);
    return { data, sawUndefined, getters, setters };
  }

  /**
   * Write `key ↦ val` to every object the value may point to, transitioning each
   * hidden class. Strong update (overwrite) under concrete time; weak update
   * (join field, keep old *and* transitioned shapes) under k-CFA.
   */
  function writeProp(
    objs: FinMap<OAddr<Ctx>, AbsObject<Ctx, D>>,
    counts: FinMap<OAddr<Ctx>, ACount>,
    objVal: D,
    key: PropName,
    val: D,
  ): FinMap<OAddr<Ctx>, AbsObject<Ctx, D>> {
    let out = objs;
    const rep = domain.typeSig(val); // the field's new representation
    for (const oaddr of domain.elimObj(objVal)) {
      const existing = out.getOr(oaddr, objLat.bot);
      const base = existing.shapes.isEmpty() ? FinSet.of(shapeKey, shapes.empty()) : existing.shapes;
      const transitioned = base.map(shapeKey, (s: Shape) => shapes.transition(s, key, rep));
      // Strong update when the address names exactly one concrete object: concrete
      // time, or — under recency/abstract-counting — a statically-known singleton
      // prototype *or* any address whose current count is `ONE`. Replacing rather
      // than accumulating gives a singleton's fields a linear shape chain instead of
      // a 2ᴺ subset powerset. (Count `ONE` is exactly Might & Shivers' condition for
      // a sound strong update: the address summarizes at most one concrete object.)
      if (
        time.singletonAddrs ||
        (recency && oaddr.proto) ||
        (counting && counts.getOr(oaddr, 0) === ONE)
      ) {
        out = out.set(oaddr, {
          shapes: transitioned,
          fields: existing.fields.set(key, val),
          accessors: existing.accessors,
          proto: existing.proto, // writes are own-only; prototype link is unchanged
          elements: existing.elements,
          ...(existing.open ? { open: true } : {}),
        });
      } else {
        // Weak update: keep the old *and* transitioned shapes — but cap the set so
        // an object built up field-by-field can't blow up to a 2ᴺ subset powerset.
        const merged = existing.shapes.union(transitioned);
        const mergedArr = merged.toArray();
        const capped = shapes.capShapeSet(mergedArr, shapeCap);
        if (capped !== mergedArr) capStats.shapeCapHits++;
        out = out.set(oaddr, {
          shapes: capped === mergedArr ? merged : FinSet.fromIterable(shapeKey, capped),
          fields: existing.fields.joinAt(DJ, key, val),
          accessors: existing.accessors,
          proto: existing.proto,
          elements: existing.elements,
          ...(existing.open ? { open: true } : {}),
        });
      }
    }
    return out;
  }

  /**
   * Deliver `v` to every continuation at `kaddr` — the shared tail of a
   * `ret` step.  Also used to return a callable summary's result at a TAIL
   * call (the summary has no body to enter, so the "return" happens at the
   * call itself).
   */
  function returnToKont(
    M: AnalysisMonad<Store<Ctx, D>>,
    v: D,
    kaddr: KAddr<Ctx>,
    store: Store<Ctx, D>,
  ): Comp<ControlState<Ctx>> {
    const konts = store.konts.getOr(kaddr, FinSet.empty(kontK));
    return mplusAll(
      M,
      konts.toArray().map((k): Comp<ControlState<Ctx>> => {
        if (k.tag === "halt") return M.mzero(); // final state: no successor
        // A `collect` frame (`Array.map`) weak-adds the callback's return to
        // the result array's elements and binds *that array* to `name`.
        let objs = store.objs;
        let resultVal: D;
        if (k.collect) {
          const arr = objs.getOr(k.collect, objLat.bot);
          objs = objs.set(k.collect, { ...arr, elements: DJ.join(arr.elements, v) });
          resultVal = domain.objRef(k.collect);
        } else {
          // For a `new` frame the result is the returned value when it is an
          // object, otherwise the freshly-constructed `this` object.
          resultVal = k.newObj && domain.elimObj(v).isEmpty() ? domain.objRef(k.newObj) : v;
        }
        // Restore the caller's time captured in the frame, and bind the
        // returned value in the caller's context (not the callee's).
        const bound = bindVar(k.env, store.vals, k.name, resultVal, k.time);
        const store2: Store<Ctx, D> = {
          vals: bound.vals,
          konts: store.konts,
          objs,
          counts: store.counts,
        };
        const successor: ControlState<Ctx> = {
          control: k.body,
          env: bound.env,
          kaddr: k.next,
          time: k.time,
        };
        return M.bind(M.put(store2), () => M.unit(successor));
      }),
    );
  }

  /**
   * Enter a closure: allocate params at the ticked time, bind args (and `this`),
   * thread store. `ctxLoc` is the context increment fed to `tick` — the call site
   * for call-site sensitivity, the receiver's allocation site for object
   * sensitivity. `siteLoc` identifies the continuation address.
   */
  function enterClosure(
    M: AnalysisMonad<Store<Ctx, D>>,
    clo: Closure<Ctx>,
    argVals: ReadonlyArray<D>,
    siteLoc: Loc,
    ctxLoc: Loc,
    callerTime: Time<Ctx>,
    store: Store<Ctx, D>,
    ret: Kont<Ctx> | null, // null ⇒ tail call (reuse caller's kaddr)
    callerKaddr: KAddr<Ctx>,
    thisVal: D | null, // non-null ⇒ bind `this` (constructor or method call)
  ): Comp<ControlState<Ctx>> {
    const t2 = time.tick(ctxLoc, callerTime);
    recordSpecParams(clo.loc, t2, argVals, clo.params.length); // observe this specialization's params
    let env = clo.env;
    let vals = store.vals;
    for (let i = 0; i < clo.params.length; i++) {
      const p = clo.params[i]!;
      const v = i < argVals.length ? argVals[i]! : domain.lit(litUndef);
      const bound = bindVar(env, vals, p, v, t2);
      env = bound.env;
      vals = bound.vals;
    }
    if (thisVal !== null) {
      // Bind `this` under this function's own per-lambda name (matches how the
      // normalizer names `this` in the body) — so distinct functions' receivers
      // occupy distinct addresses instead of colliding on one global `this`.
      const bound = bindVar(env, vals, thisVarName(clo.loc), thisVal, t2);
      env = bound.env;
      vals = bound.vals;
    }
    let kaddr = callerKaddr;
    let konts = store.konts;
    if (ret !== null) {
      // Pushdown (P4F): key the return address on the *caller's* environment (which
      // `ret` — a frame — carries), so returns match their real caller instead of
      // smearing across every context that shares the call site.
      const normalKaddr: KAddr<Ctx> =
        pushdown && ret.tag === "frame"
          ? { loc: siteLoc, time: t2, envId: ret.env.id }
          : { loc: siteLoc, time: t2 };
      // State cap: bound the distinct contexts a function is entered with. Past the
      // cap, every further caller returns through one *widened* address (their
      // continuations merge there) — returns smear, but the state space stays finite.
      if (stateCap > 0) {
        let set = funcContexts.get(clo.loc);
        if (!set) {
          set = new Set();
          funcContexts.set(clo.loc, set);
        }
        const nk = kak.key(normalKaddr);
        if (set.has(nk) || set.size < stateCap) {
          set.add(nk);
          kaddr = normalKaddr;
        } else {
          capStats.stateCapHits++;
          capStats.stateCapFuncs.add(clo.loc);
          kaddr = { loc: clo.loc, time: time.tzero, w: true };
        }
      } else {
        kaddr = normalKaddr;
      }
      konts = konts.joinAt(kontSetL, kaddr, FinSet.of(kontK, ret));
    }
    const store2: Store<Ctx, D> = { vals, konts, objs: store.objs, counts: store.counts };
    const successor: ControlState<Ctx> = { control: clo.body, env, kaddr, time: t2 };
    return M.bind(M.put(store2), () => M.unit(successor));
  }

  /**
   * `let x = obj.key; body` — read a property. Fast path (no getter on the chain):
   * bind the data value and continue. Otherwise branch: a data successor plus one
   * **getter call** per getter closure (entered with `this` = the receiver, its
   * return bound to `x`).
   */
  function handleGet(
    M: AnalysisMonad<Store<Ctx, D>>,
    r: Extract<RHS, { tag: "get" }>,
    e: Extract<Expr, { tag: "let" }>,
    c: ControlState<Ctx>,
    store: Store<Ctx, D>,
  ): Comp<ControlState<Ctx>> {
    const objVal = atomEval(r.obj, c.env, store);
    const res = resolveProp(objVal, r.key, store);
    let dataResult = res.data;
    if (res.sawUndefined) dataResult = DJ.join(dataResult, domain.lit(litUndef));
    // `s.length` on a string primitive (differential-harness finding: it read as
    // a confident `undefined` — unsound in BOTH domains). NOT gated on the
    // `intrinsics` knob — string length is core language semantics, and the
    // echojs oracle config runs intrinsics-off. A possibly-string receiver
    // contributes its length: the exact number when the receiver concretizes,
    // `anyNum` otherwise; a receiver that can ONLY be a string drops the bogus
    // `undefined` entirely.
    if (r.key === "length") {
      const tags = domain.typeSig(objVal).split("|");
      if (tags.includes("str")) {
        const exactRecv = domain.concretize?.(objVal);
        const len =
          exactRecv && typeof exactRecv.v === "string" ? domain.lit(litNum(exactRecv.v.length)) : domain.anyNum();
        dataResult = tags.length === 1 ? len : DJ.join(dataResult, len);
      }
    }
    const getters = domain.elimClo(res.getters);
    if (getters.isEmpty()) {
      return bindAndContinue(M, e.name, dataResult, e.body, c.env, c.kaddr, c.time, store);
    }
    const succs: Array<Comp<ControlState<Ctx>>> = [];
    if (!DJ.lte(dataResult, DJ.bot)) {
      succs.push(bindAndContinue(M, e.name, dataResult, e.body, c.env, c.kaddr, c.time, store));
    }
    const frame: Kont<Ctx> = { tag: "frame", name: e.name, body: e.body, env: c.env, time: c.time, next: c.kaddr };
    for (const g of getters.toArray()) {
      recordAccessor(accessorGetSites, r.loc, g.loc);
      succs.push(enterClosure(M, g, [], r.loc, r.loc, c.time, store, frame, c.kaddr, objVal));
    }
    return mplusAll(M, succs);
  }

  /**
   * `let x = (obj.key = v); body` — write a property. Fast path (no setter on the
   * chain): own data write, bind `v`, continue. Otherwise dispatch to each
   * **setter call** (entered with `this` = the receiver and argument `v`); `x` is
   * pre-bound to `v` (the assignment's value) and the setter's return is discarded.
   */
  function handlePut(
    M: AnalysisMonad<Store<Ctx, D>>,
    r: Extract<RHS, { tag: "put" }>,
    e: Extract<Expr, { tag: "let" }>,
    c: ControlState<Ctx>,
    store: Store<Ctx, D>,
  ): Comp<ControlState<Ctx>> {
    const objVal = atomEval(r.obj, c.env, store);
    const v = atomEval(r.val, c.env, store);
    const res = resolveProp(objVal, r.key, store);
    const setters = domain.elimClo(res.setters);
    if (setters.isEmpty()) {
      const store2: Store<Ctx, D> = { ...store, objs: writeProp(store.objs, store.counts, objVal, r.key, v) };
      return bindAndContinue(M, e.name, v, e.body, c.env, c.kaddr, c.time, store2);
    }
    // Pre-bind `x = v`; the setter runs for effect, its return discarded.
    const addr: Addr<Ctx> = { name: e.name, time: c.time };
    const env2 = c.env.set(e.name, addr);
    const store2: Store<Ctx, D> = { ...store, vals: store.vals.joinAt(DJ, addr, v) };
    const frame: Kont<Ctx> = { tag: "frame", name: "%discard", body: e.body, env: env2, time: c.time, next: c.kaddr };
    const succs: Array<Comp<ControlState<Ctx>>> = [];
    for (const s of setters.toArray()) {
      recordAccessor(accessorSetSites, r.loc, s.loc);
      succs.push(enterClosure(M, s, [v], r.loc, r.loc, c.time, store2, frame, c.kaddr, objVal));
    }
    return mplusAll(M, succs);
  }

  function step(M: AnalysisMonad<Store<Ctx, D>>): (c: ControlState<Ctx>) => Comp<ControlState<Ctx>> {
    return (c) =>
      M.bind(M.get(), (store) => {
        const e = c.control;
        switch (e.tag) {
          case "ret": {
            const v = atomEval(e.atom, c.env, store);
            const owner = retOwner.get(e.loc);
            if (owner !== undefined) recordSpecReturn(owner, c.time, v); // observe this specialization's return
            return returnToKont(M, v, c.kaddr, store);
          }

          case "let": {
            const r = e.rhs;
            // Property access can dispatch to an accessor (a call), so it is
            // handled separately from the pure value-producing right-hand sides.
            if (r.tag === "get") return handleGet(M, r, e, c, store);
            if (r.tag === "put") return handlePut(M, r, e, c, store);
            if (r.tag !== "call" && r.tag !== "new" && r.tag !== "method" && r.tag !== "apply") {
              // Every non-call right-hand side produces a value, binds it, and
              // continues to `e.body` in the same continuation — no frame pushed.
              // Bind the name into the environment *before* evaluating an atom RHS
              // so a `let f = (…) => …f…` lambda closes over its own binding
              // (self-recursion); harmless for the other cases.
              const addr: Addr<Ctx> = { name: e.name, time: c.time };
              const env2 = c.env.set(e.name, addr);
              let objs = store.objs;
              let counts = store.counts; // threaded so allocations bump the abstract count
              let vals = store.vals; // threaded so mutating right-hand sides (setVar) can write it
              let v: D;
              switch (r.tag) {
                case "atom":
                  v = atomEval(r.atom, env2, store);
                  break;
                case "un":
                  v = domain.unop(r.op, atomEval(r.arg, c.env, store));
                  break;
                case "bin":
                  v = domain.binop(r.op, atomEval(r.l, c.env, store), atomEval(r.r, c.env, store));
                  break;
                case "setVar": {
                  // Reassign an existing variable: write to its slot in place. Strong
                  // update when addresses are unique (concrete), weak otherwise —
                  // sound because a variable's address is one binding, not a summary.
                  v = atomEval(r.val, c.env, store);
                  const vaddr = c.env.get(r.name);
                  if (vaddr) vals = time.singletonAddrs ? vals.set(vaddr, v) : vals.joinAt(DJ, vaddr, v);
                  break; // (assignment to an unbound name is ignored — no global env yet)
                }
                case "obj": {
                  // Allocate at (site, time); property order + field types fix the
                  // (type-aware) hidden class.
                  const oaddr: OAddr<Ctx> = { loc: r.loc, time: c.time };
                  let fields = FinMap.empty<PropName, D>(propK);
                  const typed: Array<readonly [PropName, string]> = [];
                  for (const [k, ae] of r.fields) {
                    const fv = atomEval(ae, c.env, store);
                    fields = fields.joinAt(DJ, k, fv);
                    typed.push([k, domain.typeSig(fv)]);
                  }
                  const shape = shapes.fromFields(typed);
                  ({ objs, counts } = installObj(objs, counts, oaddr, {
                    shapes: FinSet.of(shapeKey, shape),
                    fields,
                    accessors: FinMap.empty(propK),
                    proto: FinSet.empty(oak), // object literals: no prototype (Object.prototype not modeled)
                    elements: DJ.bot,
                  }));
                  v = domain.objRef(oaddr);
                  break;
                }
                case "shapedTop": {
                  // A checked-tier import summary's object: the DECLARED hidden
                  // class (name + representation per field, re-interned locally)
                  // with every field value ⊤ — the shape is a guardable fact,
                  // the values deliberately are not (another module may mutate
                  // the underlying object; see core.ts ImportSummary.shape).
                  const oaddr: OAddr<Ctx> = { loc: r.loc, time: c.time };
                  let fields = FinMap.empty<PropName, D>(propK);
                  for (const [k] of r.fields) fields = fields.joinAt(DJ, k, domain.top);
                  const shape = shapes.fromFields(r.fields);
                  ({ objs, counts } = installObj(objs, counts, oaddr, {
                    shapes: FinSet.of(shapeKey, shape),
                    fields,
                    accessors: FinMap.empty(propK),
                    proto: FinSet.empty(oak),
                    elements: DJ.bot,
                    open: true, // other modules may add fields we can't see
                  }));
                  v = domain.objRef(oaddr);
                  break;
                }
                case "objectCreate": {
                  // Allocate a fresh object with the given prototype (no own fields).
                  const oaddr: OAddr<Ctx> = { loc: r.loc, time: c.time };
                  const proto = domain.elimObj(atomEval(r.proto, c.env, store));
                  ({ objs, counts } = installObj(objs, counts, oaddr, {
                    shapes: FinSet.of(shapeKey, shapes.empty()),
                    fields: FinMap.empty(propK),
                    accessors: FinMap.empty(propK),
                    proto,
                    elements: DJ.bot,
                  }));
                  v = domain.objRef(oaddr);
                  break;
                }
                case "array": {
                  // An array literal: an object with all elements smashed into the
                  // `elements` bucket, plus a `length` data property.
                  const oaddr: OAddr<Ctx> = { loc: r.loc, time: c.time };
                  let elems: D = DJ.bot;
                  for (const ae of r.elems) elems = DJ.join(elems, atomEval(ae, c.env, store));
                  const len = domain.lit(litNum(r.elems.length));
                  ({ objs, counts } = installObj(objs, counts, oaddr, {
                    shapes: FinSet.of(shapeKey, shapes.fromFields([["length", domain.typeSig(len)]])),
                    fields: FinMap.fromEntries<PropName, D>(propK, [["length", len]]),
                    accessors: FinMap.empty(propK),
                    proto: arrayProtoLink(), // link to `Array.prototype` so `.push`/`.slice` resolve
                    elements: elems,
                  }));
                  v = domain.objRef(oaddr);
                  break;
                }
                case "getDyn": {
                  // Computed read `obj[e]`: always the element bucket ⊔ undefined.
                  // A purely-numeric key is an array index (elements only); a
                  // string/unknown key may also hit any named field.
                  const numericKey = domain.typeSig(atomEval(r.keyExpr, c.env, store)) === "num";
                  const objV = atomEval(r.obj, c.env, store);
                  // ⊥ receiver: no value, not "undefined" (cf. resolveProp).
                  let out = domain.isBottom(objV) ? DJ.bot : domain.lit(litUndef);
                  if (domain.isTop(objV) || !domain.elimFnSummary(objV).isEmpty())
                    out = DJ.join(out, domain.top); // unknown receiver: any value
                  for (const oaddr of domain.elimObj(objV)) {
                    const o = objs.getOr(oaddr, objLat.bot);
                    out = DJ.join(out, o.elements);
                    if (!numericKey) for (const fv of o.fields.values()) out = DJ.join(out, fv);
                    if (o.open) out = DJ.join(out, domain.top); // untracked fields may exist
                  }
                  v = out;
                  break;
                }
                case "putDyn": {
                  // Computed write `obj[e] = v`: weak-write into the element bucket.
                  const pv = atomEval(r.val, c.env, store);
                  for (const oaddr of domain.elimObj(atomEval(r.obj, c.env, store))) {
                    const existing = objs.getOr(oaddr, objLat.bot);
                    objs = objs.set(oaddr, { ...existing, elements: DJ.join(existing.elements, pv) });
                  }
                  v = pv;
                  break;
                }
                case "keys": {
                  // `for-in`: the enumerable property *names* of `obj`, own +
                  // inherited, as an abstract string value. Named fields/accessors
                  // contribute their name constants; array-like objects (non-⊥
                  // element bucket) contribute `⊤`-string (any index).
                  let out: D = DJ.bot;
                  const visited = new Set<string>();
                  const collect = (oaddr: OAddr<Ctx>): void => {
                    const vk = oak.key(oaddr);
                    if (visited.has(vk)) return;
                    visited.add(vk);
                    const o = objs.getOr(oaddr, objLat.bot);
                    for (const name of o.fields.keys()) out = DJ.join(out, domain.lit(litStr(name)));
                    for (const name of o.accessors.keys()) out = DJ.join(out, domain.lit(litStr(name)));
                    if (!DJ.lte(o.elements, DJ.bot)) out = DJ.join(out, domain.topString());
                    if (o.open) out = DJ.join(out, domain.topString()); // untracked enumerable names
                    for (const p of o.proto) collect(p);
                  };
                  const keysObjV = atomEval(r.obj, c.env, store);
                  // An unknown receiver may have any enumerable key (keys are
                  // always strings, so ⊤-string is the precise degradation).
                  if (domain.isTop(keysObjV) || !domain.elimFnSummary(keysObjV).isEmpty())
                    out = DJ.join(out, domain.topString());
                  for (const oaddr of domain.elimObj(keysObjV)) collect(oaddr);
                  v = out;
                  break;
                }
                case "iterElem": {
                  // What `for-of` (or an array-pattern rest) binds per iteration:
                  // the join of the element buckets of the arrays `obj` may be.
                  // Anything whose elements are untracked — an unknown value, a
                  // closure (generator), an object with a ⊥ element bucket (a
                  // possibly-non-array iterable, or a genuinely empty array) —
                  // degrades to ⊤ and counts as an unknown-call-class event.
                  const src = atomEval(r.obj, c.env, store);
                  let out: D = DJ.bot;
                  let degraded =
                    domain.isTop(src) || !domain.elimClo(src).isEmpty() || !domain.elimFnSummary(src).isEmpty();
                  for (const oaddr of domain.elimObj(src)) {
                    const o = objs.getOr(oaddr, objLat.bot);
                    if (DJ.lte(o.elements, DJ.bot)) degraded = true;
                    else out = DJ.join(out, o.elements);
                  }
                  // Closures in the element join are the fingerprint of a
                  // non-array object whose bucket was filled by computed writes
                  // (`o[k] = fn`) — possibly a hand-rolled iterable whose real
                  // iteration yields something else. Degrade. (Cost: for-of
                  // over a genuine array OF FUNCTIONS also degrades to ⊤.)
                  if (!domain.elimClo(out).isEmpty()) degraded = true;
                  // Strings are iterable; their elements are (some) strings.
                  if (!domain.isTop(src) && domain.typeSig(src).split("|").includes("str"))
                    out = DJ.join(out, domain.topString());
                  if (degraded) {
                    recordUnknownCall(r.loc);
                    out = DJ.join(out, domain.top);
                  }
                  v = out;
                  break;
                }
                case "defineAccessor": {
                  // Install a getter/setter accessor property on the target(s).
                  const objVal = atomEval(r.obj, c.env, store);
                  const getV = r.getter ? atomEval(r.getter, c.env, store) : DJ.bot;
                  const setV = r.setter ? atomEval(r.setter, c.env, store) : DJ.bot;
                  for (const oaddr of domain.elimObj(objVal)) {
                    const existing = objs.getOr(oaddr, objLat.bot);
                    const prev = existing.accessors.getOr(r.key, { get: DJ.bot, set: DJ.bot });
                    const slot = { get: DJ.join(prev.get, getV), set: DJ.join(prev.set, setV) };
                    objs = objs.set(oaddr, { ...existing, accessors: existing.accessors.set(r.key, slot) });
                  }
                  v = domain.lit(litUndef);
                  break;
                }
                case "setProto": {
                  // Set each target object's prototype link (weak-joins under k-CFA).
                  const objVal = atomEval(r.obj, c.env, store);
                  const proto = domain.elimObj(atomEval(r.proto, c.env, store));
                  for (const oaddr of domain.elimObj(objVal)) {
                    const existing = objs.getOr(oaddr, objLat.bot);
                    objs = objs.set(oaddr, { ...existing, proto: existing.proto.union(proto) });
                  }
                  v = objVal; // `Object.setPrototypeOf` returns the object
                  break;
                }
              }
              const store2: Store<Ctx, D> = {
                vals: vals.joinAt(DJ, addr, v),
                konts: store.konts,
                objs,
                counts,
              };
              const successor: ControlState<Ctx> = {
                control: e.body,
                env: env2,
                kaddr: c.kaddr,
                time: c.time,
              };
              return M.bind(M.put(store2), () => M.unit(successor));
            }
            // non-tail call: `call` (free function), `new` (constructor), or
            // `method` (dispatch on a receiver). Each pushes a frame to `e.body`.
            const argVals = r.args.map((a) => atomEval(a, c.env, store));
            // Graceful degradation for calls whose callee resolves to *no* closure
            // (an unmodeled runtime builtin — `Math.floor`, `new Array()`, the
            // Octane `BenchmarkSuite` harness, …): rather than kill the path
            // (`mzero`), bind the result to a degraded value and continue. This is
            // deliberately imprecise (an unknown callee could return anything and
            // could mutate the heap) but is what lets the analyzer run on real code.
            const degrade = (value: D, st: Store<Ctx, D>): Comp<ControlState<Ctx>> => {
              const addr: Addr<Ctx> = { name: e.name, time: c.time };
              const env2 = c.env.set(e.name, addr);
              const st2: Store<Ctx, D> = {
                vals: st.vals.joinAt(DJ, addr, value),
                konts: st.konts,
                objs: st.objs,
                counts: st.counts,
              };
              return M.bind(M.put(st2), () => M.unit({ control: e.body, env: env2, kaddr: c.kaddr, time: c.time }));
            };
            const baseFrame = {
              tag: "frame" as const,
              name: e.name,
              body: e.body,
              env: c.env,
              time: c.time, // capture caller's context for restoration on return
              next: c.kaddr,
            };

            if (r.tag === "apply") {
              // `fn.call(thisArg, ...args)` / `%constructSuper` — invoke `fn` with
              // an explicit `this` and no fresh allocation (super-constructor and
              // super-method calls lower to this).
              const fnVal = atomEval(r.fn, c.env, store);
              const thisVal = atomEval(r.thisArg, c.env, store);
              const clos = domain.elimClo(fnVal).toArray();
              // callable summaries: bind the ⊤-argument result (still an
              // open-world call — recordSummarizedCall counts both ways)
              const sumBranches = domain
                .elimFnSummary(fnVal)
                .toArray()
                .map((fs) => {
                  recordSummarizedCall(r.loc);
                  const res = fnSummaryResult(fs, r.loc, c.time, store.objs, store.counts);
                  return degrade(res.v, { ...store, objs: res.objs, counts: res.counts });
                });
              if (clos.length === 0 && sumBranches.length === 0) {
                recordUnknownCall(r.loc);
                return degrade(domain.top, store); // unknown callee could return anything
              }
              return mplusAll(M, [
                ...sumBranches,
                ...clos.map((clo) =>
                  enterClosure(M, clo, argVals, r.loc, r.loc, c.time, store, baseFrame, c.kaddr, thisVal),
                ),
              ]);
            }

            if (r.tag === "method") {
              // `obj.key(args)`: for each possible receiver object, read its method
              // and enter with `this` bound to that receiver. Under object
              // sensitivity the context increment is the receiver's allocation
              // site, so the method is analyzed per receiver class.
              const objVal = atomEval(r.obj, c.env, store);
              const branches: Array<Comp<ControlState<Ctx>>> = [];
              for (const recv of domain.elimObj(objVal).toArray()) {
                const thisVal = domain.objRef(recv);
                const methodVal = readProp(thisVal, r.key, store);
                const ctxLoc = context === "object" ? recv.loc : r.loc;
                for (const clo of domain.elimClo(methodVal).toArray()) {
                  branches.push(
                    enterClosure(M, clo, argVals, r.loc, ctxLoc, c.time, store, baseFrame, c.kaddr, thisVal),
                  );
                }
                // a method slot holding a callable summary (a namespace's
                // function field): bind its ⊤-argument result
                for (const fs of domain.elimFnSummary(methodVal).toArray()) {
                  recordSummarizedCall(r.loc);
                  const res = fnSummaryResult(fs, r.loc, c.time, store.objs, store.counts);
                  branches.push(degrade(res.v, { ...store, objs: res.objs, counts: res.counts }));
                }
                // A modeled intrinsic method resolved through the prototype chain
                // (`Math.floor` on the namespace object, `arr.push` on `Array.prototype`):
                // dispatch its summary synchronously, passing the receiver so mutating
                // array methods can weak-update its `elements` bucket.
                if (intrinsics)
                  for (const id of domain.elimIntrinsic(methodVal)) {
                    // Exactness contract: compute the real result or degrade
                    // visibly — never apply a summary under a concretizing domain.
                    if (exactMode) {
                      const ev = tryExactIntrinsic(id, null, argVals);
                      if (ev !== null) branches.push(degrade(ev, store));
                      else {
                        recordUnknownCall(r.loc);
                        branches.push(degrade(domain.top, store));
                      }
                      continue;
                    }
                    // Higher-order array methods (Phase 3) spawn a real callback call.
                    if (id.startsWith("Array.prototype.")) {
                      const m = id.slice("Array.prototype.".length);
                      if (higherOrderArray.has(m)) {
                        branches.push(...higherOrderBranch(M, m, thisVal, argVals, r.loc, e.name, e.body, c, store));
                        continue;
                      }
                    }
                    const model = intrinsicModels.get(id);
                    if (!model) continue;
                    const oaddr: OAddr<Ctx> = { loc: r.loc, time: c.time };
                    const eff = model({ args: argVals, recv: thisVal, oaddr, objs: store.objs, counts: store.counts });
                    branches.push(degrade(eff.value, { ...store, objs: eff.objs, counts: eff.counts }));
                  }
              }
              // String primitives have no object address to walk, so their prototype
              // methods (`s.charCodeAt`, `s.slice`) are dispatched directly when the
              // receiver may be a string and the key names a modeled method.
              if (intrinsics && domain.typeSig(objVal).split("|").includes("str")) {
                const id = `String.prototype.${r.key}`;
                if (exactMode) {
                  // Known method: exact application or visible degradation. An
                  // unknown key falls through to the branches-empty degrade below.
                  if (intrinsicModels.has(id)) {
                    const ev = tryExactIntrinsic(id, objVal, argVals);
                    if (ev !== null) branches.push(degrade(ev, store));
                    else {
                      recordUnknownCall(r.loc);
                      branches.push(degrade(domain.top, store));
                    }
                  }
                } else {
                  const model = intrinsicModels.get(id);
                  if (model) {
                    const oaddr: OAddr<Ctx> = { loc: r.loc, time: c.time };
                    const eff = model({ args: argVals, recv: objVal, oaddr, objs: store.objs, counts: store.counts });
                    branches.push(degrade(eff.value, { ...store, objs: eff.objs, counts: eff.counts }));
                  }
                }
              }
              // No resolvable method (receiver isn't a tracked object, or the
              // property holds no closure) ⇒ degrade rather than abort.
              if (branches.length === 0) {
                recordUnknownCall(r.loc);
                return degrade(domain.top, store); // unknown method could return anything
              }
              return mplusAll(M, branches);
            }

            // `call` or `new`
            const fv = atomEval(r.fn, c.env, store);
            // Modeled standard-library intrinsics: dispatch to a summary transfer
            // function (synchronous — compute the result, bind it, continue) instead
            // of degrading. `Array`/`Object` allocate; `Math.*`/`parseInt` are pure.
            const intrBranches: Array<Comp<ControlState<Ctx>>> = [];
            if (intrinsics) {
              for (const id of domain.elimIntrinsic(fv)) {
                if (exactMode) {
                  // Exactness contract: only a pure `call` computes (a `new
                  // Number(3)` is a wrapper *object*, not the primitive — never
                  // "exact"); anything else falls through to the unknown-callee
                  // degrade below (targets is empty for a pure intrinsic).
                  const ev = r.tag === "call" ? tryExactIntrinsic(id, null, argVals) : null;
                  if (ev !== null) intrBranches.push(degrade(ev, store));
                  continue;
                }
                const model = intrinsicModels.get(id);
                if (!model) continue;
                const oaddr: OAddr<Ctx> = { loc: r.loc, time: c.time };
                const eff = model({ args: argVals, recv: DJ.bot, oaddr, objs: store.objs, counts: store.counts });
                intrBranches.push(degrade(eff.value, { ...store, objs: eff.objs, counts: eff.counts }));
              }
            }
            let store1 = store;
            let thisVal: D | null = null;
            let newObj: OAddr<Ctx> | null = null;
            if (r.tag === "new") {
              newObj = { loc: r.loc, time: c.time };
              // Link the instance's prototype to each constructor's prototype
              // object, so inherited methods/properties resolve up the chain.
              let proto = FinSet.empty<OAddr<Ctx>>(oak);
              for (const clo of domain.elimClo(fv).toArray()) {
                proto = proto.add(protoAddr(clo.loc));
                recordConstructor(clo.loc, r.loc);
              }
              const empty: AbsObject<Ctx, D> = {
                shapes: FinSet.of(shapeKey, shapes.empty()),
                fields: FinMap.empty(propK),
                accessors: FinMap.empty(propK),
                proto,
                elements: DJ.bot,
              };
              const alloc = installObj(store.objs, store.counts, newObj, empty);
              store1 = { ...store, objs: alloc.objs, counts: alloc.counts };
              thisVal = domain.objRef(newObj);
            }
            const frame: Kont<Ctx> = newObj ? { ...baseFrame, newObj } : baseFrame;
            const targets = domain.elimClo(fv).toArray();
            // Callable summaries dispatch for plain calls only: `new` through an
            // imported function has construct semantics the ⊤-argument result
            // doesn't describe (this-binding, prototype) — it stays a plain
            // unknown callee.
            const sumBranches =
              r.tag === "call"
                ? domain
                    .elimFnSummary(fv)
                    .toArray()
                    .map((fs) => {
                      recordSummarizedCall(r.loc);
                      const res = fnSummaryResult(fs, r.loc, c.time, store1.objs, store1.counts);
                      return degrade(res.v, { ...store1, objs: res.objs, counts: res.counts });
                    })
                : [];
            if (targets.length === 0) {
              // If an intrinsic or summary handled it, take those branches;
              // otherwise it is a genuine unknown callee — record and degrade.
              if (intrBranches.length > 0 || sumBranches.length > 0)
                return mplusAll(M, [...intrBranches, ...sumBranches]);
              recordUnknownCall(r.loc);
              // An unknown callee — plain call or `new` — could return anything
              // (⊤). Binding the freshly-allocated `this` for an unknown `new`
              // would be worse than ⊤: every property read on that empty object
              // resolves to a confident `undefined`. (The orphan allocation may
              // remain in the heap; nothing references it.)
              return degrade(domain.top, store1);
            }
            return mplusAll(M, [
              ...intrBranches,
              ...sumBranches,
              ...targets.map((clo) =>
                enterClosure(M, clo, argVals, r.loc, r.loc, c.time, store1, frame, c.kaddr, thisVal),
              ),
            ]);
          }

          case "letrec": {
            // Mutually-recursive bindings: allocate every address first, extend
            // the environment with all of them, then build each closure over that
            // fully-extended environment so any binding can reference any other.
            let env2 = c.env;
            const addrs: Addr<Ctx>[] = [];
            for (const b of e.bindings) {
              const addr: Addr<Ctx> = { name: b.name, time: c.time };
              addrs.push(addr);
              env2 = env2.set(b.name, addr);
            }
            let vals = store.vals;
            e.bindings.forEach((b, i) => {
              const lam = b.lam;
              if (lam.tag !== "lam") return; // normalizer guarantees lambdas
              const cloVal = domain.clo({
                loc: lam.loc,
                params: lam.params,
                body: lam.body,
                env: env2.restrict(freeVarsOfLam(lam)),
              });
              vals = vals.joinAt(DJ, addrs[i]!, cloVal);
            });
            const store2: Store<Ctx, D> = { vals, konts: store.konts, objs: store.objs, counts: store.counts };
            const successor: ControlState<Ctx> = {
              control: e.body,
              env: env2,
              kaddr: c.kaddr,
              time: c.time,
            };
            return M.bind(M.put(store2), () => M.unit(successor));
          }

          case "if": {
            const cv = atomEval(e.cond, c.env, store);
            return mplusAll(
              M,
              domain
                .elimBool(cv)
                .toArray()
                .map((b): Comp<ControlState<Ctx>> => {
                  const successor: ControlState<Ctx> = {
                    control: b ? e.then : e.else,
                    env: c.env,
                    kaddr: c.kaddr,
                    time: c.time,
                  };
                  return M.unit(successor);
                }),
            );
          }

          case "tailcall": {
            const fv = atomEval(e.fn, c.env, store);
            const argVals = e.args.map((a) => atomEval(a, c.env, store));
            const targets = domain.elimClo(fv).toArray();
            // A callable summary in tail position: the summary has no body to
            // enter, so "returning" its ⊤-argument result happens right here —
            // deliver it to the current continuation (`return f(x)` with an
            // imported `f` no longer kills the path).
            const sumBranches = domain
              .elimFnSummary(fv)
              .toArray()
              .map((fs) => {
                recordSummarizedCall(e.loc);
                const res = fnSummaryResult(fs, e.loc, c.time, store.objs, store.counts);
                return returnToKont(M, res.v, c.kaddr, { ...store, objs: res.objs, counts: res.counts });
              });
            // A tail call with no callee has no `let` body to degrade into —
            // the path simply ends — but record it so `metrics.unknownCalls`
            // still reports the open world.
            if (targets.length === 0 && sumBranches.length === 0) recordUnknownCall(e.loc);
            return mplusAll(M, [
              ...sumBranches,
              ...targets.map((clo) => enterClosure(M, clo, argVals, e.loc, e.loc, c.time, store, null, c.kaddr, null)),
            ]);
          }

          case "throw":
            // Evaluate the operand (atomic — no store effect), then abandon this
            // control path. The nearest `try`'s handler is modeled separately (as a
            // reachable `nondet` alternative), so a throw is simply a dead end here.
            return M.mzero();

          case "nondet":
            // Continue as any alternative (same continuation) — used to make a
            // `try`'s catch handler reachable alongside normal completion.
            return mplusAll(
              M,
              e.alts.map((alt) => M.unit({ control: alt, env: c.env, kaddr: c.kaddr, time: c.time })),
            );
        }
      });
  }

  function isFinal(c: ControlState<Ctx>, store: Store<Ctx, D>): boolean {
    if (c.control.tag !== "ret") return false;
    const konts = store.konts.getOr(c.kaddr, FinSet.empty(kontK));
    return konts.toArray().some((k) => k.tag === "halt");
  }

  function finalValue(c: ControlState<Ctx>, store: Store<Ctx, D>): D {
    if (c.control.tag !== "ret") return DJ.bot;
    return atomEval(c.control.atom, c.env, store);
  }

  /**
   * **Abstract garbage collection** (ΓCFA, Might & Shivers): restrict `store` to
   * the addresses reachable from `c`'s roots — its environment and continuation
   * chain, plus the transitive heap they touch. Unreachable bindings can't affect
   * any future step, so dropping them is sound; it keeps per-control-point stores
   * small (the memory that makes flow-sensitive analysis blow up) and sharpens
   * precision (a dead value no longer merges into a later reuse of its address).
   */
  function gcStore(c: ControlState<Ctx>, store: Store<Ctx, D>): Store<Ctx, D> {
    const liveV = new Set<string>();
    const liveO = new Set<string>();
    const liveK = new Set<string>();
    const vQ: Addr<Ctx>[] = [];
    const oQ: OAddr<Ctx>[] = [];
    const kQ: KAddr<Ctx>[] = [];
    const addV = (a: Addr<Ctx>): void => {
      const k = ak.key(a);
      if (!liveV.has(k)) {
        liveV.add(k);
        vQ.push(a);
      }
    };
    const addO = (o: OAddr<Ctx>): void => {
      const k = oak.key(o);
      if (!liveO.has(k)) {
        liveO.add(k);
        oQ.push(o);
      }
    };
    const addK = (kk: KAddr<Ctx>): void => {
      const k = kak.key(kk);
      if (!liveK.has(k)) {
        liveK.add(k);
        kQ.push(kk);
      }
    };
    // A value's reachable addresses: the environments of the closures it may be,
    // and the objects it may point to.
    const scanVal = (d: D): void => {
      for (const clo of domain.elimClo(d)) for (const [, a] of clo.env) addV(a);
      for (const o of domain.elimObj(d)) addO(o);
    };
    for (const [, a] of c.env) addV(a); // root: the current environment
    addK(c.kaddr); // root: the current continuation
    while (vQ.length > 0 || oQ.length > 0 || kQ.length > 0) {
      while (vQ.length > 0) scanVal(store.vals.getOr(vQ.pop()!, DJ.bot));
      while (oQ.length > 0) {
        const obj = store.objs.getOr(oQ.pop()!, objLat.bot);
        for (const d of obj.fields.values()) scanVal(d);
        scanVal(obj.elements);
        for (const slot of obj.accessors.values()) {
          scanVal(slot.get);
          scanVal(slot.set);
        }
        for (const p of obj.proto) addO(p);
      }
      while (kQ.length > 0) {
        for (const kont of store.konts.getOr(kQ.pop()!, FinSet.empty(kontK))) {
          if (kont.tag === "frame") {
            for (const [, a] of kont.env) addV(a);
            addK(kont.next);
            if (kont.newObj) addO(kont.newObj);
          }
        }
      }
    }
    return {
      vals: store.vals.filterKeys(liveV),
      konts: store.konts.filterKeys(liveK),
      objs: store.objs.filterKeys(liveO),
      // Drop dead addresses' counts too: collecting an object resets its count to
      // `0`, so a *non-escaping* allocation re-run at the same site bumps `0→ONE`
      // again and stays strong-updatable — the Might & Shivers GC⊕counting synergy.
      counts: store.counts.filterKeys(liveO),
    };
  }

  return {
    domain,
    time,
    controlKey,
    storeKey: skey,
    storeLattice: sLat,
    closureKey: closureK,
    shapes,
    constructorTargets,
    accessorGetSites,
    accessorSetSites,
    specObservations: specObs,
    unknownCallSites,
    summarizedCallSites,
    capStats,
    inject,
    step,
    gcStore,
    isFinal,
    finalValue,
  };
}
