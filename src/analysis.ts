/**
 * The public analysis entry point — where the three orthogonal knobs are chosen
 * and the one definitional interpreter is run to a fixpoint.
 *
 * Pick a **value domain** (concrete / abstract), a **time** (concrete / k-CFA /
 * 0-CFA), and a **sensitivity** (path / flow / flow-insensitive); this module
 * assembles the matching monad + driver and returns the collected result. Every
 * combination reuses the *same* `machine.step`.
 */

import type { Keyable } from "./data/key.js";
import type { Collecting } from "./driver.js";
import { exploreConfigs, exploreFlowSensitive, exploreGlobal } from "./driver.js";
import type { JoinSemilattice } from "./lattice.js";
import { flowInsensitiveMonad, pathSensitiveMonad } from "./monad/monads.js";
import type { TimeDict } from "./time.js";
import type { Node, Program, Span } from "./lang/ast.js";
import type { Expr, Loc, Name } from "./lang/core.js";
import { computeSiteLayouts, defaultSizeOf, structOf, terminalShapes } from "./layout.js";
import type { SiteLayout, SizeOf, StructLayout } from "./layout.js";
import type { DegradedBinding, LambdaInfo } from "./lang/normalize.js";
import { TOPLEVEL } from "./lang/normalize.js";
import { shapeToString } from "./lang/shapes.js";
import type { TypeSig } from "./lang/shapes.js";
import { makeMachine } from "./lang/machine.js";
import type { ContextStrategy, ControlState } from "./lang/machine.js";
import { normalizeProgram } from "./lang/normalize.js";
import { assertRestrictions } from "./lang/restrictions.js";
import type { Closure, OAddr, Store } from "./lang/state.js";
import { addrKey, closureKey, envKey, oaddrKey } from "./lang/state.js";
import type { Shape } from "./lang/shapes.js";
import type { ValDomain } from "./lang/values.js";

/** Which store-relation precision to compute. */
export type Sensitivity = "path-sensitive" | "flow-sensitive" | "flow-insensitive";

/** What a function produces when used as a constructor (`new F()`). */
export interface ConstructorReport {
  /** The constructor function's core location. */
  readonly ctorLoc: Loc;
  /** Source name, if it was a named function. */
  readonly name?: string;
  /** Source span of the constructor function. */
  readonly span?: Span;
  /** The terminal hidden classes its constructed objects settle into. */
  readonly shapes: Shape[];
  /** True when it always produces one class — a single struct to emit. */
  readonly monomorphic: boolean;
  /** A struct layout per produced class. */
  readonly layouts: StructLayout[];
}

/** A diagnostic surfaced by the analysis. */
export interface Warning {
  readonly kind: "polymorphic-constructor" | "polymorphic-function" | "unknown-call" | "degraded-binding";
  readonly message: string;
  readonly span?: Span;
}

/**
 * An accessor-dispatch site: a property read/write that resolves (through the
 * prototype chain) to getter/setter functions. A **monomorphic** site (one
 * target) is a candidate to **inline** the accessor body back to a field load /
 * store, eliminating the call — the payoff of tracking accessors precisely.
 */
export interface AccessorSite {
  readonly site: Loc;
  readonly span?: Span;
  readonly kind: "getter" | "setter";
  /** The getter/setter function locations this site may dispatch to. */
  readonly targets: Loc[];
  /** True when exactly one target ⇒ inlinable. */
  readonly monomorphic: boolean;
}

/** One `(parameter types) → return type` row observed for a function. */
export interface Specialization {
  /** Parameter representation per position (e.g. `["num", "str"]`). */
  readonly params: TypeSig[];
  /** The return representation for those parameter types. */
  readonly returns: TypeSig;
}

/**
 * The type-specialization table for a function — every distinct
 * `(param types) → return type` it exhibits across the analyzed calling contexts.
 * One row ⇒ monomorphic (emit a single specialized version); several rows ⇒
 * candidates for per-signature specialization / a boxed fallback.
 */
export interface SpecializationReport {
  readonly loc: Loc;
  readonly name?: string;
  readonly span?: Span;
  readonly paramNames: string[];
  readonly specializations: Specialization[];
  readonly monomorphic: boolean;
}

/** A fully-specified analysis: the three knobs. */
export interface AnalysisSpec<D> {
  /**
   * Value-domain factory. Receives the closure key and the object-address key,
   * both derived from `time`, so the domain and machine agree on them.
   */
  readonly domain: (closureK: Keyable<Closure<Loc>>, oaddrK: Keyable<OAddr<Loc>>) => ValDomain<Loc, D>;
  /** Time / context abstraction. */
  readonly time: TimeDict<Loc>;
  /** Store-relation sensitivity. */
  readonly sensitivity: Sensitivity;
  /**
   * How calling-context is chosen: `"call-site"` (classic k-CFA, the default) or
   * `"object"` (object sensitivity — a method call's context is the receiver's
   * allocation site).
   */
  readonly context?: ContextStrategy;
  /**
   * Max distinct hidden classes per object address before the set widens to the
   * megamorphic `⊤` class (0 = unbounded). Bounds the field-subset powerset a
   * field-by-field-built object (e.g. a prototype) accrues, so precise-where-few
   * stays sharp while megamorphic outliers stay tractable.
   */
  readonly shapeCap?: number;
  /**
   * Recency: strong-update statically-known singleton objects (function
   * prototypes) rather than weak-accumulating their shapes. This is the precise
   * fix for the prototype-method-table subset explosion, but only takes effect
   * under `"flow-sensitive"` sensitivity (a flow-insensitive store join undoes the
   * strong update). Default `false`.
   */
  readonly recency?: boolean;
  /**
   * Abstract counting (Might & Shivers ΓCFA / Balakrishnan–Reps recency): the
   * generalization of `recency` — strong-update *any* address whose abstract count
   * is `ONE`, not just prototypes. Tracks per-address counts in the store and pairs
   * with `gc` (a collected address resets to count 0). Collapses once-allocated
   * objects' field-init from a 2ᴺ shape powerset to a linear chain. A win for
   * allocation-light code, a cost on allocation-heavy looped code. Flow-sensitive
   * only. Default `false`.
   */
  readonly counting?: boolean;
  /**
   * Model the JS standard library: seed the initial store with `Math`, `Array`,
   * `parseInt`, `String.fromCharCode`, … as intrinsic values with sound summary
   * transfer functions, instead of degrading their calls to `⊤`. A precision and
   * soundness win (removes the degradation over-approximation). Default `false`.
   */
  readonly intrinsics?: boolean;
  /**
   * Abstract garbage collection (ΓCFA): restrict each control point's store to the
   * addresses it can still reach. Keeps per-point stores small — the memory that
   * makes flow-sensitive analysis blow up — and sharpens precision. Only meaningful
   * under `"flow-sensitive"`. Default `false`.
   */
  readonly gc?: boolean;
  /**
   * Pushdown (P4F): exactly-matched call/return via caller-environment-keyed
   * continuation addresses. Collapses the return-flow smearing that grows the state
   * space on deep/recursive call graphs. Default `false`.
   */
  readonly pushdown?: boolean;
  /**
   * **State-widening cap** — the safety valve for a *total* analysis (always
   * terminates in bounded time on any input, at the cost of precision where an
   * input is genuinely explosive). At most this many distinct calling contexts per
   * function; beyond that, a function's calls collapse to one *widened* continuation
   * (returns smear to every caller). Also canonicalizes environments per control
   * point (sound at k=0). Bounds the state space to `locations × (cap+1)`.
   * 0 = unbounded (default).
   */
  readonly stateCap?: number;
}

/** Telemetry about the size of the analysis — the abstract state space it explored. */
export interface AnalysisMetrics {
  /** Distinct control states reached (`Exp × Env × KAddr × Time`). */
  readonly reachedStates: number;
  /** `(control, store)` configurations reached. */
  readonly configs: number;
  /** Driver iterations / worklist rounds to reach the fixpoint. */
  readonly iterations: number;
  /** Value-store addresses `(name, time)` in the final heap summary. */
  readonly storeValAddrs: number;
  /** Object-heap addresses `(loc, time)`. */
  readonly storeObjAddrs: number;
  /** Continuation-store addresses. */
  readonly storeKontAddrs: number;
  /** Distinct hidden classes interned. */
  readonly shapesInterned: number;
  /**
   * Call sites (call/`new`/method/`apply`/tail call) that resolved to no callee
   * (unmodeled externals — builtins, harness, cross-module, unknown intrinsics).
   * Zero in a closed world; non-zero marks where results were degraded rather
   * than computed.
   */
  readonly unknownCalls: number;
  /**
   * Bindings the normalizer bound to a degraded value because the construct is
   * not modeled precisely (e.g. old-esprima rest parameters). Like
   * `unknownCalls`, non-zero means results were degraded, not computed; each is
   * also surfaced as a `degraded-binding` warning.
   */
  readonly degradedBindings: number;
  /**
   * How many calls were routed through a widened (`stateCap`-saturated)
   * continuation address, i.e. convergence was *forced*, not natural. Zero
   * means the cap never fired.
   */
  readonly stateCapHits: number;
  /** Distinct functions whose calling contexts hit the state cap. */
  readonly stateCapFuncs: number;
  /** How many shape sets were collapsed to the megamorphic ⊤ shape by `shapeCap`. */
  readonly shapeCapHits: number;
}

/** The result of running an analysis. */
export interface AnalysisResult<D> {
  readonly spec: { domain: string; time: string; sensitivity: Sensitivity };
  readonly collecting: Collecting<ControlState<Loc>, Store<Loc, D>>;
  /** Size telemetry for the abstract state space. */
  readonly metrics: AnalysisMetrics;
  /** The value(s) the whole program evaluates to (join over final states). */
  readonly result: D;
  /** The value-lattice dictionary, for interpreting `result`/store contents. */
  readonly domain: ValDomain<Loc, D>;
  /** Join of all values bound to any address whose variable name matches. */
  valueOfVar(name: Name): D;
  /** The distinct hidden classes the objects a value may point to can have. */
  shapesOfValue(v: D): Shape[];
  /** The distinct hidden classes reachable from a variable's binding(s). */
  shapesOfVar(name: Name): Shape[];
  /**
   * Per allocation site, the terminal hidden classes and their struct layouts —
   * the direct input to object-layout codegen. `sizeOf` defaults to a 64-bit
   * model; override for your ABI.
   */
  layouts(sizeOf?: SizeOf): SiteLayout[];
  /** The layout of a single allocation site, or `undefined` if it wasn't reached. */
  layoutOf(site: Loc, sizeOf?: SizeOf): SiteLayout | undefined;
  /**
   * For each function used as a constructor (`new F()`), the hidden class(es) its
   * objects settle into — the struct(s) to emit, aggregated across all `new`
   * sites that call it.
   */
  constructors(sizeOf?: SizeOf): ConstructorReport[];
  /**
   * Per function, its `(param types) → return type` specialization table — the
   * direct input to monomorphization / call-site specialization.
   */
  specializations(): SpecializationReport[];
  /**
   * Every property access that dispatched to a getter/setter, with the functions
   * it resolved to — a monomorphic site is inlinable back to a field load/store.
   */
  accessorSites(): AccessorSite[];
  /** Diagnostics — polymorphic constructors and heavily-polymorphic functions. */
  warnings(): Warning[];
  /**
   * The node-identity type oracle: source node → the {@link TypeSig} of the
   * value it evaluates to, JOINED over every reached configuration/context.
   * Keys are the exact node objects fed to {@link analyze} (identity, never
   * structure); nodes the analysis never reached — dead code, or glue the
   * normalizer does not map (literals, template intermediates, loop
   * scaffolding) — are simply absent. Built once, lazily.
   *
   * Join semantics: a node mapped to a declared VARIABLE reports the join of
   * every value that variable ever holds — reassignments included — which may
   * be strictly wider than what the expression itself produces (`var x = 1+2;
   * x = "s"` reports "num|str" for the BinaryExpression). Sound (⊒ actual)
   * for guarded consumption; not a value-at-site reading.
   */
  nodeTypes(): ReadonlyMap<Node, TypeSig>;
  /**
   * {@link nodeTypes} for one node: its joined TypeSig, or `undefined` for a
   * never-reached / unmapped / foreign node (fail-soft — never throws;
   * degradation policy belongs to the consumer).
   */
  typeOfNode(n: Node): TypeSig | undefined;
  /** A short human-readable summary. */
  describe(): string;
}

/** Run an analysis over an already-normalized core expression. */
export function analyzeCore<D>(
  core: Expr,
  spec: AnalysisSpec<D>,
  siteSpans?: ReadonlyMap<Loc, Span>,
  lambdaInfo?: ReadonlyMap<Loc, LambdaInfo>,
  retOwner?: ReadonlyMap<Loc, Loc>,
  lambdaParams?: ReadonlyMap<Loc, ReadonlyArray<string>>,
  degradedBindings?: ReadonlyArray<DegradedBinding>,
  nodeNames?: ReadonlyMap<Node, Name>,
): AnalysisResult<D> {
  // Build the closure key from `time` so the domain and machine agree on it.
  const ak = addrKey<Loc>(spec.time.key);
  const envK = envKey<Loc>();
  const closK = closureKey<Loc>(envK);
  const oak = oaddrKey<Loc>(spec.time.key);
  const domain = spec.domain(closK, oak);
  const machine = makeMachine(
    domain,
    spec.time,
    spec.context ?? "call-site",
    retOwner,
    spec.shapeCap ?? 0,
    spec.recency ?? false,
    spec.counting ?? false,
    spec.pushdown ?? false,
    spec.stateCap ?? 0,
    spec.intrinsics ?? false,
  );

  const { c0, s0 } = machine.inject(core);
  const CK = machine.controlKey;
  const SK = machine.storeKey;
  const SJ: JoinSemilattice<Store<Loc, D>> = machine.storeLattice;

  let collecting: Collecting<ControlState<Loc>, Store<Loc, D>>;
  switch (spec.sensitivity) {
    case "path-sensitive": {
      const M = pathSensitiveMonad<Store<Loc, D>>();
      collecting = exploreConfigs(M, CK, SK, SJ, machine.step(M), c0, s0);
      break;
    }
    case "flow-sensitive": {
      const M = pathSensitiveMonad<Store<Loc, D>>();
      const gc = spec.gc ? (c: ControlState<Loc>, s: Store<Loc, D>) => machine.gcStore(c, s) : undefined;
      collecting = exploreFlowSensitive(M, CK, SK, SJ, machine.step(M), c0, s0, gc);
      break;
    }
    case "flow-insensitive": {
      const M = flowInsensitiveMonad<Store<Loc, D>>(SJ);
      collecting = exploreGlobal(M, CK, SK, SJ, machine.step(M), c0, s0);
      break;
    }
  }

  // Join the returned value over every final (`return`-to-`Halt`) configuration.
  let result = domain.lattice.bot;
  for (const [c, store] of collecting.configs) {
    if (machine.isFinal(c, store)) result = domain.lattice.join(result, machine.finalValue(c, store));
  }

  // Normalization alpha-renames source variables to `name$N`; match either the
  // exact core name or the source base name so callers can query by source name.
  const matchesName = (addrName: string, query: Name): boolean =>
    addrName === query || addrName.startsWith(`${query}$`);

  const valueOfVar = (name: Name): D => {
    let acc = domain.lattice.bot;
    for (const [, store] of collecting.configs) {
      for (const [addr, v] of store.vals) {
        if (matchesName(addr.name, name)) acc = domain.lattice.join(acc, v);
      }
    }
    return acc;
  };

  // The node-identity type oracle: one pass over every config's value store
  // joins each core name's bindings; the normalizer's node → name map then
  // keys those joins by source node. Built once on first query.
  let nodeTypesCache: Map<Node, TypeSig> | null = null;
  const nodeTypes = (): ReadonlyMap<Node, TypeSig> => {
    if (nodeTypesCache) return nodeTypesCache;
    const byName = new Map<Name, D>();
    for (const [, store] of collecting.configs) {
      for (const [addr, v] of store.vals) {
        const prev = byName.get(addr.name);
        byName.set(addr.name, prev === undefined ? v : domain.lattice.join(prev, v));
      }
    }
    const out = new Map<Node, TypeSig>();
    for (const [node, name] of nodeNames ?? []) {
      const v = byName.get(name);
      // A name that never got a binding is unreached (dead code): absent, so
      // `typeOfNode` fail-softs to undefined rather than reporting "never".
      if (v !== undefined && !domain.isBottom(v)) out.set(node, domain.typeSig(v));
    }
    nodeTypesCache = out;
    return out;
  };
  const typeOfNode = (n: Node): TypeSig | undefined => nodeTypes().get(n);

  // The heap summary (join of every store) — objects live here.
  const heap = collecting.store.objs;
  const shapesOfValue = (v: D): Shape[] => {
    const seen = new Set<number>();
    const out: Shape[] = [];
    for (const oaddr of domain.elimObj(v)) {
      const obj = heap.get(oaddr);
      if (!obj) continue;
      for (const s of obj.shapes) {
        if (!seen.has(s.id)) {
          seen.add(s.id);
          out.push(s);
        }
      }
    }
    return out;
  };

  const layouts = (sizeOf: SizeOf = defaultSizeOf): SiteLayout[] =>
    computeSiteLayouts(collecting.store.objs, sizeOf, siteSpans);

  const constructors = (sizeOf: SizeOf = defaultSizeOf): ConstructorReport[] => {
    const reports: ConstructorReport[] = [];
    for (const [ctorLoc, newLocs] of machine.constructorTargets) {
      const shapes: Shape[] = [];
      for (const [addr, obj] of heap) {
        if (newLocs.has(addr.loc)) for (const s of obj.shapes) shapes.push(s);
      }
      const terminals = terminalShapes(shapes);
      const info = lambdaInfo?.get(ctorLoc);
      reports.push({
        ctorLoc,
        ...(info?.name !== undefined ? { name: info.name } : {}),
        ...(info?.span ? { span: info.span } : {}),
        shapes: terminals,
        monomorphic: terminals.length === 1,
        layouts: terminals.map((s) => structOf(s, sizeOf)),
      });
    }
    reports.sort((a, b) => a.ctorLoc - b.ctorLoc);
    return reports;
  };

  const specializations = (): SpecializationReport[] => {
    // Group the raw per-context observations by function loc.
    const byLoc = new Map<Loc, Specialization[]>();
    for (const rec of machine.specObservations.values()) {
      if (rec.loc === TOPLEVEL) continue; // top-level code is not a function
      const row: Specialization = {
        params: rec.params.map((p) => domain.typeSig(p)),
        returns: domain.typeSig(rec.ret),
      };
      const rows = byLoc.get(rec.loc) ?? [];
      rows.push(row);
      byLoc.set(rec.loc, rows);
    }
    const reports: SpecializationReport[] = [];
    for (const [loc, rawRows] of byLoc) {
      // Deduplicate identical (params → returns) signatures.
      const seen = new Map<string, Specialization>();
      for (const row of rawRows) seen.set(`${row.params.join(",")}->${row.returns}`, row);
      const rows = [...seen.values()];
      const info = lambdaInfo?.get(loc);
      reports.push({
        loc,
        ...(info?.name !== undefined ? { name: info.name } : {}),
        ...(info?.span ? { span: info.span } : {}),
        paramNames: [...(lambdaParams?.get(loc) ?? [])],
        specializations: rows,
        monomorphic: rows.length === 1,
      });
    }
    reports.sort((a, b) => a.loc - b.loc);
    return reports;
  };

  const accessorSites = (): AccessorSite[] => {
    const out: AccessorSite[] = [];
    const collect = (m: ReadonlyMap<Loc, ReadonlySet<Loc>>, kind: "getter" | "setter") => {
      for (const [site, targetSet] of m) {
        const targets = [...targetSet].sort((a, b) => a - b);
        const span = siteSpans?.get(site);
        out.push({ site, ...(span ? { span } : {}), kind, targets, monomorphic: targets.length === 1 });
      }
    };
    collect(machine.accessorGetSites, "getter");
    collect(machine.accessorSetSites, "setter");
    out.sort((a, b) => a.site - b.site);
    return out;
  };

  const warnings = (): Warning[] => {
    const out: Warning[] = [];
    for (const c of constructors()) {
      if (c.monomorphic) continue;
      const who = c.name ? `\`${c.name}\`` : c.span ? `at [${c.span.start}..${c.span.end}]` : `loc ${c.ctorLoc}`;
      out.push({
        kind: "polymorphic-constructor",
        message: `constructor ${who} may produce ${c.shapes.length} distinct hidden classes: ${c.shapes
          .map(shapeToString)
          .join(" | ")}`,
        ...(c.span ? { span: c.span } : {}),
      });
    }
    for (const s of specializations()) {
      if (s.monomorphic) continue;
      const who = s.name ? `\`${s.name}\`` : s.span ? `at [${s.span.start}..${s.span.end}]` : `loc ${s.loc}`;
      out.push({
        kind: "polymorphic-function",
        message: `function ${who} has ${s.specializations.length} type specializations: ${s.specializations
          .map((r) => `(${r.params.join(", ")}) → ${r.returns}`)
          .join(" ; ")}`,
        ...(s.span ? { span: s.span } : {}),
      });
    }
    for (const d of degradedBindings ?? []) {
      out.push({
        kind: "degraded-binding",
        message: `binding \`${d.name}\` holds a degraded value: ${d.reason}.`,
        ...(d.span ? { span: d.span } : {}),
      });
    }
    if (machine.unknownCallSites.size > 0) {
      out.push({
        kind: "unknown-call",
        message: `${machine.unknownCallSites.size} call site(s) resolved to no callee (unmodeled external — builtin, harness, cross-module, or unknown intrinsic); their results were degraded. In a closed-world AOT program this should be 0.`,
      });
    }
    return out;
  };

  const metrics: AnalysisMetrics = {
    reachedStates: collecting.reached.size,
    configs: collecting.configs.size,
    iterations: collecting.iterations,
    storeValAddrs: collecting.store.vals.size,
    storeObjAddrs: collecting.store.objs.size,
    storeKontAddrs: collecting.store.konts.size,
    unknownCalls: machine.unknownCallSites.size,
    degradedBindings: degradedBindings?.length ?? 0,
    shapesInterned: machine.shapes.size,
    stateCapHits: machine.capStats.stateCapHits,
    stateCapFuncs: machine.capStats.stateCapFuncs.size,
    shapeCapHits: machine.capStats.shapeCapHits,
  };

  const describeSpec = { domain: domain.name, time: spec.time.name, sensitivity: spec.sensitivity };

  return {
    spec: describeSpec,
    collecting,
    metrics,
    result,
    domain,
    valueOfVar,
    nodeTypes,
    typeOfNode,
    shapesOfValue,
    shapesOfVar: (name) => shapesOfValue(valueOfVar(name)),
    layouts,
    layoutOf: (site, sizeOf = defaultSizeOf) => layouts(sizeOf).find((l) => l.site === site),
    constructors,
    specializations,
    accessorSites,
    warnings,
    describe() {
      return (
        `analysis: ${describeSpec.sensitivity} · ${describeSpec.time} · ${describeSpec.domain}\n` +
        `  strategy:    ${collecting.strategy}\n` +
        `  iterations:  ${metrics.iterations}\n` +
        `  states:      ${metrics.reachedStates}\n` +
        `  configs:     ${metrics.configs}\n` +
        `  store:       ${metrics.storeValAddrs} vals · ${metrics.storeObjAddrs} objs · ${metrics.storeKontAddrs} konts\n` +
        `  shapes:      ${metrics.shapesInterned}\n` +
        `  caps:        stateCap ${metrics.stateCapHits} hit(s) across ${metrics.stateCapFuncs} function(s) · shapeCap ${metrics.shapeCapHits} hit(s)`
      );
    },
  };
}

/**
 * Validate a program against the dialect restrictions, normalize it, and analyze
 * it. Throws {@link RestrictionError} if the program uses `eval` /
 * `new Function` / `with`.
 */
export function analyze<D>(program: Program, spec: AnalysisSpec<D>): AnalysisResult<D> {
  assertRestrictions(program);
  const { core, siteSpans, lambdaInfo, retOwner, lambdaParams, degradedBindings, nodeNames } =
    normalizeProgram(program);
  return analyzeCore(core, spec, siteSpans, lambdaInfo, retOwner, lambdaParams, degradedBindings, nodeNames);
}
