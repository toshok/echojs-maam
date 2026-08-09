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
import type { AExp, Expr, ImportSummary, Loc, Name, RHS } from "./lang/core.js";
import { computeSiteLayouts, defaultSizeOf, structOf, terminalShapes } from "./layout.js";
import type { SiteLayout, SizeOf, StructLayout } from "./layout.js";
import type { DegradedBinding, ImportHooks, LambdaInfo } from "./lang/normalize.js";
import { TOPLEVEL } from "./lang/normalize.js";
import { isMegamorphic, shapeToString } from "./lang/shapes.js";
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
   * **Iteration budget** — the wall-clock safety valve: at most this many
   * driver worklist steps before the exploration throws
   * {@link AnalysisBudgetError} (hosts catch and degrade to "no oracle for
   * this module").  Complements `stateCap` (which bounds the state SPACE):
   * precision growth can make a module's fixpoint legitimately huge, and a
   * host that promised "--types never hangs a compile" needs a hard stop,
   * not a smaller space.  0 = unbounded (default).
   */
  readonly iterationBudget?: number;
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
  /**
   * How many import bindings were bound from a host-supplied summary
   * (cross-module linking) instead of `⊤`.  The precision counterpart of
   * `degradedBindings`: hits resolve, misses degrade and are counted there.
   */
  readonly summaryBindings: number;
  /**
   * The subset of `unknownCalls` sites that dispatched through a callable
   * summary and bound its ⊤-argument result instead of plain `⊤`.  Still
   * open-world calls (effects unmodeled), but no longer informationless.
   */
  readonly summarizedCalls: number;
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
  /**
   * Node-identity receiver-shape query (echojs shapes-plan P4.3): the
   * TERMINAL hidden classes the value of `n` (typically a property access's
   * object node) may point to, joined over every reached configuration —
   * construction intermediates are subsumed away exactly as in
   * {@link layouts}. `undefined` for an unmapped/never-reached node (the
   * node-identity fail-soft); `[]` for a node whose value points at no
   * analyzed object. Guarded consumers need the join, not a per-site value.
   */
  receiverShapesOfNode(n: Node): Shape[] | undefined;
  /**
   * The ordered witness for a shape: its field names in the insertion order
   * of the first transition path that interned it (see
   * `ShapeTable.insertionOrderOf`), or `undefined` for the megamorphic ⊤.
   * An order-sensitive runtime (echojs) interns its guard shapes from this.
   */
  fieldOrderOfShape(s: Shape): readonly string[] | undefined;
  /**
   * The export side of cross-module linking (docs/cross-module-summaries.md):
   * project the final-store join of the toplevel binding source-named `name`
   * to a host-neutral {@link ImportSummary}, for an importing module's
   * analysis to consume through its `importValue` hook.  `undefined` — no
   * summary, the importer binds `⊤` — whenever the projection would not be
   * sound or expressible:
   *
   *  - no such toplevel binding (or its unique name is ambiguous);
   *  - the binding is assigned inside a source function.  A function can be
   *    invoked from OUTSIDE the exporting module (an importer calling an
   *    export) with arguments this analysis never saw, so such assignments
   *    are not covered by the module-local fixpoint.  Toplevel assignments —
   *    including loop bodies, whose scaffolding lambdas only run under
   *    analyzed toplevel control flow — are fully covered;
   *  - the joined value holds something a phase-one summary cannot carry
   *    (closures, objects, intrinsics, bigints, `⊤`), or is `⊥` (unreached).
   */
  summarizeBinding(name: string): ImportSummary | undefined;
  /**
   * The imports whose CHECKED-TIER objects this module's analyzed code
   * mutates (`source#exportName` labels): any shape transition, accessor
   * install, or dynamic write observed on a `shapedTop` site's final heap
   * state.  The empirical trigger for cross-module reanalysis: a module
   * that mutates nothing it imported costs its importers nothing.
   */
  mutatedImports(): string[];
  /**
   * A syntactically-function export's CALLABLE summary, extracted from an
   * export-harness run ({@link analyzeExports}): `{fn: {result}}` with the
   * ⊤-argument result summary when expressible (primitives, or a
   * single-terminal-class object shape), `{fn: {}}` (result `⊤`) otherwise.
   * `undefined` when this analysis carried no harness for `name`.  The host
   * stamps the program-wide `fn.id` (its registry key) before publishing.
   */
  summarizeExport(name: string): ImportSummary | undefined;
  /** A short human-readable summary. */
  describe(): string;
}

/** The cross-module-linking inputs `analyzeCore` needs beyond the core itself. */
export interface SummaryInputs {
  /** Toplevel source name → unique core name (see `normalizeProgram`). */
  readonly toplevelScope?: ReadonlyMap<string, Name>;
  /** How many import bindings the normalizer bound from summaries. */
  readonly summaryBindings?: number;
  /** Checked-tier import sites: synthetic loc → import label + declared shape. */
  readonly importShapeSites?: ReadonlyMap<
    Loc,
    { label: string; fields: ReadonlyArray<{ name: string; sig: string }> }
  >;
  /** Export-harness result bindings (see `normalizeProgram`): name → core names. */
  readonly exportResultNames?: ReadonlyMap<string, ReadonlyArray<Name>>;
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
  summaryInputs?: SummaryInputs,
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

  const budget = spec.iterationBudget ?? 0;
  let collecting: Collecting<ControlState<Loc>, Store<Loc, D>>;
  switch (spec.sensitivity) {
    case "path-sensitive": {
      const M = pathSensitiveMonad<Store<Loc, D>>();
      collecting = exploreConfigs(M, CK, SK, SJ, machine.step(M), c0, s0, budget);
      break;
    }
    case "flow-sensitive": {
      const M = pathSensitiveMonad<Store<Loc, D>>();
      const gc = spec.gc ? (c: ControlState<Loc>, s: Store<Loc, D>) => machine.gcStore(c, s) : undefined;
      collecting = exploreFlowSensitive(M, CK, SK, SJ, machine.step(M), c0, s0, gc, budget);
      break;
    }
    case "flow-insensitive": {
      const M = flowInsensitiveMonad<Store<Loc, D>>(SJ);
      collecting = exploreGlobal(M, CK, SK, SJ, machine.step(M), c0, s0, budget);
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

  // One pass over every config's value store joins each core name's
  // bindings — shared by the node-identity type oracle and the receiver-
  // shape query. Built once, lazily.
  let byNameCache: Map<Name, D> | null = null;
  const joinedByName = (): Map<Name, D> => {
    if (byNameCache) return byNameCache;
    const byName = new Map<Name, D>();
    for (const [, store] of collecting.configs) {
      for (const [addr, v] of store.vals) {
        const prev = byName.get(addr.name);
        byName.set(addr.name, prev === undefined ? v : domain.lattice.join(prev, v));
      }
    }
    byNameCache = byName;
    return byName;
  };

  // The node-identity type oracle: the joined per-name bindings, keyed by
  // source node through the normalizer's node → name map.
  let nodeTypesCache: Map<Node, TypeSig> | null = null;
  const nodeTypes = (): ReadonlyMap<Node, TypeSig> => {
    if (nodeTypesCache) return nodeTypesCache;
    const byName = joinedByName();
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

  // The node-identity receiver-shape query (echojs shapes-plan P4.3): the
  // node's core name's joined value → its objects' shapes, with construction
  // intermediates subsumed (the layouts() terminal filter). Fail-soft:
  // unmapped node → undefined; mapped-but-objectless → [].
  //
  // The terminal filter runs PER OBJECT ADDRESS, not over the joined list
  // (shapes-plan P4.6): an object's own construction intermediates are
  // subsumed by its own terminal, but one receiver class's terminal must
  // not be absorbed by a DIFFERENT class's superset shape — a {x,y}
  // receiver beside a {x,y,z} receiver is a 2-shape site, not a
  // monomorphic {x,y,z} one (the global filter reported exactly that,
  // which made the runtime guard silently miss half the receivers).
  const receiverShapesOfNode = (n: Node): Shape[] | undefined => {
    const name = nodeNames?.get(n);
    if (name === undefined) return undefined;
    const v = joinedByName().get(name);
    if (v === undefined || domain.isBottom(v)) return undefined;
    const seen = new Set<number>();
    const out: Shape[] = [];
    for (const oaddr of domain.elimObj(v)) {
      const obj = heap.get(oaddr);
      if (!obj) continue;
      for (const s of terminalShapes([...obj.shapes])) {
        if (!seen.has(s.id)) {
          seen.add(s.id);
          out.push(s);
        }
      }
    }
    return out;
  };

  const fieldOrderOfShape = (s: Shape): readonly string[] | undefined =>
    machine.shapes.insertionOrderOf(s);

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

  // The names `setVar`-assigned anywhere inside a SOURCE lambda (one with a
  // `lambdaInfo` entry — normalizer scaffolding lambdas for loops/joins have
  // none and only run under analyzed toplevel control flow).  Such a binding's
  // module-local fixpoint may not cover assignments an importer triggers by
  // calling an export, so `summarizeBinding` refuses it.  Without `lambdaInfo`
  // every lambda is conservatively a source lambda.  The walk mirrors
  // `freeVarsOfLam`: the core is a DAG (shared continuations), so each node is
  // visited at most once per mode — a shared spine reachable both outside and
  // inside a lambda needs both visits.
  let assignedUnderLamCache: Set<Name> | null = null;
  const namesAssignedUnderSourceLams = (): Set<Name> => {
    if (assignedUnderLamCache) return assignedUnderLamCache;
    const out = new Set<Name>();
    const visitedOut = new WeakSet<Expr>();
    const visitedIn = new WeakSet<Expr>();
    const isSourceLam = (loc: Loc): boolean => lambdaInfo?.has(loc) ?? true;
    const atom = (a: AExp, inside: boolean): void => {
      if (a.tag === "lam") walkE(a.body, inside || isSourceLam(a.loc));
    };
    const rhs = (r: RHS, inside: boolean): void => {
      switch (r.tag) {
        case "atom":
          return atom(r.atom, inside);
        case "bin":
          atom(r.l, inside);
          return atom(r.r, inside);
        case "un":
          return atom(r.arg, inside);
        case "call":
        case "new":
          atom(r.fn, inside);
          r.args.forEach((a) => atom(a, inside));
          return;
        case "method":
          atom(r.obj, inside);
          r.args.forEach((a) => atom(a, inside));
          return;
        case "apply":
          atom(r.fn, inside);
          atom(r.thisArg, inside);
          r.args.forEach((a) => atom(a, inside));
          return;
        case "obj":
          for (const [, v] of r.fields) atom(v, inside);
          return;
        case "shapedTop":
          return; // declared shape, no operands
        case "array":
          r.elems.forEach((a) => atom(a, inside));
          return;
        case "get":
        case "keys":
        case "iterElem":
          return atom(r.obj, inside);
        case "put":
          atom(r.obj, inside);
          return atom(r.val, inside);
        case "getDyn":
          atom(r.obj, inside);
          return atom(r.keyExpr, inside);
        case "putDyn":
          atom(r.obj, inside);
          atom(r.keyExpr, inside);
          return atom(r.val, inside);
        case "setVar":
          if (inside) out.add(r.name);
          return atom(r.val, inside);
        case "objectCreate":
          return atom(r.proto, inside);
        case "setProto":
          atom(r.obj, inside);
          return atom(r.proto, inside);
        case "defineAccessor":
          atom(r.obj, inside);
          if (r.getter) atom(r.getter, inside);
          if (r.setter) atom(r.setter, inside);
          return;
      }
    };
    const walkE = (e0: Expr, inside: boolean): void => {
      let e = e0;
      while (true) {
        const seen = inside ? visitedIn : visitedOut;
        if (seen.has(e)) return;
        seen.add(e);
        switch (e.tag) {
          case "let":
            rhs(e.rhs, inside);
            e = e.body;
            continue;
          case "ret":
            return atom(e.atom, inside);
          case "letrec":
            for (const b of e.bindings) atom(b.lam, inside);
            e = e.body;
            continue;
          case "if":
            atom(e.cond, inside);
            walkE(e.then, inside);
            e = e.else;
            continue;
          case "tailcall":
            atom(e.fn, inside);
            e.args.forEach((a) => atom(a, inside));
            return;
          case "throw":
            return atom(e.val, inside);
          case "nondet": {
            const alts = e.alts;
            for (let i = 0; i + 1 < alts.length; i++) walkE(alts[i]!, inside);
            if (alts.length === 0) return;
            e = alts[alts.length - 1]!;
            continue;
          }
        }
      }
    };
    walkE(core, false);
    assignedUnderLamCache = out;
    return out;
  };

  // The CHECKED-TIER object extraction: a pure-object binding whose objects
  // settle into exactly ONE terminal hidden class summarizes as that shape —
  // identity only (names + representation sigs, insertion-ordered), no value
  // claims.  Mutability is deliberately NOT an obstacle: importers consume a
  // `shape` summary only through runtime-guarded paths, where a stale shape
  // costs a guard miss, never behavior (see core.ts ImportSummary.shape).
  const shapeSummaryOf = (v: D): ImportSummary | undefined => {
    if (domain.isTop(v) || domain.typeSig(v) !== "obj") return undefined;
    const seen = new Set<number>();
    let terminal: Shape | null = null;
    for (const oaddr of domain.elimObj(v)) {
      const obj = heap.get(oaddr);
      if (!obj) continue;
      for (const s of terminalShapes([...obj.shapes])) {
        if (seen.has(s.id)) continue;
        seen.add(s.id);
        if (terminal !== null) return undefined; // polymorphic: no single class
        terminal = s;
      }
    }
    if (terminal === null || isMegamorphic(terminal) || terminal.fields.length === 0) return undefined;
    const order = machine.shapes.insertionOrderOf(terminal);
    if (!order || order.length !== terminal.fields.length) return undefined;
    const sigByName = new Map(terminal.fields.map((f) => [f.name, f.type]));
    const fields: Array<{ name: string; sig: string }> = [];
    for (const name of order) {
      const sig = sigByName.get(name);
      if (sig === undefined) return undefined;
      fields.push({ name, sig });
    }
    return { shape: fields };
  };

  const summarizeBinding = (name: string): ImportSummary | undefined => {
    if (!domain.toSummary) return undefined;
    const unique = summaryInputs?.toplevelScope?.get(name);
    if (unique === undefined) return undefined;
    if (namesAssignedUnderSourceLams().has(unique)) return undefined;
    const v = joinedByName().get(unique);
    if (v === undefined || domain.isBottom(v)) return undefined;
    const prim = domain.toSummary(v);
    if (prim !== undefined) return prim;
    return shapeSummaryOf(v);
  };

  const summarizeExport = (name: string): ImportSummary | undefined => {
    const resNames = summaryInputs?.exportResultNames?.get(name);
    if (!resNames || resNames.length === 0) return undefined;
    // join the harness call results across every materialized harness copy
    let v = domain.lattice.bot;
    const byName = joinedByName();
    for (const rn of resNames) {
      const x = byName.get(rn);
      if (x !== undefined) v = domain.lattice.join(v, x);
    }
    // ⊥ — the function never returned under ⊤ args (always throws/diverges):
    // still a function, result unclaimed
    if (domain.isBottom(v)) return { fn: {} };
    const prim = domain.toSummary ? domain.toSummary(v) : undefined;
    const result = prim !== undefined ? prim : shapeSummaryOf(v);
    return { fn: { ...(result !== undefined ? { result } : {}) } };
  };

  // Which checked-tier import objects did this module's analyzed code mutate?
  // Compare each `shapedTop` site's final heap state against its declaration:
  // any extra/changed shape (field add or representation change), any accessor
  // install, or any dynamic (elements-bucket) write flags the import.
  const mutatedImports = (): string[] => {
    const sites = summaryInputs?.importShapeSites;
    if (!sites || sites.size === 0) return [];
    const out = new Set<string>();
    for (const [oaddr, obj] of heap) {
      const site = sites.get(oaddr.loc);
      if (!site) continue;
      let mutated = false;
      const shapesArr = [...obj.shapes];
      if (shapesArr.length !== 1) mutated = true;
      else {
        const s = shapesArr[0]!;
        if (isMegamorphic(s) || s.fields.length !== site.fields.length) mutated = true;
        else {
          const want = new Map(site.fields.map((f) => [f.name, f.sig]));
          for (const f of s.fields) {
            if (want.get(f.name) !== f.type) {
              mutated = true;
              break;
            }
          }
        }
      }
      if (!mutated && [...obj.accessors].length > 0) mutated = true;
      if (!mutated && !domain.isBottom(obj.elements)) mutated = true;
      if (mutated) out.add(site.label);
    }
    return [...out].sort();
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
    summaryBindings: summaryInputs?.summaryBindings ?? 0,
    summarizedCalls: machine.summarizedCallSites.size,
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
    receiverShapesOfNode,
    fieldOrderOfShape,
    summarizeBinding,
    summarizeExport,
    mutatedImports,
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
 * `new Function` / `with`.  `hooks.importValue` supplies cross-module linking:
 * imported bindings with a summary bind it instead of `⊤`
 * (docs/cross-module-summaries.md).
 */
export function analyze<D>(program: Program, spec: AnalysisSpec<D>, hooks?: ImportHooks): AnalysisResult<D> {
  assertRestrictions(program);
  const {
    core,
    siteSpans,
    lambdaInfo,
    retOwner,
    lambdaParams,
    degradedBindings,
    nodeNames,
    toplevelScope,
    summaryBindings,
    importShapeSites,
  } = normalizeProgram(program, hooks);
  return analyzeCore(core, spec, siteSpans, lambdaInfo, retOwner, lambdaParams, degradedBindings, nodeNames, {
    toplevelScope,
    summaryBindings,
    importShapeSites,
  });
}

/**
 * The EXPORT-HARNESS analysis (docs/cross-module-summaries.md): normalize
 * with the ⊤-argument harness over the syntactically-function exports and
 * analyze to a fixpoint, for {@link AnalysisResult.summarizeExport}.  Returns
 * `null` when the program has no such exports (nothing to harness — use the
 * plain analysis's summaries alone).
 *
 * Run this SEPARATELY from the plain {@link analyze}: the harness joins `⊤`
 * into exported functions' parameters, so a harness run's node types are
 * deliberately wider — sound for export summaries, too wide for the type
 * oracle the plain run feeds.
 */
export function analyzeExports<D>(
  program: Program,
  spec: AnalysisSpec<D>,
  hooks?: ImportHooks,
): AnalysisResult<D> | null {
  assertRestrictions(program);
  const {
    core,
    siteSpans,
    lambdaInfo,
    retOwner,
    lambdaParams,
    degradedBindings,
    nodeNames,
    toplevelScope,
    summaryBindings,
    importShapeSites,
    exportResultNames,
  } = normalizeProgram(program, hooks, { exportHarness: true });
  if (exportResultNames.size === 0) return null;
  return analyzeCore(core, spec, siteSpans, lambdaInfo, retOwner, lambdaParams, degradedBindings, nodeNames, {
    toplevelScope,
    summaryBindings,
    importShapeSites,
    exportResultNames,
  });
}
