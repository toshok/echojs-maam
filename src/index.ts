/**
 * maam-fable — a TypeScript transliteration of MAAM (Monadic Abstract
 * Abstracting Machines), the artifact for "Galois Transformers and Modular
 * Abstract Interpreters" (Darais, Might, Van Horn).
 *
 * Public surface: the algebraic core, the monad framework, the CESK* machine for
 * the restricted-JS dialect, and the {@link analyze} entry point with a set of
 * ready-made analysis presets.
 */

// Algebraic core
export * from "./order.js";
export * from "./lattice.js";
export * from "./lattices.js";
export * from "./galois.js";
export * from "./data/key.js";
export { FinSet, powersetLattice } from "./data/finset.js";
export { FinMap, finMapLattice } from "./data/finmap.js";

// Monad framework
export * from "./monad/monad.js";
export * from "./monad/monads.js";

// CFA machinery
export * from "./time.js";
export * from "./driver.js";

// Language — the surface AST is ESTree; feed any ESTree `Program` to `analyze`.
// `parse` (an acorn convenience for tests/demos) lives in `./lang/parse.js` and
// is intentionally NOT re-exported here, so importing the library never pulls in
// a parser. The host compiler supplies its own ESTree (e.g. from esprima).
export * as ast from "./lang/ast.js";
export { checkRestrictions, assertRestrictions, RestrictionError } from "./lang/restrictions.js";
export type { Violation } from "./lang/restrictions.js";
export { normalizeProgram, NormalizeError } from "./lang/normalize.js";
export type { DegradedBinding } from "./lang/normalize.js";
export * from "./lang/values.js";
export { makeMachine } from "./lang/machine.js";
export type { ContextStrategy, ControlState, Machine } from "./lang/machine.js";
export type { Addr, AbsObject, Closure, Env, KAddr, Kont, OAddr, Store } from "./lang/state.js";
export type { PropName, Shape, TypeSig } from "./lang/shapes.js";
export { ShapeTable, shapeToString } from "./lang/shapes.js";

// Analysis entry point
export * from "./analysis.js";

// Object layout (hidden class → struct)
export * from "./layout.js";

// Presets
import type { Keyable } from "./data/key.js";
import type { AnalysisSpec, Sensitivity } from "./analysis.js";
import type { ContextStrategy } from "./lang/machine.js";
import { concreteTime, kCFATime, zeroCFATime, jsonCtxKey } from "./time.js";
import type { Loc } from "./lang/core.js";
import type { Closure, OAddr } from "./lang/state.js";
import { abstractDomain, concreteDomain } from "./lang/values.js";
import type { AVal, CVal } from "./lang/values.js";
import type { FinSet } from "./data/finset.js";

const locKey: Keyable<Loc> = jsonCtxKey<Loc>();

/**
 * Concrete evaluation: exact values + unbounded context. A faithful interpreter
 * (path-sensitive by default). Only terminates on terminating programs.
 */
export function concreteEval(
  sensitivity: Sensitivity = "path-sensitive",
): AnalysisSpec<FinSet<CVal<Loc>>> {
  return {
    domain: (closureK: Keyable<Closure<Loc>>, oaddrK: Keyable<OAddr<Loc>>) =>
      concreteDomain<Loc>(closureK, oaddrK),
    time: concreteTime<Loc>(locKey),
    sensitivity,
  };
}

/**
 * k-CFA: abstract values (constant propagation + closures) with `k` levels of
 * call-site context. `k = 0` is 0-CFA (context-insensitive, cheapest, coarsest);
 * `k` defaults to **1**, since 0-CFA merges every calling context and is usually
 * too imprecise (e.g. a polymorphic helper collapses to `⊤`). Sensitivity
 * defaults to flow-sensitive, which for this non-relational value domain is as
 * precise as path-sensitive at lower cost. Always terminates.
 */
export function kCFA(
  k = 1,
  sensitivity: Sensitivity = "flow-sensitive",
  context: ContextStrategy = "call-site",
  shapeCap = 0,
  recency = false,
  gc = false,
  pushdown = false,
  stateCap = 0,
  counting = false,
  intrinsics = false,
): AnalysisSpec<AVal<Loc>> {
  return {
    domain: (closureK: Keyable<Closure<Loc>>, oaddrK: Keyable<OAddr<Loc>>) =>
      abstractDomain<Loc>(closureK, oaddrK),
    time: k === 0 ? zeroCFATime<Loc>(locKey) : kCFATime<Loc>(k, locKey),
    sensitivity,
    context,
    shapeCap,
    recency,
    gc,
    pushdown,
    stateCap,
    counting,
    intrinsics,
  };
}
