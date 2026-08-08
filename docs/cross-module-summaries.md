# Cross-module import summaries (design)

2026-08-08.  Status: design + phasing agreed; C1 in progress.

## Problem

Module-goal analysis binds every imported name to `⊤`
(normalize.ts `ImportDeclaration` → `litTop`, recorded as a
`degradedBinding`).  On multi-module programs this is the dominant
precision loss: the echojs self-compile shows `shapeDeclined=unmapped`
for nearly every shape site whose receiver flows through an import,
and `specialized=0` across the board.  Static specialization needs
imports to carry real lattice values.

## Shape of the solution

A **summary fixpoint over the module DAG**, not whole-program
analysis: each module's analysis produces an **export summary** (a
serializable abstract value per exported binding); importers consume
summaries instead of `⊤`.  Whole-program AAM over all modules in one
state space is exactly what module-goal analysis exists to avoid.

Key structural facts:

- The module import graph is almost a DAG.  Analyzing in topological
  order makes "re-analyze importers when a dependency's summary
  changes" degenerate to "analyze in dependency order, once".  Only
  genuine import cycles need Kleene iteration within the SCC (seed
  the cyclic edges at the registry-miss value — `⊤` initially, `⊥`
  once we want the full monotone ascent), and the echojs tree has few
  or none.  The compile driver already visits modules in dependency
  order (gather-imports establishes it), so the echojs integration
  gets the ordering for free.
- Summaries must be **host-neutral and re-internable**.  Shape ids
  are per-analysis; a summary names shapes structurally (field list +
  reprs), and the importing analysis re-interns them.  TypeSig
  strings ("num", "num|str", …) already round-trip for primitives.

## Semantics to get right

- **Live bindings**: ES imports view the exported *binding*, not a
  snapshot.  An exported `let` that is reassigned summarizes as the
  join over every assignment — the export-side analysis already
  computes exactly that join at its final store; extract from there,
  never from the initializer.
- **Exported functions**: phase one summarizes a function export as
  its ⊤-argument result analysis (sound for every caller, loses
  argument-polyvariance).  Context-sensitive summaries are a later
  phase.
- **Escaping mutable objects**: an importer can mutate an exported
  object's shape.  Phase one: summaries for object exports carry
  shapes only when the export-side analysis proves the object's field
  set is closed under the exporting module (no escape into unknown
  calls); otherwise widen to `⊤`-shape with primitive field types
  kept.  Conservative, monotone, cheap to check via the existing
  escape accounting.
- **Cycles / registry misses**: absent summary = today's behavior
  (`⊤` + degradedBinding).  Correctness never depends on the registry
  being complete.

## Plumbing (phases)

- **C1 (maam)**: `analyze(program, spec, hooks?)` grows an optional
  `importValue(source: string, imported: string): ImportSummary |
  undefined` hook.  normalize's ImportDeclaration keeps the current
  `litTop` binding when the hook is absent/misses, and otherwise
  binds a new `Lit {kind:"summary", payload}` that the domains map
  into their lattice (primitives first).  Degraded-binding records
  stay for misses, so the stats keep measuring residual `⊤` imports.
- **C2 (maam)**: `AnalysisResult.summarizeBinding(name):
  ImportSummary` — extract the final-store join for a toplevel
  binding; primitives + closure-arity first, structural shapes next.
- **C3 (echojs)**: oracle.ts keeps a per-compilation registry
  `resolvedModulePath → { exportName → ImportSummary }`, filled after
  each module's analysis (module-info supplies export names; the
  driver's dependency order supplies the fixpoint-free scheduling).
  The ImportDeclaration `source` string resolves through the same
  module resolution the compiler already did — key the registry by
  the RESOLVED identity, not the specifier text.
- **C4**: end-to-end with primitive summaries; success metric =
  `degradedBindings`/`unmapped` counts drop on the self-compile, and
  at least some cross-module `shapeSites` stop declining.
- **C5**: structural shape summaries + re-interning + synthetic
  allocation sites for imported object values.
- **C6**: ⊤-argument function-result summaries; then re-evaluate
  whether context-sensitive export summaries are worth their cost
  against the runtime-IC/PGO alternative.

## Validation discipline

Metric-identity is the wrong gate here (summaries CHANGE results by
design).  Gates instead: maam unit suite; the echojs matrix; the
--types self-compile completing with stats-diff REVIEWED (declines
should only move unmapped→resolved, never resolved→worse); and the
oracle-parity check (node-hosted vs self-hosted stats byte-identical)
which is orthogonal to summaries and must stay green.
