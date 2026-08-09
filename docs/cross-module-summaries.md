# Cross-module import summaries (design)

2026-08-08.  Status: **C1–C4 landed** (primitive summaries end-to-end);
C5 (structural shapes) and C6 (function results) are next.  Measured
findings from the first self-compile are at the bottom.

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
  or none.  (The design's original claim that the driver already
  compiled in dependency order was WRONG — it compiled main-first.
  ejs-es6.ts now topologically orders the compile, dependencies before
  importers, with cycle back-edges falling back to registry misses.)
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
  allocation sites for imported object values.  **Landed 2026-08-08 as
  NAMESPACE-object summaries** (the measured dominant case): the
  registry synthesizes, per module, an object summary whose exact field
  set is the module's export names — immutability comes from the SPEC
  (module namespace objects are frozen), not from escape analysis — and
  whose field values are the per-export summaries (⊤ where none).  The
  importing normalize materializes it as a synthetic object LITERAL at
  a fresh allocation site, so shape interning, field tracking, and
  layout queries all reuse the existing machinery; a namespace
  specifier asks the hook for `"*"` and accepts only the object form.
  `export * as ns` chains the source module's namespace summary.
  Deliberately EXCLUDED: shaped summaries for mutable named object
  exports — ANY importer can mutate an exported object's field set, and
  no single module's analysis sees the other importers, so the
  exporter-side closedness check the original design sketched is not
  sufficient; those exports need either a frozen-object proof or
  runtime-guard-only consumption discipline.  Their primitive FIELD
  types (the "⊤-shape with primitive field types kept" idea) are
  likewise deferred.
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

## What landed (C1–C4, 2026-08-08)

- **C1**: `analyze(program, spec, hooks?)` with
  `hooks.importValue(source, imported)`; normalize binds a
  `Lit {kind:"summary"}` on a hit, `⊤` + degraded-binding on a miss.
  Both domains map summaries in; `metrics.summaryBindings` counts hits.
- **C2**: `AnalysisResult.summarizeBinding(name)` — the final-store
  join of the toplevel binding, projected by `ValDomain.toSummary`.
  Soundness rule: a binding assigned inside a SOURCE lambda has no
  summary (an importer can call an export with arguments the
  module-local fixpoint never saw); scaffolding lambdas (loops, joins)
  don't disqualify — they only run under analyzed toplevel control
  flow.  Inexpressible values (closures, objects, intrinsics, bigints,
  `⊤`) have no summary: absence is the only degradation channel.
- **C3**: oracle.ts keeps the registry keyed by resolved `source_path`,
  fills it after each module's analysis (direct exports via
  `summarizeBinding`, re-exports — `export {a} from` / `export *` —
  chained from the source module's entry), and serves the hook.
  ejs-es6.ts compiles dependencies before importers.
- **C4**: A/B on the self-compile (old oracle vs new, same input):
  ONLY deltas are `exportSummaries` 0→N (analysis metrics
  byte-identical) and the entry module's `degradedBindings` 23→19 /
  `summaryBindings` 0→4.  Nothing moved resolved→worse.

Measured findings that shape C5/C6:

- (C4) 76 summaries published across the self-compile, only 4 consumed.
  The echojs tree imports overwhelmingly as `import * as X` — a
  NAMESPACE object — which phase one cannot summarize.  ast-builder
  alone publishes 69 primitive summaries nobody can consume through
  `import * as b`.  That motivated the C5 namespace form above.
- Most remaining named imports are functions → C6 (⊤-argument result
  summaries) is where degradedBindings actually falls.
- A module whose analysis FAILS publishes nothing, so normalize
  coverage gaps now also cost importers.  Fixed here:
  `export default class` (arrives post-desugar as a
  VariableDeclaration under ExportDefaultDeclaration).  Still failing
  (pre-existing): `??` (maam's own normalize/machine/monad dist
  modules), `Object.defineProperty` non-literal keys (finset/finmap/
  state, lib/runtime), acorn's defineProperties.  values.ts is kept
  `??`-free deliberately so maam's value domain stays self-analyzable.

## C5 measurement (self-compile A/B vs pre-C1 oracle, 2026-08-08)

summaryBindings 0→28, degradedBindings 291→263 (every namespace import
of an analyzable module now resolves; ~1-2 per module).  Emitted-code
metrics did NOT move: diamonds 300→300, shapeGuards 114→114,
specialized 0→0, unknownCalls 148→148, analysis wall ~1.0s→~1.1s
(state spaces byte-identical outside the synthetic objects).  Two
structural reasons, both anticipated:

1. The value types now flowing through namespace field reads
   (`b.FunctionDeclaration : str` + constant) have NO consumer in
   today's lowering — shape guards want receiver shapes (namespace
   receivers decline union-repr because function-valued fields are ⊤),
   and specialization is closedWorld-gated (degradedBindings and
   unknownCalls both still non-zero).
2. The degraded mass that remains IS the function imports (C6).

## C5b: checked-tier shape summaries for MUTABLE object exports (landed 2026-08-08)

The mutable-object exclusion above was too conservative — toshok's
call, and the consumer audit backs it: EVERY shape consumer in EIR
lowering re-checks at runtime (`lower.ts`: "guarded consumption is
correct even when the oracle is wrong"), the numeric fast paths sit
behind `has_tag`, and the one fact-trusting consumer (trusted
specialization clones) is fenced by a COMPILER-side structural escape
analysis that never trusts exports.  So shape facts about mutable
objects are publishable as **checked-tier** facts:

- `ImportSummary.shape`: field names in insertion order + their
  representation sigs.  Identity only — NO value claims.
- The importer materializes it as a `shapedTop` core RHS: declared
  hidden class, every field value `⊤`, and the object marked **open**
  (`AbsObject.open`): the runtime object may carry fields this
  analysis can't see (another importer's mutation), so an untracked
  key reads as `⊤` — never the closed-world `undefined` — and
  unknown-key enumeration includes unknown names.  This keeps the
  asserted tier clean: no false value claim can flow into
  `typeOfNode` and reach the trusted-clone channel (whose taint fence
  covers external CALLERS but not imported state mutated by an
  order-sibling importer's init).
- Export side: a pure-object binding with exactly ONE terminal hidden
  class summarizes; polymorphic/megamorphic/empty refuse.
- **Mutation detection** (`AnalysisResult.mutatedImports`): each
  `shapedTop` site's final heap state is compared against its
  declaration — any field add, representation change, accessor
  install, or dynamic write flags the import as mutated
  (`source#export` labels; surfaced per-module in the --types stats
  as `mutatedImports=N` + detail lines).  Same-representation value
  writes are shape-invisible and unflagged.

Measured payoff (micro): a hot loop reading an imported object's field
runs 2x faster with the cross-module guard passing than with
EJS_SHAPES=off — the first execution-speed win attributable to
summaries.  Self-compile A/B (vs pre-C1 oracle): exportSummaries
79→100, summaryBindings 28→41, degradedBindings 291→250, and — the
first emitted-code movement — **shapeGuards 114→126, typedLoads
84→96** (cross-module guarded fast paths on the compiler itself).
**mutatedImports=0 across all 79 modules**: the tree never mutates an
imported object, so the reanalysis loop below would never fire here —
"pay only when unsafe" costs zero on this codebase.

## Cross-module reanalysis (design sketch — "pay only when unsafe")

The mutation report is the trigger half of a demand-driven Kleene
ascent over the module DAG that would make even VALUE claims about
mutable exports sound without whole-program analysis:

1. Analyze in topo order as today.  Each module reports
   `mutatedImports` (plus, in a fuller version, the mutated field
   joins).
2. When module M1 mutates `E#config`, re-publish E's summary for
   `config` as join(original, M1's observed mutations), then
   re-analyze every OTHER importer of `E#config` — and E itself with
   the joined object state seeded (its own functions also see the
   mutation at runtime).
3. Iterate: joins only grow, the lattice is finite (widening bounds),
   so it terminates; a round cap with fallback-to-⊤ bounds cost.

Cost is proportional to how much cross-module mutation actually
exists — a program that never mutates imported state pays nothing
(the reports come free with the per-module analysis).  Prerequisite
for the driver loop: split compile() so a module's analysis can rerun
without recompiling it (hoist desugar+analyze out of codegen).  The
`mutatedImports=N` numbers on the self-compile are the empirical
go/no-go: if they stay ~0, the loop never fires and annotations
(fresh/frozen) remain the cheaper path to the asserted tier.

## C6: callable summaries (landed 2026-08-08)

- **Export side**: `analyzeExports(program, spec, hooks)` — a SECOND
  analysis whose normalization appends the export harness: a `letrec`
  nondeterministic loop calling every syntactically-function export with
  `⊤` arguments and re-entering itself, `nondet`-joined with the real
  completion.  The loop's fixpoint covers every external call sequence
  (repetition included — `count++` module state needs the ascent; a
  straight-line ⊤-call would be unsound).  `summarizeExport(name)` joins
  the harness result bindings and projects `{fn: {result}}` — primitives
  or a single-class object shape; inexpressible → `{fn: {}}` (result ⊤).
  TWO-PASS on purpose: the harness joins ⊤ into exported functions'
  parameters, so its node types are wider than the plain run's — pass 1
  stays the oracle, pass 2 only publishes.
- **Import side**: a new `AVal.fnSums` constituent (`FnSummary` =
  id + result payload, interned by content).  Calls through it —
  let-position, method, apply, and TAIL position (via the factored
  `returnToKont`) — bind the result: primitives through the summary lit,
  object shapes as an OPEN `shapedTop` object AT THE CALL SITE (per-site
  allocation: the caller's own mutations are tracked locally; cross-caller
  aliasing is the checked tier's guarded story, so C6 object results need
  NO freshness proof for guard-tier use).  Property reads on the summary
  value degrade to ⊤ (never `undefined`); `new` through it stays a plain
  unknown callee (construct semantics are not the call result).  Every
  summary dispatch still counts as an unknown call (arguments' mutation
  by the callee is unmodeled — closedWorld honesty), with
  `metrics.summarizedCalls` tracking the informative subset.
- **The bug C6 exposed — import bindings vs hoisting**: normalize's
  function-declaration hoisting wrapped the whole scope in a `letrec`
  ABOVE the import let-bindings, so a hoisted function's closure never
  captured import addresses — reads of imports inside function bodies
  were `⊥` (masked as unknown calls pre-summaries, fatal after).  Fix:
  import bindings normalize FIRST, above the letrec — which is the SPEC's
  hoisting semantics for imports.  This un-blinded every summary tier
  (C1-C6) inside function bodies, where imports are actually used.
- **Cost control — the iteration budget**: harnessing a PIPELINE-ENTRY
  module (lib/eir/lower exports functions that reach the whole compiler)
  degenerates toward whole-program analysis — the first C6 self-compile
  hung for 20+ minutes on one module.  Two valves, both landed: pass 2
  runs flow-insensitive 0-CFA (the ⊤-argument result JOINS are all it
  needs; the flow-sensitive config-set explosion added nothing), and the
  drivers now take an ITERATION BUDGET (`AnalysisSpec.iterationBudget` →
  `AnalysisBudgetError`) so a runaway exploration degrades to
  "no summaries for this module" instead of hanging the compile —
  deterministic (iteration counts, not wall clock), so host-vs-host
  parity survives.  No cheap pre-pass predicts harness cost (pass-1 size
  doesn't correlate: `optimize` at 31 reached states trips, `verifier`
  at 661 shape sites doesn't) — the budget is the control.  Calibration
  on the self-compile: every harness that ever produced a summary
  fixpoints under 10k iterations; the pipeline-entry modules trip and
  waste only their time-to-trip.

## C6 measurement (self-compile A/B vs pre-C1 oracle, 2026-08-08)

degradedBindings **291 → 86** (every function import of an analyzable
module resolves); 429 export summaries published (207 callable, with
⊤-argument results); summaryBindings 205; **summarizedCalls 87** —
cross-module calls binding real results.  shapeGuards 333→395,
typedLoads 267→293 (both sides veto-free; the summary contribution on
top of local facts).  Pass-1 analysis wall **7.0s → 1.1s** — a 6x
SPEEDUP from precision: summaries kill the ⊤-degradation smears that
dominated exploration.  Pass-2 (harness) cost is the new line item —
budget-tripping pipeline-entry modules waste their time-to-trip —
tracked per-module in the stats (`export-harness wall= iters=`).
unknownCalls unchanged at 148 BY DESIGN (summarized calls still count:
argument-mutation effects are unmodeled, closedWorld stays honest).
specialized remains 0 — the trusted tier is structurally fenced from
imports; runtime-guarded consumption is where summary facts land.

**Ship decision: pass 2 is OPT-IN (`-ffn-summaries`)** until the
self-hosted oracle is fast enough.  Two facts forced it: (1) emitted
code is IDENTICAL with pass 2 off — shapeGuards 395 / typedLoads 293
both ways (fn summaries' object results carry ⊤-sig fields from the ⊤
arguments, which decline union-repr; their value is analysis-level
today), and (2) the deterministic iteration budget cannot bound WALL
on the exe: esprima's harness burned 90+ CPU-minutes inside its 10k
iterations in the stage1 exe (self-hosted store-join cost per
iteration), hanging test-stage1.  Default config measured: 20s
node-hosted self-compile, pass-1 wall 1.1s (the 6x speedup holds
without pass 2 — it comes from value/shape/namespace summaries plus
the import-hoisting fix), degraded 250, all gates green (maam 311,
test-stage1 clean, host-vs-host 28/28 IDENTICAL).  Enable pass 2 by
default when either the exe oracle speed work lands or the budget is
re-based on deterministic JOIN-WORK units instead of iterations.

## C6 design notes (from the C5 postmortem, before building it)

- **Result summaries via a normalize-injected harness**: after the real
  toplevel, inject `letrec h = () => { nondet { r_f = f(⊤…); r_g =
  g(⊤…); … }; tailcall h }` over the exported functions.  The abstract
  fixpoint of that loop over-approximates every external call sequence
  (repetition included — a single straight-line ⊤-call per export is
  NOT sound for module state like `count++`), reuses the machine
  unchanged, and `joinedByName(r_f)` is the ⊤-argument result.  Bonus:
  with the harness in place, exported functions' assignments to module
  bindings become analyzed effects, relaxing today's
  assigned-under-source-lam refusals.
- **Import-side callable summaries need a new value species** (the
  fnTop problem dodged in C1): call sites bind the result summary;
  property reads on it must degrade to ⊤ (NOT `undefined` — the
  current non-object read rule); `new` through it stays ⊤.  Summarized
  calls must still count toward the open-world bit that gates
  closedWorld (their argument-mutation effects stay unmodeled — same
  gap as today's unknown calls, so the posture must not silently
  improve), unless/until an effect summary exists.
- **The self-compile's function results are mostly OBJECTS** (ast
  node literals from builders, parser trees) — a primitive result
  summary buys little here.  The lever that would actually move shape
  guards: prove export-side that a function's result is FRESHLY
  ALLOCATED per call (no aliasing with exporter state), then
  materialize it importer-side as a synthetic allocation AT THE CALL
  SITE — the importer's own mutations are then tracked locally, and
  ast-builder results would carry exact shapes into every desugar
  pass.  That freshness analysis is the real C6 core for this
  codebase; weigh it against the runtime-IC/PGO alternative before
  building (the original C6 caveat stands).
