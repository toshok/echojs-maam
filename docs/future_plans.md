# Future plans

Running list of next steps, deferred work, and open questions. Kept *out* of the
paper draft to keep it focused — the paper should name at most the one or two
next-steps that matter for its story (the strong-update ceiling → recency/k≥1), not
this whole backlog.

---

## Analysis precision & performance

### Strong-update ceiling → two-address recency, or k ≥ 1
The single biggest known precision limit (§6.3/§7 of the paper). At k = 0,
single-address abstract counting cannot keep a *looped* allocation
strong-updatable when the source variable is reused: monovariance collapses the
fresh object and its predecessors onto one address, and GC cannot collect an
address a live variable still names, so the count saturates to `MANY`. This is why
`counting` regresses box2d.
- **Fix A — two-address recency** [Balakrishnan & Reps 2006]: split each allocation
  site into a most-recent (strong-updatable) and a summary address, aging
  most-recent → summary on reallocation. Recovers strong update for looped
  allocations. Cost: must reconcile stale references to an aged most-recent object
  (the soundness subtlety we deliberately avoided with single-address counting).
- **Fix B — k ≥ 1**: context separates the fresh allocation from its predecessors
  without the stale-pointer machinery, at the usual k-CFA cost.
- Both fit the existing knob structure (add/ablate in isolation). Worth measuring
  which buys more on box2d/crypto per unit cost.

### Perf: integer-intern addresses (was task #39)
Intern `Addr`/`OAddr`/`KAddr`/`Name` to dense integer ids (as we already do for
environments) so map keys are int-compares, not string builds. Expected constant-
factor speedup on the store-join hot path. Never done; still open.

### Structural environment ids
A residual ~1.4× env over-distinction remains from path-dependent incremental env
ids. Canonicalizing environments structurally (content-addressed, not path-
addressed) would merge spurious distinctions even without the state cap. The state
cap's env-canonicalization already does this *when the cap is on*; this would
generalize it.

### Fold counting into crypto's recommended config?
Open decision. `counting` gives crypto a 12.8× shape reduction (7204 → 561) at zero
monomorphism cost, but the paper's §6.1 recommended-config table currently has it
*off* (counting appears only in the §6.3 ablation). If we decide the win is worth
making default for allocation-light code, update §6.1 and the `suite` array in
`docs/paper/results.ts` together. (It must stay off for box2d.)

### `putDyn` / `defineAccessor` / `setProto` strong update
These object-mutating RHS forms currently always weak-join (sound but imprecise),
even when the target address is count-`ONE`. Extending the counting-based strong
update to them (as we did for `writeProp`) is a small, self-contained precision
win. Low priority.

---

## Standard-library intrinsics

### Phase 1 — DONE (2026-07)
Value-level modeling behind the `intrinsics` knob (kCFA 11th arg / `BENCH_INTRINSICS`).
Globals seeded into the initial store as intrinsic values with summary transfer
functions; dispatched in both the `call`/`new` and `method` paths. Covered: `Math.*`
(→num) + constants, `parseInt`/`parseFloat`/`isNaN`/`isFinite`, `Number`/`String`/
`Boolean` coercions and their statics (`Number.isInteger`, `String.fromCharCode`,
`Array.isArray`), and `Array`/`Object` construction. Off by default (173 tests
unchanged; +7 new). **Results:** reduces `unknownCalls` everywhere (crypto 19→8,
navier 9→3, richards 5→3 — the codegen-relevant headline). Shape effect is two-sided:
crypto 7204→5236 (−27%; degraded arrays were *polluting* shapes) but navier/richards
rise (degraded-`undefined` was *collapsing* shapes; real types differentiate). Mono
verdicts and time unchanged. A precision/soundness win (removes the §6.5 degradation
threat), a size tradeoff — worth it for codegen sharpness.

### Phase 2 — array/string prototype methods with heap effects — DONE (2026-07)
`Array.prototype` and `String.prototype` seeded as store objects (megamorphic ⊤
shape, so they add no shapes to the metric); arrays proto-link to `Array.prototype`
so `arr.push`/`.slice` resolve through the normal prototype walk. Intrinsic models
now receive the **receiver**, so mutating methods (`push`/`unshift`/`fill`) weak-
update its `elements` bucket (verified: `a.push("hi"); a[0]` reads `str`). Covered:
array `push`/`pop`/`shift`/`unshift`/`slice`/`concat`/`fill`/`reverse`/`sort`/
`indexOf`/`includes`/`join`; string `charCodeAt`/`charAt`/`slice`/`substring`/
`split`/`toUpperCase`/`includes`/`startsWith`/… (string primitives dispatch via a
`typeSig`-includes-`str` check, since they have no object address to walk).
**Results:** `unknownCalls` fall further (navier 9→3, deltablue 9→7, richards 5→3);
shapes essentially unchanged for most (richards +72 real precision); states and
monomorphism unchanged. +5 tests (185 total). `sort`/`replace` callbacks are *not*
invoked (returned soundly, ignoring the fn) — that is Phase 3.

### Phase 3 — higher-order builtins — DONE (2026-07)
`map`/`flatMap`/`forEach`/`filter`/`find`/`findIndex`/`some`/`every`/`reduce`/
`reduceRight`/`sort` invoke the user callback through the machine. Mechanism: a new
`collect?: OAddr` continuation-frame variant (state.ts `Kont`) — on the callback's
return, the value is weak-added to the result array's elements and *that array* is
bound (this is `map`). `reduce` threads acc = init ⊔ element and binds the callback's
return. The rest pre-bind a synchronous result and run the callback for effect (a
discard frame, mirroring setter dispatch). The callback is entered **once** with the
index-insensitive smashed element value, so the fixpoint covers all elements with **no
state explosion** (nested maps < 40 states; Octane benchmarks byte-identical on/off,
since none use HOFs). **Precision = coverage:** a function used only as a `map`
callback goes from *unanalyzed/invisible* (off) to fully specialized `(num)→num` (on),
and the result array is precisely typed (`[1,2,3].map(x=>x*2)[0]` = `{2,4,6}`). +7
tests (192 total). Approximations: `sort`/`replace` comparators are called but ordering
is index-insensitive; `reduce`'s accumulator fixpoint is approximated (init ⊔ element),
not iterated — revisit if a workload needs precise fold typing.

### Coverage is open-ended
Beyond the phases, full stdlib coverage is an ongoing *curation* task (a lib.d.ts
with dataflow summaries), not a bounded one. The framework is done; the table grows.

### Possible: model in the concrete interpreter too
Currently intrinsics are abstract-only (`anyNum`/`anyBool` are `⊥` concretely). A
concrete interpreter that evaluates `Math.floor` exactly would let concrete eval run
stdlib-using programs faithfully (currently they degrade). Lower priority.

---

## Compiler / IR integration

### Migrate the analysis IR to basic-block-with-parameters (BBWP / SSA)
Context: the compiler is moving to a BBWP IR (SSA-friendly). Question was whether
the analysis is hampered by the current ANF core. Findings (2026-07):
- We are **already on ANF**, not raw AST — so most AST-irregularity is already
  normalized away. BBWP ≈ SSA ≈ functional/ANF (Appel; Kelsey CPS↔SSA), so this is
  a *reshaping*, not a paradigm change. **Headline results (monomorphism) are
  representation-invariant** and will not move (possibly marginally *improve*).
- **Where BBWP helps:**
  1. *Scalar strong-update for free.* Today at k = 0 a reassigned local weak-joins
     into one address `(name, tzero)` (`setVar` → `joinAt`), so `var x=3; x="s"`
     leaves `x ↦ {3,"s"}` even flow-sensitively. Block-param renaming makes each def
     precise — "SSA is to scalars what counting is to the heap," but unconditional
     (no aliasing hazard for locals). Also lets scalars *leave the per-point store*,
     shrinking the store to heap + continuations → faster joins (our dominant cost).
  2. *Loops as blocks, not tail-recursive closures.* Loops are currently lowered to
     tail-recursive closures (`normalize.ts:340`), so every back-edge is a
     closure-enter (tick + continuation alloc + store threading). A BBWP loop is a
     block with a back-edge and block-param φs — local fixpoint, no per-iteration
     call machinery. Big for loop-heavy code (box2d, crypto, navier).
  3. *Enables sparse (SCCP-style) analysis* along def-use edges — the substrate for
     a fast production tier.
- **Where it does NOT help (be honest):**
  1. *The heap is IR-independent.* Objects are keyed by allocation site; shapes,
     aliasing, strong-update, recency/counting are unchanged. box2d/crypto costs and
     the k = 0 strong-update ceiling do **not** improve from the IR change (that
     needs the heap-side levers above). SSA-over-the-heap would require
     memory-SSA/HSSA — separate, harder.
  2. *Interprocedural context/return still need the CESK\* model* — k-CFA contexts,
     the continuation store, P4F. BBWP is intraprocedural.
- **Recommended approach:** do NOT reformulate as classical CFG dataflow (would cost
  the MAAM property — one step relation, monad-swappable, concrete recovery). Instead
  **step the same CESK\* machine directly over the BBWP IR**: block parameters as the
  binding forms, terminators as control transfers. Keeps MAAM purity + concrete
  recovery; gains the scalar and loop wins for free; transplants the heap model
  unchanged. ("Block-args as binders" is the whole trick.)
- **Net expectation:** somewhat faster (materially on loop-heavy code), marginally
  more precise (reassigned scalars), IR aligned with the compiler — but not a fix for
  the heap-driven costs, which are orthogonal to the IR.
- Optional two-tier design: sparse SSA propagation for production speed; CESK* MAAM
  analysis as the precise oracle.

---

## Paper / evaluation

### Regenerate all results on the reference machine
All §6 timings are provisional (dev laptop, Apple Silicon). Re-run
`docs/paper/results.ts` in one batch on the desktop (AMD Ryzen 7) so
times are mutually consistent; fill in `⟨MACHINE SPEC⟩`. Structural counts are
hardware-independent and won't change. Re-confirm per-benchmark valve settings — a
larger memory/time budget may permit a *higher* state cap (more precision) within
the same totality guarantee.

### Baseline comparison (JSAI / TAJS) — §6.4 TODO
The single most valuable evaluation addition. Primary: run JSAI (closest neighbor)
and, if the dialect gap allows, TAJS on the shared Octane subset; map value-set
output onto our monomorphism/layout metrics. The totality axis needs no shared
metric — any benchmark where a baseline diverges/OOMs while we return a bounded
result is a self-contained data point. Fallback if artifacts are costly to
resurrect (JSAI is older Scala/JS; TAJS is Java, maintained): paper comparison vs.
published numbers, leaning on totality.

### GC-off → DNC confirmation
Assert-with-a-number that crypto/raytrace/box2d do *not* converge without abstract
GC (currently asserted from prior experience). One run per benchmark with `gc` off
and a timeout; report as evidence that GC is the flow-sensitivity enabler.

### Bibliography verification
Two entries flagged (†) in the draft's References: SAFE [Lee et al. 2012] (venue —
FOOL vs. later SAFE lineage) and CFA2 [Vardoulakis & Shivers 2010] (ESOP vs. 2011
LMCS journal). Verify page numbers throughout against DOIs; generate `references.bib`
when moving to LaTeX.

### Title / framing decision
Current title leads with totality + composition; monomorphism is the payoff. If we
want the (more surprising) monomorphism finding as the headline, retitle and reorder
the intro. Decide before the body hardens.
