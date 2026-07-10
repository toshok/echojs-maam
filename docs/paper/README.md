# Paper: *Total, Composable Abstract Interpretation for JavaScript*

This directory holds the paper and **all the tooling used to generate its results**,
so every table is reproducible from a clean checkout.

| file | what it is |
|------|------------|
| [`draft.md`](draft.md) | The paper (rough full draft: abstract → references). |
| [`results.ts`](results.ts) | One-invocation regenerator for every §6 results table. |
| [`baselines/`](baselines/) | Scaffold for the JSAI / TAJS baseline comparison (§6.4). |

## Regenerating the results

Every timing/count in §6 of the draft comes from `results.ts`. From the repo root:

```sh
npx tsx docs/paper/results.ts             # all 6 tables (~15 min)
PAPER_ONLY=fast npx tsx docs/paper/results.ts   # skip crypto/box2d/raytrace (<1 min)
PAPER_ONLY=1,6  npx tsx docs/paper/results.ts   # a subset of tables
```

It prints Markdown ready to paste into `draft.md`, preceded by a machine-spec block
for the `⟨MACHINE SPEC⟩` placeholder. Each measurement runs in an isolated
subprocess (heap-capped, timed out), so a divergent configuration reports
"DID NOT CONVERGE" instead of taking down the batch; identical configs shared
across tables are measured once. Env knobs: `PAPER_TIMEOUT_MS`, `PAPER_HEAP_MB`,
`PAPER_ONLY`.

The tables:
1. §6.1 whole-suite totality
2. §6.2 state-cap precision curve
3. §6.3 abstract-counting ablation
4. §6.3 abstract-GC ablation
5. §6.3 P4F-pushdown ablation
6. §6.3 standard-library-intrinsics ablation

**Structural counts (states/shapes/specializations, every monomorphism verdict) are
hardware-independent** — only wall-clock times vary by machine. Regenerate the whole
set in one batch on a single reference machine so the times are mutually consistent.

## Analyzer configuration

The analyzer is invoked via `kCFA(...)` from `../../src/index.ts`; `results.ts`
documents the exact knob vector per table. The knobs (all orthogonal, all ablatable):
`k`, sensitivity, context, `shapeCap`, `recency`, `gc`, `pushdown`, `stateCap`,
`counting`, `intrinsics`. See §4 of the draft.
