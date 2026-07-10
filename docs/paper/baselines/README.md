# Baseline comparison (§6.4) — JSAI / TAJS

Scaffold for comparing our analyzer against prior JavaScript static analyzers on
the shared Octane subset. **Status: not yet run** — this directory documents the
intended pipeline and provides a driver skeleton (`run-baselines.sh`). See the
§6.4 TODO in [`../draft.md`](../draft.md).

## Why a translation layer is needed

The baselines report abstract **value sets at program points**; we report
**specialization** and **shape-monomorphism** verdicts. The headline numbers do not
line up directly, so a fair comparison maps both onto a common measure. Two axes:

1. **Totality (no shared metric required).** Run each tool on every benchmark with a
   fixed time/memory budget and record *which terminate*. Any benchmark on which a
   baseline diverges or exhausts memory while we return a bounded result is a
   self-contained data point for §5. This is the cheapest, strongest comparison and
   the one to do first.
2. **Precision (needs translation).** Pick a common metric — e.g. **call-target-set
   size per call site** (how many callees a site may reach) or points-to-set size —
   computable from both tools' output, and compare distributions. Separately, map
   the baselines' value sets at each variable to a coarse type and compare against
   our per-function monomorphism verdict.

## The tools

| tool | lang | notes |
|------|------|-------|
| **JSAI** [Kashyap et al. 2014] | Scala | Closest architectural neighbor (configurable AAM-style). Older artifact; may need resurrection. **Primary baseline.** |
| **TAJS** [Jensen et al. 2009] | Java | Actively maintained; the cheaper lift if only one can be stood up. |

Both accept plain `.js`, so they run against `../../examples/benchmarks/*.js`
directly (with the same synthetic driver appended — see `run-baselines.sh`).

## Dialect caveat

The baselines analyze full ECMAScript (including `eval` and the intrinsic library)
under a different soundness envelope than our AOT whole-program dialect. Note which
benchmarks each tool rejects/soundly-approximates so the comparison is apples-to-apples.

## Fallback

If standing up the artifacts proves costly, drop to a **paper comparison**: cite the
tools' published Octane/precision numbers where they exist, compare qualitatively,
and lean on the totality axis (which needs no shared metric).

## Running

```sh
# Configure tool locations, then:
bash docs/paper/baselines/run-baselines.sh
```
