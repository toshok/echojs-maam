#!/usr/bin/env bash
#
# Baseline comparison driver (§6.4) — SCAFFOLD, not yet functional.
#
# Runs JSAI (primary) and TAJS (secondary) over the shared Octane subset and records
# (a) termination under a fixed budget — the totality axis — and (b) a common
# precision metric (call-target-set size per site). Fill in the TODOs marked below;
# the structure is intended to mirror `results.ts` so outputs sit side by side.
#
# See ./README.md for the metric-translation rationale.

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../../.." && pwd)"
BENCH_DIR="$REPO/examples/benchmarks"
OUT_DIR="$HERE/out"
mkdir -p "$OUT_DIR"

# --- configuration: point these at local checkouts/builds of the tools -----------
# TODO: set these (or export before running).
JSAI_HOME="${JSAI_HOME:-}"   # e.g. ~/src/jsai   (Scala; sbt build)
TAJS_JAR="${TAJS_JAR:-}"     # e.g. ~/src/TAJS/dist/tajs-all.jar
BUDGET_SEC="${BUDGET_SEC:-300}"
BUDGET_MB="${BUDGET_MB:-8192}"

# The same whole-program entry sequences results.ts appends. Keep in sync.
declare -A DRIVERS=(
  [richards]="runRichards();"
  [deltablue]="deltaBlue();"
  [crypto]="encrypt(); decrypt();"
  [raytrace]="renderScene();"
  [splay]="SplaySetup(); SplayRun(); SplayTearDown();"
  [navier-stokes]="setupNavierStokes(); runNavierStokes(); tearDownNavierStokes();"
  [box2d]="setupBox2D(); runBox2D(); tearDownBox2D();"
  [code-load]="setupCodeLoad(); runCodeLoadClosure(); runCodeLoadJQuery();"
)

# Build a driver-appended copy of a benchmark in $OUT_DIR, echo its path.
prepare() {
  local name="$1" src="$OUT_DIR/$1.driven.js"
  cat "$BENCH_DIR/$name.js" >"$src"
  printf '\n;(function(){%s})();\n' "${DRIVERS[$name]}" >>"$src"
  echo "$src"
}

run_jsai() {
  local name="$1" js; js="$(prepare "$name")"
  if [[ -z "$JSAI_HOME" ]]; then echo "  jsai:  SKIP (set JSAI_HOME)"; return; fi
  # TODO: invoke JSAI on "$js" under (BUDGET_SEC, BUDGET_MB); capture:
  #   - terminated? (exit vs timeout/OOM)  -> totality axis
  #   - per-call-site target-set sizes     -> precision axis
  # e.g. (cd "$JSAI_HOME" && timeout "$BUDGET_SEC" sbt "run ... $js") ...
  echo "  jsai:  TODO"
}

run_tajs() {
  local name="$1" js; js="$(prepare "$name")"
  if [[ -z "$TAJS_JAR" ]]; then echo "  tajs:  SKIP (set TAJS_JAR)"; return; fi
  # TODO: java -Xmx${BUDGET_MB}m -jar "$TAJS_JAR" ... "$js" under a timeout;
  # capture termination and the call-graph edge counts for the precision metric.
  echo "  tajs:  TODO"
}

echo "# baselines: budget=${BUDGET_SEC}s / ${BUDGET_MB}MB"
for name in "${!DRIVERS[@]}"; do
  echo "$name"
  run_jsai "$name"
  run_tajs "$name"
done

echo
echo "TODO: emit a Markdown table (termination + common precision metric) matching"
echo "the §6.4 layout, for paste into docs/paper/draft.md."
