/**
 * Run the analyzer over the bundled, self-contained JS benchmarks (Octane) and
 * report **timing** and the hidden-class / specialization "N-distribution" — the
 * instrument for the monomorphism hypothesis, and for watching analysis cost grow
 * as codebases get large.
 *
 * The Octane files are wrapped in a `BenchmarkSuite(...)` harness (from Octane's
 * `base.js`) we don't ship, so the real work function is never *called* from
 * inside the file. We append a direct call to each benchmark's entry point (the
 * `setup`/`run`/`tearDown` its `Benchmark(...)` names). Unbound runtime globals
 * (`Math`, `Array`, the harness, …) resolve to no callee and are *degraded*
 * (result unknown, path continues) — see `metrics.unknownCalls`.
 *
 *   npx tsx examples/benchmarks/run.ts                 # sweep all (subprocess-isolated)
 *   npx tsx examples/benchmarks/run.ts richards        # one benchmark, in-process
 *   npx tsx examples/benchmarks/run.ts richards 1 flow-sensitive
 *
 * Env: BENCH_TIMEOUT_MS (default 60000), BENCH_HEAP_MB (default 8192),
 *      BENCH_K (default 0), BENCH_SENS (default flow-insensitive).
 */
import { readFileSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

import { parse } from "../../src/lang/parse.js";
import { normalizeProgram } from "../../src/lang/normalize.js";
import { analyze, kCFA } from "../../src/index.js";
import type { Sensitivity } from "../../src/analysis.js";

const HERE = dirname(fileURLToPath(import.meta.url));

/** Each benchmark's entry sequence (setup, run, teardown) — from its `new Benchmark(...)`. */
const DRIVERS: Record<string, string> = {
  richards: "runRichards();",
  deltablue: "deltaBlue();",
  crypto: "encrypt(); decrypt();",
  raytrace: "renderScene();",
  splay: "SplaySetup(); SplayRun(); SplayTearDown();",
  "navier-stokes": "setupNavierStokes(); runNavierStokes(); tearDownNavierStokes();",
  box2d: "setupBox2D(); runBox2D(); tearDownBox2D();",
  "code-load": "setupCodeLoad(); runCodeLoadClosure(); runCodeLoadJQuery();",
};

const K = Number(process.env.BENCH_K ?? "0");
const SENS = (process.env.BENCH_SENS ?? "flow-insensitive") as Sensitivity;
const SHAPE_CAP = Number(process.env.BENCH_SHAPECAP ?? "0");
const RECENCY = process.env.BENCH_RECENCY === "1";
const COUNTING = process.env.BENCH_COUNTING === "1";
const INTRINSICS = process.env.BENCH_INTRINSICS === "1";
const GC = process.env.BENCH_GC === "1";
const PUSHDOWN = process.env.BENCH_PUSHDOWN === "1";
const STATE_CAP = Number(process.env.BENCH_STATECAP ?? "0");

/** Analyze one benchmark in-process, printing a single result line. */
function runOne(name: string, k = K, sens = SENS): void {
  const driver = DRIVERS[name] ?? "";
  const raw = readFileSync(join(HERE, `${name}.js`), "utf8");
  const src = driver ? `${raw}\n;(function(){${driver}})();\n` : raw;

  let t = Date.now();
  let ast;
  try {
    ast = parse(src);
  } catch (e) {
    return void console.log(`${name.padEnd(15)} parse-FAIL — ${(e as Error).message}`);
  }
  const parseMs = Date.now() - t;
  t = Date.now();
  try {
    normalizeProgram(parse(src)); // normalize timing (analyze re-normalizes internally)
  } catch (e) {
    return void console.log(`${name.padEnd(15)} parse=${parseMs}ms normalize-FAIL — ${(e as Error).message}`);
  }
  const normMs = Date.now() - t;
  t = Date.now();
  const r = analyze(
    ast,
    kCFA(k, sens, "call-site", SHAPE_CAP, RECENCY, GC, PUSHDOWN, STATE_CAP, COUNTING, INTRINSICS),
  );
  const anaMs = Date.now() - t;

  const ctors = r.constructors();
  const specs = r.specializations();
  console.log(
    `${name.padEnd(15)} k=${k} ${sens.padEnd(16)} ` +
      `parse=${String(parseMs).padStart(4)}ms norm=${String(normMs).padStart(4)}ms ` +
      `analyze=${String(anaMs).padStart(7)}ms  ` +
      `states=${String(r.metrics.reachedStates).padStart(6)} shapes=${String(r.metrics.shapesInterned).padStart(7)} ` +
      `ctors=${ctors.length}(mono ${ctors.filter((c) => c.monomorphic).length}) ` +
      `specs=${specs.length}(mono ${specs.filter((s) => s.monomorphic).length}) ` +
      `unknownCalls=${r.metrics.unknownCalls}`,
  );
}

/** Sweep: run each benchmark in an isolated subprocess so a timeout/OOM is contained. */
function sweep(): void {
  const timeoutMs = Number(process.env.BENCH_TIMEOUT_MS ?? "60000");
  const heapMb = Number(process.env.BENCH_HEAP_MB ?? "8192");
  const self = fileURLToPath(import.meta.url);
  console.log(`# sweep: k=${K} ${SENS}, timeout=${timeoutMs}ms, heap=${heapMb}MB\n`);
  for (const name of Object.keys(DRIVERS)) {
    try {
      const out = execFileSync("npx", ["tsx", self, name], {
        cwd: join(HERE, "../.."),
        timeout: timeoutMs,
        env: { ...process.env, NODE_OPTIONS: `--max-old-space-size=${heapMb}` },
        encoding: "utf8",
        stdio: ["ignore", "pipe", "ignore"],
      });
      process.stdout.write(out);
    } catch (e) {
      const err = e as { signal?: string; status?: number; killed?: boolean };
      const why = err.killed || err.signal === "SIGTERM" ? `TIMEOUT (>${timeoutMs}ms) or OOM` : `exit ${err.status}`;
      console.log(`${name.padEnd(15)} DID NOT CONVERGE — ${why}`);
    }
  }
}

const which = process.argv[2];
if (!which) sweep();
else runOne(which, process.argv[3] ? Number(process.argv[3]) : K, (process.argv[4] as Sensitivity) ?? SENS);
