/**
 * Regenerate **every results table in `docs/paper-draft.md`** in one invocation.
 *
 *   npx tsx examples/benchmarks/paper-results.ts            # all tables (~10 min)
 *   PAPER_ONLY=fast npx tsx examples/benchmarks/paper-results.ts   # skip crypto+box2d (<1 min)
 *   PAPER_ONLY=1,2  npx tsx examples/benchmarks/paper-results.ts   # only tables 1 and 2
 *
 * Output is Markdown, ready to paste back into the draft, preceded by a machine-spec
 * block for the `⟨MACHINE SPEC⟩` placeholder (§6 setup).
 *
 * Each measurement runs in its own subprocess with a heap cap and timeout, so a
 * divergent configuration (e.g. crypto at too high a state cap) is *contained* —
 * it reports "DID NOT CONVERGE" instead of killing the batch. Identical configs
 * shared across tables are measured once and cached.
 *
 * Env: PAPER_TIMEOUT_MS (default 600000), PAPER_HEAP_MB (default 8192),
 *      PAPER_ONLY (comma list of table numbers, or "fast").
 */
import os from "node:os";
import { readFileSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

import { parse } from "../../src/lang/parse.js";
import { analyze, kCFA } from "../../src/index.js";

const HERE = dirname(fileURLToPath(import.meta.url));

/** Each benchmark's whole-program entry sequence (from its `new Benchmark(...)`). */
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

/** A single measurement: a program (benchmark name *or* inline source) + the knob vector. */
interface Job {
  readonly bench: string; // benchmark file name, or "" when `src` is inline
  readonly src?: string; // inline program (for the synthetic §6.3 probe)
  readonly sc: number; // shapeCap
  readonly rec: boolean; // recency
  readonly gc: boolean; // abstract GC
  readonly push: boolean; // P4F pushdown
  readonly st: number; // stateCap
  readonly cnt: boolean; // abstract counting
}

interface Result {
  ms: number;
  states: number;
  shapes: number;
  specs: number;
  specsMono: number;
  ctors: number;
  ctorsMono: number;
}

const jobKey = (j: Job): string =>
  `${j.bench || `src:${j.src}`}|sc${j.sc}|r${+j.rec}|g${+j.gc}|p${+j.push}|st${j.st}|c${+j.cnt}`;

// --- child mode: run ONE job in-process, print one RESULT line -----------------

function runOne(j: Job): Result {
  const prog = j.src ?? `${readFileSync(join(HERE, `${j.bench}.js`), "utf8")}\n;(function(){${DRIVERS[j.bench]}})();\n`;
  const ast = parse(prog);
  const t = Date.now();
  const r = analyze(ast, kCFA(0, "flow-sensitive", "call-site", j.sc, j.rec, j.gc, j.push, j.st, j.cnt));
  const ms = Date.now() - t;
  const specs = r.specializations();
  const ctors = r.constructors();
  return {
    ms,
    states: r.metrics.reachedStates,
    shapes: r.metrics.shapesInterned,
    specs: specs.length,
    specsMono: specs.filter((s) => s.monomorphic).length,
    ctors: ctors.length,
    ctorsMono: ctors.filter((c) => c.monomorphic).length,
  };
}

if (process.argv[2] === "--child") {
  const job: Job = JSON.parse(process.argv[3]!);
  process.stdout.write(`RESULT ${JSON.stringify(runOne(job))}\n`);
  process.exit(0);
}

// --- parent mode: orchestrate, cache, render -----------------------------------

const TIMEOUT_MS = Number(process.env.PAPER_TIMEOUT_MS ?? "600000");
const HEAP_MB = Number(process.env.PAPER_HEAP_MB ?? "8192");
const ONLY = process.env.PAPER_ONLY ?? "";
const FAST = ONLY === "fast";
const wanted = (table: number): boolean => FAST || ONLY === "" || ONLY.split(",").includes(String(table));
/** Benchmarks skipped in `fast` mode (the multi-second/minute ones). */
const HEAVY = new Set(["crypto", "box2d", "raytrace"]);

const self = fileURLToPath(import.meta.url);
const cache = new Map<string, Result | null>(); // null ⇒ did-not-converge

/** Measure a job in an isolated subprocess (heap-capped, timed out); cache by config. */
function measure(j: Job): Result | null {
  const key = jobKey(j);
  if (cache.has(key)) return cache.get(key)!;
  if (FAST && HEAVY.has(j.bench)) {
    cache.set(key, null);
    return null;
  }
  process.stderr.write(`  … ${key}\n`);
  let res: Result | null = null;
  try {
    const out = execFileSync("npx", ["tsx", self, "--child", JSON.stringify(j)], {
      cwd: join(HERE, "../.."),
      timeout: TIMEOUT_MS,
      env: { ...process.env, NODE_OPTIONS: `--max-old-space-size=${HEAP_MB}` },
      encoding: "utf8",
      stdio: ["ignore", "pipe", "ignore"],
    });
    const line = out.split("\n").find((l) => l.startsWith("RESULT "));
    if (line) res = JSON.parse(line.slice("RESULT ".length));
  } catch {
    res = null; // timeout or OOM
  }
  cache.set(key, res);
  return res;
}

const job = (bench: string, o: Partial<Job> = {}): Job => ({
  bench,
  sc: 0,
  rec: true,
  gc: true,
  push: false,
  st: 0,
  cnt: false,
  ...o,
});

const secs = (ms: number): string => (ms >= 10000 ? `${(ms / 1000).toFixed(0)} s` : `${(ms / 1000).toFixed(2)} s`);
const mono = (r: Result | null, kind: "spec" | "ctor"): string =>
  !r ? "—" : kind === "spec" ? `${r.specs} (${r.specsMono})` : r.ctors === 0 ? "0" : `${r.ctors} (${r.ctorsMono})`;
const dnc = (label: string): string => `${label} — **DID NOT CONVERGE** (>${TIMEOUT_MS / 1000}s / ${HEAP_MB}MB)`;

const out: string[] = [];
const P = (s = ""): void => void out.push(s);

// --- machine-spec block --------------------------------------------------------
const cpu = os.cpus()[0]?.model ?? "unknown CPU";
const cores = os.cpus().length;
const ramGB = (os.totalmem() / 2 ** 30).toFixed(0);
P("## Machine spec (paste into the §6 `⟨MACHINE SPEC⟩` placeholder)");
P();
P(`- CPU: ${cpu} (${cores} logical cores)`);
P(`- RAM: ${ramGB} GB`);
P(`- OS: ${os.type()} ${os.release()} (${process.platform}/${process.arch})`);
P(`- Node.js: ${process.version}; V8 heap cap: ${HEAP_MB} MB`);
P();
P("---");
P();

// === Table 1 — §6.1 whole-suite totality ======================================
if (wanted(1)) {
  P("### §6.1 — Whole-suite totality (k = 0, flow-sensitive, GC + recency)");
  P();
  P("| benchmark | knobs beyond GC+recency | time | states | shapes | specs (mono) | ctors (mono) |");
  P("|-----------|-------------------------|-----:|-------:|-------:|--------------|--------------|");
  // (config, label) per the draft's recommended totality settings.
  const suite: Array<[string, Partial<Job>, string]> = [
    ["splay", {}, "—"],
    ["navier-stokes", {}, "—"],
    ["code-load", {}, "—"],
    ["deltablue", {}, "—"],
    ["richards", {}, "—"],
    ["raytrace", { st: 2 }, "stateCap = 2"],
    ["box2d", { sc: 8, st: 1 }, "shapeCap = 8, stateCap = 1"],
    ["crypto", { st: 1 }, "stateCap = 1"],
  ];
  for (const [name, extra, knobs] of suite) {
    const r = measure(job(name, extra));
    if (!r) {
      P(`| ${name} | ${knobs} | ${dnc("")} |||||`);
      continue;
    }
    P(
      `| ${name} | ${knobs} | ${secs(r.ms)} | ${r.states} | ${r.shapes} | ${mono(r, "spec")} | ${mono(r, "ctor")} |`,
    );
  }
  P();
}

// === Table 2 — §6.2 state-cap precision curve ==================================
if (wanted(2)) {
  P("### §6.2 — State-cap precision curve (richards, GC + recency)");
  P();
  P("| richards, cap = | states | specs (mono) |");
  P("|-----------------|-------:|--------------|");
  for (const st of [1, 2, 4, 8, 0]) {
    const r = measure(job("richards", { st }));
    P(`| ${st === 0 ? "off" : st} | ${r ? r.states : "—"} | ${mono(r, "spec")} |`);
  }
  P();
}

// === Table 3 — §6.3 counting ablation ==========================================
if (wanted(3)) {
  P("### §6.3 — Abstract-counting ablation (shapes: off → on)");
  P();
  P("| workload | counting off | counting on | outcome |");
  P("|----------|-------------:|------------:|---------|");
  const PROBE = `
    function Point(a,b,c,d){ this.a=a; this.b=b; this.c=c; this.d=d; }
    var p = new Point(1,2,3,4);
    p.a + p.b + p.c + p.d;`;
  const rows: Array<[string, Partial<Job>]> = [
    ["4-field constructor", { bench: "", src: PROBE }],
    ["crypto", { bench: "crypto", st: 1 }],
    ["richards", { bench: "richards" }],
    ["box2d", { bench: "box2d", sc: 8, st: 1 }],
  ];
  for (const [label, base] of rows) {
    const off = measure(job(base.bench ?? "", { ...base, cnt: false }));
    const on = measure(job(base.bench ?? "", { ...base, cnt: true }));
    const shp = (r: Result | null): string => (r ? String(r.shapes) : "DNC");
    const verdict =
      off && on
        ? on.shapes < off.shapes
          ? `${(off.shapes / on.shapes).toFixed(1)}× fewer; specs ${on.specs}(${on.specsMono})`
          : on.shapes > off.shapes
            ? `**regression** (+${on.shapes - off.shapes})`
            : "no change"
        : "—";
    P(`| ${label} | ${shp(off)} | ${shp(on)} | ${verdict} |`);
  }
  P();
}

// === Table 4 — §6.3 abstract-GC ablation =======================================
if (wanted(4)) {
  P("### §6.3 — Abstract-GC ablation (recency on, no caps)");
  P();
  P("| benchmark | gc off (states / shapes / time) | gc on (states / shapes / time) |");
  P("|-----------|---------------------------------|--------------------------------|");
  const cell = (r: Result | null): string => (r ? `${r.states} / ${r.shapes} / ${secs(r.ms)}` : "DNC");
  for (const name of ["richards", "deltablue", "navier-stokes", "splay"]) {
    const off = measure(job(name, { gc: false }));
    const on = measure(job(name, { gc: true }));
    P(`| ${name} | ${cell(off)} | ${cell(on)} |`);
  }
  P();
}

// === Table 5 — §6.3 P4F-pushdown ablation ======================================
if (wanted(5)) {
  P("### §6.3 — P4F-pushdown ablation (GC + recency)");
  P();
  P("| benchmark | push off (states / time) | push on (states / time) |");
  P("|-----------|--------------------------|-------------------------|");
  const cell = (r: Result | null): string => (r ? `${r.states} / ${secs(r.ms)}` : "DNC");
  // raytrace needs the state cap to converge; apply it on both sides so only `push` varies.
  const rows: Array<[string, Partial<Job>]> = [
    ["richards", {}],
    ["deltablue", {}],
    ["raytrace", { st: 2 }],
  ];
  for (const [name, extra] of rows) {
    const off = measure(job(name, { ...extra, push: false }));
    const on = measure(job(name, { ...extra, push: true }));
    P(`| ${name} | ${cell(off)} | ${cell(on)} |`);
  }
  P();
}

process.stdout.write(out.join("\n") + "\n");
