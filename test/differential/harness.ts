/**
 * The differential harness (echojs docs/maam-plan.md, Phase 3.5): the concrete
 * interpreter — `analyze(prog, concreteEval() + intrinsics)` — run over a
 * closed-world corpus and diffed against real engines. `concreteEval()` is the
 * reference semantics; any divergence is a machine bug that would poison the
 * abstract results too.
 *
 * Lanes
 * -----
 * 1. **node** — the corpus convention is that a file's LAST top-level statement
 *    is an ExpressionStatement; its value is the file's *final value* (for this
 *    corpus shape it coincides with the program completion value). The harness
 *    wraps that expression in a reporter (`__diffReport((<expr>))`) whose
 *    canonical renderer prints value-level results — `Object.is`-faithful for
 *    numbers (−0 renders `"-0"`, NaN `"NaN"`), quoted/escaped strings — and
 *    runs the wrapped file under `node`. The printed value must be a MEMBER of
 *    the concrete result set (rendered the same way); a singleton set must
 *    match exactly. Non-singleton sets arise from the machine's one deliberate
 *    concrete imprecision — the index-insensitive (smashed) array `elements`
 *    bucket (plus nondet for-in/for-of iteration built on it) — and are
 *    reported separately as `PASS-CONTAINS`, never silently.
 *
 *    Blind spots (documented, by construction): object/function-valued finals
 *    compare by type only (`<object>`/`<function>`) — structure must be
 *    projected into primitives by the corpus file itself; `console.log`-level
 *    formatting differences are out of scope because comparison is value-level
 *    via the injected renderer, not host stringification.
 *
 * 2. **ejs** — the same wrapped file compiled by the echojs node-hosted
 *    compiler and run natively; its stdout must equal node's stdout byte for
 *    byte. Only available inside an echojs dev tree: set `MAAM_DIFF_EJS_TREE`
 *    to a stage0-style work tree (a `//:srcdir-tree` copy + `lib/generated`,
 *    the layout `buck-test-stage.sh` assembles). Unset ⇒ the lane is SKIPPED
 *    LOUDLY, never silently (standalone maam clones / maam CI).
 *    Root-caused echojs bugs this lane has found live in
 *    `ejs-known-divergences.json` (structured entries: symptom + rootCause,
 *    enforced): listed files report `KNOWN` without failing the gate, an
 *    UNLISTED divergence fails it, and a listed file that stops diverging
 *    fails it as STALE — the list can only shrink by fixing echojs, never
 *    rot. An entry whose file cannot be validated at all (compiles N/A, is
 *    skipped, or is missing from the corpus) is warned about by name.
 *
 * 3. **containment** — for every file the concrete run handles, and every
 *    source node BOTH the concrete and an abstract run map (the concrete
 *    entries are exactly the values a real execution produced, making this the
 *    principled checked-node set), the abstract `typeOfNode` must be ⊒ the
 *    concrete TypeSig — cheap soundness fuzzing for ⊑-direction bugs. Checked
 *    against two abstract configs: (A) the echojs oracle spec verbatim
 *    (`kCFA(1, flow-sensitive, call-site, shapeCap=64, stateCap=512)`) and
 *    (B) the same + `intrinsics: true` (the summary transfer functions whose
 *    soundness is otherwise only asserted).
 *
 * Preconditions, per file: `metrics.unknownCalls === 0` and
 * `metrics.degradedBindings === 0` — degradation makes the diff meaningless.
 * Violations SKIP with the reason printed (the no-silent-caps discipline; the
 * corpus keeps two deliberate skip files to prove the machinery).
 *
 * Gate: exit 1 on any divergence (node, ejs, or containment), on a vacuous
 * pass (zero files compared / zero containment nodes / ejs lane enabled but
 * zero files covered), or on a corpus config error.
 *
 * Run: `npm run diff-harness` (tsx; sequential; ~seconds without the ejs lane).
 */

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

import type { Program, Statement } from "estree";
import { parse } from "../../src/lang/parse.js";
import { analyze, concreteEval, kCFA } from "../../src/index.js";
import type { AnalysisResult, AnalysisSpec } from "../../src/index.js";
import type { CVal } from "../../src/lang/values.js";
import type { FinSet } from "../../src/data/finset.js";
import type { Loc } from "../../src/lang/core.js";

type ConcreteD = FinSet<CVal<Loc>>;

const HERE = path.dirname(fileURLToPath(import.meta.url));
const THIS_FILE = fileURLToPath(import.meta.url);
const REPO_ROOT = path.join(HERE, "..", "..");
const CORPUS_DIR = path.join(HERE, "corpus");
const TIMEOUT_MS = 120_000;
/** Analysis runs in a per-file worker subprocess under this budget: the
 * concrete machine can genuinely diverge (nondet for-of/for-in iteration ×
 * unbounded concrete time), and a hang must become a VISIBLE skip. */
const ANALYZE_TIMEOUT_MS = 30_000;

// ---------------------------------------------------------------------------
// Canonical value rendering — the comparison seam. The injected JS prelude
// (below) and `renderCVal` implement the SAME function; both run under node
// (the harness process and the spawned corpus run), so number→string is the
// identical algorithm. −0 is distinguished explicitly (console.log/String
// would print "0"); strings are quoted with a hand-rolled escaper so no
// host-library formatting is trusted; objects/functions render by type only.
// ---------------------------------------------------------------------------

const escapeString = (s: string): string => {
  let out = '"';
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 0x22) out += '\\"';
    else if (c === 0x5c) out += "\\\\";
    else if (c >= 0x20 && c < 0x7f) out += s.charAt(i);
    else out += "\\u" + c.toString(16).padStart(4, "0");
  }
  return out + '"';
};

const renderNumber = (v: number): string => (Object.is(v, -0) ? "-0" : String(v));

const renderCVal = (v: CVal<Loc>): string => {
  switch (v.t) {
    case "num":
      return renderNumber(v.v);
    case "str":
      return escapeString(v.v);
    case "bool":
      return String(v.v);
    case "null":
      return "null";
    case "undef":
      return "undefined";
    case "clo":
    case "intr":
      return "<function>";
    case "obj":
      return "<object>";
    case "top":
      return "⊤";
  }
};

/** The reporter injected ahead of each corpus file — ES5 only (the ejs lane's
 * esprima front end), no free names beyond the `__diff` prefix. */
const PRELUDE = `function __diffRender(v) {
  if (typeof v === "number") {
    if (v === 0 && 1 / v === -Infinity) return "-0";
    return String(v);
  }
  if (typeof v === "string") {
    var out = '"';
    for (var i = 0; i < v.length; i++) {
      var c = v.charCodeAt(i);
      if (c === 34) out += '\\\\"';
      else if (c === 92) out += "\\\\\\\\";
      else if (c >= 32 && c < 127) out += v.charAt(i);
      else {
        var h = c.toString(16);
        while (h.length < 4) h = "0" + h;
        out += "\\\\u" + h;
      }
    }
    return out + '"';
  }
  if (typeof v === "boolean") return String(v);
  if (v === null) return "null";
  if (v === undefined) return "undefined";
  if (typeof v === "function") return "<function>";
  return "<object>";
}
function __diffReport(v) { console.log(__diffRender(v)); }
`;

// ---------------------------------------------------------------------------
// Wrapping: replace the last top-level ExpressionStatement with a reporter
// call, textually (acorn ranges), so everything else runs unchanged.
// ---------------------------------------------------------------------------

type Ranged = { range?: [number, number] };

function wrapSource(src: string, prog: Program, file: string): string {
  const body = prog.body as Statement[];
  const last = body[body.length - 1];
  if (!last || last.type !== "ExpressionStatement") {
    throw new Error(`${file}: corpus files must end in an ExpressionStatement (the final value)`);
  }
  const stmtR = (last as Ranged).range;
  const exprR = (last.expression as unknown as Ranged).range;
  if (!stmtR || !exprR) throw new Error(`${file}: parser did not attach ranges`);
  return (
    PRELUDE + src.slice(0, stmtR[0]) + `__diffReport((${src.slice(exprR[0], exprR[1])}));` + src.slice(stmtR[1])
  );
}

// ---------------------------------------------------------------------------
// TypeSig containment: c ⊑ a iff a is ⊤, c is never/⊥, or c's tags ⊆ a's tags.
// ---------------------------------------------------------------------------

const sigLeq = (c: string, a: string): boolean => {
  if (a === "⊤") return true;
  if (c === "never") return true;
  if (c === "⊤") return false;
  const at = new Set(a.split("|"));
  return c.split("|").every((t) => at.has(t));
};

// ---------------------------------------------------------------------------
// The ejs lane environment (mirrors buck-test-stage.sh / the diff-lane script).
// ---------------------------------------------------------------------------

interface EjsLane {
  tree: string;
  workDir: string;
  env: NodeJS.ProcessEnv;
}

function setupEjsLane(): EjsLane | { disabled: string } {
  const tree = process.env["MAAM_DIFF_EJS_TREE"];
  if (!tree) {
    return {
      disabled:
        "MAAM_DIFF_EJS_TREE is not set. To enable, run inside an echojs dev tree and point it " +
        "at a stage0-style work tree (//:srcdir-tree copy + lib/generated — see buck-test-stage.sh).",
    };
  }
  const compiler = path.join(tree, "lib/generated/ejs-es6.js");
  if (!fs.existsSync(compiler)) return { disabled: `no compiler at ${compiler} (is the tree assembled?)` };
  // The repo checkout the tree lives in supplies node_modules + node-llvm.
  let repo = path.resolve(tree);
  while (repo !== path.dirname(repo) && !fs.existsSync(path.join(repo, "node-llvm"))) repo = path.dirname(repo);
  const env: NodeJS.ProcessEnv = { ...process.env, NO_COLOR: "1" };
  delete env["FORCE_COLOR"];
  if (fs.existsSync(path.join(repo, "node-llvm"))) {
    env["NODE_PATH"] = `${path.join(repo, "node_modules")}:${path.join(repo, "node-llvm/build/Release")}`;
  }
  const llvmBin = process.env["MAAM_DIFF_LLVM_BIN"] ?? "/opt/homebrew/opt/llvm/bin";
  if (fs.existsSync(path.join(llvmBin, "llc"))) env["PATH"] = `${llvmBin}:${env["PATH"] ?? ""}`;
  if (process.platform === "darwin" && !env["SDKROOT"]) {
    const sdk = spawnSync("/usr/bin/xcrun", ["--show-sdk-path"], { encoding: "utf8" });
    if (sdk.status === 0) env["SDKROOT"] = sdk.stdout.trim();
  }
  // Compile from a directory INSIDE the tree so `--moduledir ../node-compat`
  // and `--moduledir ../ejs-llvm` resolve, like the test/ directory does.
  const workDir = path.join(tree, "maam-diff");
  fs.rmSync(workDir, { recursive: true, force: true });
  fs.mkdirSync(workDir, { recursive: true });
  return { tree, workDir, env };
}

// ---------------------------------------------------------------------------
// Per-file record keeping.
// ---------------------------------------------------------------------------

interface FileResult {
  file: string;
  status: "PASS" | "PASS-CONTAINS" | "SKIP" | "DIVERGE" | "CONFIG-FAIL";
  detail: string;
  ejs: "OK" | "N/A" | "N/A-KNOWN" | "DIVERGE" | "KNOWN" | "STALE-KNOWN" | "off" | "-";
  containChecked: number;
  containAbstractMissing: number;
  containViolations: string[];
}

// ---------------------------------------------------------------------------
// Worker mode (`--analyze-one <file>`): the analysis runs — concrete,
// abstract×2, containment — in a subprocess so machine divergence is a
// timeout, not a harness hang. Node-object identity between the concrete and
// abstract `nodeTypes()` maps only has to hold WITHIN this process (one parse,
// three analyze calls).
// ---------------------------------------------------------------------------

type WorkerOut =
  | { kind: "skip"; reason: string }
  | { kind: "config-fail"; reason: string }
  | { kind: "ok"; concreteSet: string[]; containChecked: number; containMissing: number; violations: string[] };

// The echojs oracle spec verbatim (lib/eir/oracle.ts) and its intrinsics twin —
// config B exercises the summary transfer functions whose soundness is
// otherwise only asserted by maam's own tests.
const abstractSpecs: ReadonlyArray<readonly [string, () => AnalysisSpec<unknown>]> = [
  ["A(oracle)", () => kCFA(1, "flow-sensitive", "call-site", 64, false, false, false, 512) as AnalysisSpec<unknown>],
  [
    "B(oracle+intrinsics)",
    () => kCFA(1, "flow-sensitive", "call-site", 64, false, false, false, 512, false, true) as AnalysisSpec<unknown>,
  ],
];

function analyzeOne(filePath: string): WorkerOut {
  const src = fs.readFileSync(filePath, "utf8");
  let prog: Program;
  let concrete: AnalysisResult<ConcreteD>;
  try {
    prog = parse(src);
    concrete = analyze(prog, { ...concreteEval(), intrinsics: true });
  } catch (e) {
    return { kind: "config-fail", reason: `concrete run threw: ${e instanceof Error ? e.message : String(e)}` };
  }
  const m = concrete.metrics;
  if (m.unknownCalls > 0 || m.degradedBindings > 0) {
    const why = concrete
      .warnings()
      .filter((w) => w.kind === "unknown-call" || w.kind === "degraded-binding")
      .slice(0, 2)
      .map((w) => w.message)
      .join("; ");
    return {
      kind: "skip",
      reason: `unknownCalls=${m.unknownCalls} degradedBindings=${m.degradedBindings}${why ? ` (${why})` : ""}`,
    };
  }
  const out: WorkerOut = {
    kind: "ok",
    concreteSet: [...concrete.result].map(renderCVal),
    containChecked: 0,
    containMissing: 0,
    violations: [],
  };
  const cTypes = concrete.nodeTypes();
  for (const [specName, mkSpec] of abstractSpecs) {
    let abstract: AnalysisResult<unknown>;
    try {
      abstract = analyze(prog, mkSpec());
    } catch (e) {
      out.violations.push(`${specName}: abstract run threw: ${e instanceof Error ? e.message : String(e)}`);
      continue;
    }
    for (const [node, cSig] of cTypes) {
      const aSig = abstract.typeOfNode(node);
      if (aSig === undefined) {
        out.containMissing++;
        continue;
      }
      out.containChecked++;
      if (!sigLeq(cSig, aSig)) {
        const line = (node as { loc?: { start?: { line?: number } } }).loc?.start?.line;
        out.violations.push(`${specName}: node@line${line ?? "?"} concrete ${cSig} ⋢ abstract ${aSig} (⊑-direction bug)`);
      }
    }
  }
  return out;
}

function runWorker(filePath: string): WorkerOut {
  const res = spawnSync(
    process.execPath,
    ["--max-old-space-size=1024", "--import", "tsx", THIS_FILE, "--analyze-one", filePath],
    { encoding: "utf8", timeout: ANALYZE_TIMEOUT_MS, cwd: REPO_ROOT },
  );
  if (res.signal) {
    return {
      kind: "skip",
      reason: `analysis worker killed (${res.signal}) after ${ANALYZE_TIMEOUT_MS} ms — concrete machine divergence (e.g. nondet for-of/for-in × unbounded concrete time) or memory blowup`,
    };
  }
  const lastLine = (res.stdout ?? "").trim().split("\n").pop() ?? "";
  try {
    return JSON.parse(lastLine) as WorkerOut;
  } catch {
    return {
      kind: "config-fail",
      reason: `analysis worker exited ${res.status} without a result: ${(res.stderr ?? "").split("\n")[0]}`,
    };
  }
}

function main(): number {
  const files = fs
    .readdirSync(CORPUS_DIR)
    .filter((f) => f.endsWith(".js"))
    .sort();
  const ejs = setupEjsLane();
  const ejsEnabled = !("disabled" in ejs);
  const knownRaw: Record<string, unknown> = JSON.parse(
    fs.readFileSync(path.join(HERE, "ejs-known-divergences.json"), "utf8"),
  );
  delete knownRaw["//"];
  const knownEjsDivergences = new Map<string, { symptom: string; rootCause: string }>();
  for (const [f, entry] of Object.entries(knownRaw)) {
    const e = entry as { symptom?: unknown; rootCause?: unknown };
    if (typeof e?.symptom !== "string" || typeof e?.rootCause !== "string") {
      console.log(`GATE FAIL: malformed ejs-known-divergences.json entry for ${f} (symptom + rootCause required)`);
      return 1;
    }
    knownEjsDivergences.set(f, { symptom: e.symptom, rootCause: e.rootCause });
  }

  console.log(`differential harness: ${files.length} corpus files, node ${process.version}`);
  if ("disabled" in ejs) console.log(`ejs lane: SKIPPED — ${ejs.disabled}`);
  else console.log(`ejs lane: ENABLED (tree: ${ejs.tree})`);
  console.log("");

  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "maam-diff-"));
  const results: FileResult[] = [];

  for (const file of files) {
    const r: FileResult = {
      file,
      status: "PASS",
      detail: "",
      ejs: ejsEnabled ? "-" : "off",
      containChecked: 0,
      containAbstractMissing: 0,
      containViolations: [],
    };
    results.push(r);
    const src = fs.readFileSync(path.join(CORPUS_DIR, file), "utf8");

    // --- concrete + abstract runs (worker subprocess; see analyzeOne) ---
    const w = runWorker(path.join(CORPUS_DIR, file));
    if (w.kind === "skip") {
      r.status = "SKIP";
      r.detail = w.reason;
      continue;
    }
    if (w.kind === "config-fail") {
      r.status = "CONFIG-FAIL";
      r.detail = w.reason;
      continue;
    }
    r.containChecked = w.containChecked;
    r.containAbstractMissing = w.containMissing;
    r.containViolations = w.violations;
    const concreteSet = w.concreteSet;
    if (concreteSet.length === 0) {
      r.status = "DIVERGE";
      r.detail = "concrete result is ⊥ (stuck machine) with no degradation reported";
      continue;
    }
    if (concreteSet.includes("⊤")) {
      r.status = "DIVERGE";
      r.detail = "concrete result contains ⊤ although unknownCalls=0 — degradation accounting hole";
      continue;
    }

    // --- node lane ---
    // (Re-parse locally just for the wrap ranges; node identity only matters
    // inside the worker, where all three analyses share one parse.)
    let wrapped: string;
    try {
      wrapped = wrapSource(src, parse(src), file);
    } catch (e) {
      r.status = "CONFIG-FAIL";
      r.detail = e instanceof Error ? e.message : String(e);
      continue;
    }
    const wrappedPath = path.join(tmpDir, file);
    fs.writeFileSync(wrappedPath, wrapped);
    const nodeRun = spawnSync(process.execPath, [wrappedPath], { encoding: "utf8", timeout: TIMEOUT_MS });
    if (nodeRun.status !== 0) {
      r.status = "CONFIG-FAIL";
      r.detail = `node exited ${nodeRun.status}: ${(nodeRun.stderr ?? "").split("\n")[0]}`;
      continue;
    }
    const nodeLines = nodeRun.stdout.split("\n").filter((l) => l !== "");
    if (nodeLines.length !== 1) {
      r.status = "CONFIG-FAIL";
      r.detail = `expected exactly one reported line from node, got ${nodeLines.length}`;
      continue;
    }
    const nodeValue = nodeLines[0]!;
    if (!concreteSet.includes(nodeValue)) {
      r.status = "DIVERGE";
      r.detail = `node says ${nodeValue}, concrete set {${concreteSet.join(", ")}}`;
      continue;
    }
    if (concreteSet.length === 1) {
      r.status = "PASS";
      r.detail = nodeValue;
    } else {
      r.status = "PASS-CONTAINS";
      r.detail = `${nodeValue} ∈ ${concreteSet.length}-value set (machine over-approximation: smashed array elements / nondet catch)`;
    }

    // --- ejs lane ---
    if (ejsEnabled) {
      const lane = ejs as EjsLane;
      const ejsSrc = path.join(lane.workDir, file);
      fs.copyFileSync(wrappedPath, ejsSrc);
      const compile = spawnSync(
        process.execPath,
        [
          path.join(lane.tree, "lib/generated/ejs-es6.js"),
          "--srcdir",
          "--moduledir",
          "../node-compat",
          "--moduledir",
          "../ejs-llvm",
          file,
        ],
        { cwd: lane.workDir, encoding: "utf8", timeout: TIMEOUT_MS, env: lane.env },
      );
      const known = knownEjsDivergences.get(file);
      if (compile.status !== 0) {
        r.ejs = "N/A";
        const firstErr = (compile.stderr ?? "").split("\n").find((l) => l.trim() !== "") ?? "compile failed";
        r.detail += ` [ejs N/A: ${firstErr.slice(0, 120)}]`;
        if (known !== undefined) {
          // Review F4: a known-divergence entry for a file that no longer
          // COMPILES cannot be validated in either direction (the claim is
          // about run behavior). A warning rather than a hard failure —
          // hard-failing would let compile-subset drift (an esprima gap) flip
          // a gate about semantics — but it is counted and printed so the
          // entry cannot rot silently.
          r.ejs = "N/A-KNOWN";
          r.detail += " [WARNING: listed in ejs-known-divergences.json but N/A — entry unvalidatable, investigate]";
        }
      } else {
        const exeRun = spawnSync(path.join(lane.workDir, `${file}.exe`), [], {
          cwd: lane.workDir,
          encoding: "utf8",
          timeout: TIMEOUT_MS,
          env: lane.env,
        });
        if (exeRun.status !== 0 || exeRun.stdout !== nodeRun.stdout) {
          if (known !== undefined) {
            // A root-caused, tracked echojs bug (ejs-known-divergences.json):
            // reported loudly, does not fail the gate. Removing the echojs bug
            // makes this entry STALE, which DOES fail the gate.
            r.ejs = "KNOWN";
            r.detail += ` [ejs known-divergence: ${known.rootCause.split(".")[0]}]`;
          } else {
            r.ejs = "DIVERGE";
            r.detail += ` [ejs: exit=${exeRun.status} stdout=${JSON.stringify(exeRun.stdout ?? "")} vs node ${JSON.stringify(nodeRun.stdout)}]`;
          }
        } else if (known !== undefined) {
          r.ejs = "STALE-KNOWN";
          r.detail += " [ejs matches node but the file is listed in ejs-known-divergences.json — remove the stale entry]";
        } else {
          r.ejs = "OK";
        }
      }
    }

    // (containment already computed in the worker, recorded on `r` above)
  }

  fs.rmSync(tmpDir, { recursive: true, force: true });

  // --- report ---
  let exit = 0;
  for (const r of results) {
    const contain =
      r.containViolations.length > 0
        ? ` CONTAIN-FAIL(${r.containViolations.length})`
        : r.containChecked > 0
          ? ` contain=${r.containChecked}`
          : "";
    console.log(`${r.file.padEnd(28)} ${r.status.padEnd(13)} ejs=${r.ejs.padEnd(7)}${contain} ${r.detail}`);
    for (const v of r.containViolations) console.log(`    ${v}`);
  }

  const count = (s: FileResult["status"]): FileResult[] => results.filter((r) => r.status === s);
  const passed = count("PASS");
  const contained = count("PASS-CONTAINS");
  const skipped = count("SKIP");
  const diverged = count("DIVERGE");
  const configFailed = count("CONFIG-FAIL");
  const ejsOk = results.filter((r) => r.ejs === "OK");
  const ejsNa = results.filter((r) => r.ejs === "N/A" || r.ejs === "N/A-KNOWN");
  const ejsDiv = results.filter((r) => r.ejs === "DIVERGE");
  const ejsKnown = results.filter((r) => r.ejs === "KNOWN");
  const ejsStale = results.filter((r) => r.ejs === "STALE-KNOWN");
  // Review F4: every known-divergences entry must be accounted for — validated
  // (KNOWN/STALE), or explicitly reported unvalidatable (its file compiled N/A,
  // was skipped concrete-side, or is missing from the corpus entirely).
  const ejsUnvalidatable = ejsEnabled
    ? [...knownEjsDivergences.keys()].filter((f) => {
        const res = results.find((x) => x.file === f);
        return !res || (res.ejs !== "KNOWN" && res.ejs !== "STALE-KNOWN" && res.ejs !== "DIVERGE" && res.ejs !== "OK");
      })
    : [];
  const containChecked = results.reduce((a, r) => a + r.containChecked, 0);
  const containMissing = results.reduce((a, r) => a + r.containAbstractMissing, 0);
  const containViolations = results.flatMap((r) => r.containViolations);

  console.log("\n==== differential harness summary ====");
  console.log(
    `corpus: ${results.length}  exact: ${passed.length}  contains: ${contained.length}  ` +
      `skipped: ${skipped.length}  diverged: ${diverged.length}  config-failed: ${configFailed.length}`,
  );
  if (skipped.length > 0) console.log(`skips (visible, with reasons above): ${skipped.map((r) => r.file).join(" ")}`);
  console.log(
    ejsEnabled
      ? `ejs lane: ok ${ejsOk.length}  n/a ${ejsNa.length}  known-divergent ${ejsKnown.length} (tracked echojs bugs, see ejs-known-divergences.json)  new-divergent ${ejsDiv.length}  stale-known ${ejsStale.length}`
      : "ejs lane: skipped (see reason above)",
  );
  if (ejsUnvalidatable.length > 0) {
    console.log(
      `WARNING: ${ejsUnvalidatable.length} known-divergence entr${ejsUnvalidatable.length === 1 ? "y" : "ies"} could not be validated ` +
        `(file N/A, skipped, or missing from corpus): ${ejsUnvalidatable.join(" ")} — investigate; entries must not rot`,
    );
  }
  console.log(
    `containment: ${containChecked} node checks across 2 abstract configs, ` +
      `${containMissing} concrete-mapped nodes unmapped abstractly, ${containViolations.length} violations`,
  );

  if (diverged.length > 0 || configFailed.length > 0) {
    console.log(`GATE FAIL: divergences=${diverged.length} config-failures=${configFailed.length}`);
    exit = 1;
  }
  if (containViolations.length > 0) {
    console.log(`GATE FAIL: ${containViolations.length} containment violations`);
    exit = 1;
  }
  if (ejsEnabled && ejsDiv.length > 0) {
    console.log(`GATE FAIL: ${ejsDiv.length} NEW ejs divergences (not in ejs-known-divergences.json)`);
    exit = 1;
  }
  if (ejsEnabled && ejsStale.length > 0) {
    console.log(`GATE FAIL: ${ejsStale.length} stale ejs-known-divergences.json entries (bug fixed? remove them)`);
    exit = 1;
  }
  // Vacuous-pass guards: a lane that compared nothing proves nothing.
  if (passed.length + contained.length === 0) {
    console.log("GATE FAIL: zero files compared against node — vacuous pass");
    exit = 1;
  }
  if (containChecked === 0) {
    console.log("GATE FAIL: zero containment checks — vacuous pass");
    exit = 1;
  }
  if (ejsEnabled && ejsOk.length === 0) {
    console.log("GATE FAIL: ejs lane enabled but covered zero files — vacuous pass");
    exit = 1;
  }
  if (exit === 0) console.log("GATE PASS: zero divergences");
  return exit;
}

if (process.argv[2] === "--analyze-one") {
  console.log(JSON.stringify(analyzeOne(process.argv[3]!)));
  process.exit(0);
}
process.exit(main());
