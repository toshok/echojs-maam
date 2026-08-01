/**
 * A guided tour of maam-fable: one restricted-JS program analyzed under many
 * abstractions, all sharing a single definitional interpreter.
 *
 * Run with:  npm run demo
 */

import {
  analyze,
  concreteEval,
  kCFA,
  checkRestrictions,
  shapeToString,
  structToString,
  type AnalysisResult,
  type Sensitivity,
} from "../src/index.js";
import { parse } from "../src/lang/parse.js";
import type { CVal, AVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

const rule = (s: string) => console.log(`\n\x1b[1m${s}\x1b[0m\n${"─".repeat(s.length)}`);

// Render a concrete result set.
function showConcrete(r: AnalysisResult<FinSet<CVal<Loc>>>): string {
  const parts = [...r.result].map((v) => {
    switch (v.t) {
      case "num":
        return String(v.v);
      case "bigint":
        return `${v.v}n`;
      case "bool":
        return String(v.v);
      case "str":
        return JSON.stringify(v.v);
      case "null":
        return "null";
      case "undef":
        return "undefined";
      case "clo":
        return "<closure>";
      case "obj":
        return "<object>";
      case "intr":
        return `<intrinsic ${v.id}>`;
      case "top":
        return "⊤";
    }
  });
  return `{ ${parts.sort().join(", ")} }`;
}

// Render an abstract value's numeric component.
function showAbstract(r: AnalysisResult<AVal<Loc>>): string {
  const v = r.result;
  const bits: string[] = [];
  if (v.nums.top) bits.push("num:⊤");
  else if (!v.nums.items.isEmpty()) bits.push(`num:{${v.nums.items.toArray().sort((a, b) => a - b).join(",")}}`);
  if (!v.bools.isEmpty()) bits.push(`bool:{${v.bools.toArray().join(",")}}`);
  if (v.strs.top) bits.push("str:⊤");
  else if (!v.strs.items.isEmpty()) bits.push(`str:{${v.strs.items.toArray().join(",")}}`);
  if (!v.clos.isEmpty()) bits.push(`clo×${v.clos.size}`);
  if (v.nullP) bits.push("null");
  if (v.undefP) bits.push("undefined");
  return bits.length ? bits.join(" ") : "⊥";
}

// ---------------------------------------------------------------------------

rule("1. The restricted-JS dialect: some programs are rejected");

for (const src of [
  `const x = eval("2 + 2");`,
  `const f = new Function("a", "return a + 1");`,
  `with (Math) { const y = max(1, 2); }`,
  `const ok = (x) => x * 2; ok(21);`,
]) {
  const violations = checkRestrictions(parse(src));
  const verdict =
    violations.length === 0
      ? "\x1b[32m✓ accepted\x1b[0m"
      : `\x1b[31m✗ rejected\x1b[0m — ${violations.map((v) => v.rule).join(", ")}`;
  console.log(`  ${verdict}\n      ${src}`);
}

// ---------------------------------------------------------------------------

rule("2. Concrete evaluation — the interpreter run at the concrete monad");

const programs: Array<[string, string]> = [
  ["factorial", `function fact(n){ if (n < 1) return 1; return n * fact(n-1); } fact(6);`],
  ["mutual recursion", `function even(n){ if (n===0) return true; return odd(n-1); }
                        function odd(n){ if (n===0) return false; return even(n-1); }
                        even(9);`],
  ["curried closures", `const adder = (n) => (m) => n + m; adder(30)(12);`],
  ["Church-ish twice", `const twice = (f) => (x) => f(f(x)); const inc = (a)=>a+1; twice(twice(inc))(0);`],
];

for (const [name, src] of programs) {
  const r = analyze(parse(src), concreteEval()) as AnalysisResult<FinSet<CVal<Loc>>>;
  console.log(`  ${name.padEnd(18)} ⇒ ${showConcrete(r)}   (${r.collecting.reached.size} states)`);
}

// ---------------------------------------------------------------------------

rule("3. Context-sensitivity (k-CFA): the value×time knob");

// The classic polyvariance example: a shared `apply` used at two types.
const poly = `
  const apply = (f, x) => f(x);
  const inc = (a) => a + 1;
  const neg = (b) => 0 - b;
  const r1 = apply(inc, 100);
  const r2 = apply(neg, 7);
  r1 + r2;`;
console.log(poly.trim().replace(/^/gm, "  "));
console.log();
for (const k of [0, 1, 2]) {
  const r = analyze(parse(poly), kCFA(k)) as AnalysisResult<AVal<Loc>>;
  console.log(`  ${k}-CFA  ⇒  result = ${showAbstract(r)}   (${r.collecting.reached.size} states)`);
}
console.log("  (concrete answer is 94; higher k separates the two uses of `apply`)");

// ---------------------------------------------------------------------------

rule("4. Sensitivity spectrum: the monad-stack knob (same interpreter!)");

console.log("  Analyzing the polyvariance program at 1-CFA under each stack order:\n");
console.log(`  ${"sensitivity".padEnd(20)} ${"result".padEnd(22)} states  iters`);
for (const sensitivity of ["path-sensitive", "flow-sensitive", "flow-insensitive"] as const) {
  const r = analyze(parse(poly), { ...kCFA(1), sensitivity: sensitivity as Sensitivity }) as AnalysisResult<AVal<Loc>>;
  console.log(
    `  ${sensitivity.padEnd(20)} ${showAbstract(r).padEnd(22)} ${String(r.collecting.reached.size).padStart(5)}  ${String(r.collecting.iterations).padStart(5)}`,
  );
}
console.log(
  "\n  Precision decreases left→right as the store is shared more aggressively —\n" +
    "  path ⊑ flow ⊑ flow-insensitive — exactly the order of the transformer stack.",
);

// ---------------------------------------------------------------------------

rule("5. Objects with hidden classes: inferring a parameter's shape");

const shapesProg = `
  function render(node) { return node; }
  const box    = { width: 10, height: 20 };
  const circle = { radius: 5, color: 1, filled: 1 };
  render(box);
  render(circle);
  0;`;
console.log(shapesProg.trim().replace(/^/gm, "  "));
console.log();
{
  const r = analyze(parse(shapesProg), kCFA(1)) as AnalysisResult<AVal<Loc>>;
  const shapes = r.shapesOfVar("node").map(shapeToString).sort();
  console.log(`  hidden classes of \`box\`:    ${r.shapesOfVar("box").map(shapeToString).join(" ")}`);
  console.log(`  hidden classes of \`circle\`: ${r.shapesOfVar("circle").map(shapeToString).join(" ")}`);
  console.log(`  inferred type of param \`node\` = ${shapes.join("  ∪  ")}`);
  console.log(
    `  ⇒ the call site is ${shapes.length === 1 ? "monomorphic" : `polymorphic over ${shapes.length} shapes`}` +
      " — the union of the classes flowing in.",
  );
}

// ---------------------------------------------------------------------------

rule("6. From hidden classes to memory layout: struct emission");

const layoutProg = `
  const player = { hp: 100, name: "hero", alive: true };
  const enemy  = { hp: 30, dmg: 5 };
  0;`;
console.log(layoutProg.trim().replace(/^/gm, "  "));
console.log();
{
  const r = analyze(parse(layoutProg), kCFA(1)) as AnalysisResult<AVal<Loc>>;
  for (const site of r.layouts()) {
    const where = site.span ? layoutProg.slice(site.span.start, site.span.end) : `#${site.site}`;
    const tag = site.monomorphic ? "monomorphic ✓ struct-able" : `polymorphic (${site.shapes.length})`;
    console.log(`  site ${where}  — ${tag}`);
    for (const l of site.layouts) {
      console.log(structToString(l).split("\n").map((s) => "    " + s).join("\n"));
    }
  }
  console.log("\n  malloc(sizeBytes); fields at fixed offsets; numbers unboxed — no dictionary, no tag.");
}

// ---------------------------------------------------------------------------

rule("7. Constructors: the struct a `new F()` produces (and warnings)");

const ctorProg = `
  function Vec2(x, y) { this.x = x; this.y = y; }        // monomorphic
  function Node(leaf) {                                   // polymorphic!
    if (leaf) { this.value = 1; }
    else { this.left = 0; this.right = 0; }
  }
  new Vec2(1, 2);
  new Node(true);
  new Node(false);
  0;`;
console.log(ctorProg.trim().replace(/^/gm, "  "));
console.log();
{
  const r = analyze(parse(ctorProg), kCFA(1)) as AnalysisResult<AVal<Loc>>;
  for (const c of r.constructors()) {
    const tag = c.monomorphic ? "monomorphic ✓" : `polymorphic (${c.shapes.length}) ✗`;
    console.log(`  ${(c.name ?? "<anon>").padEnd(6)} ${tag.padEnd(18)} ${c.shapes.map(shapeToString).join("  |  ")}`);
  }
  const warns = r.warnings();
  if (warns.length) {
    console.log();
    for (const w of warns) console.log(`  \x1b[33m⚠ ${w.message}\x1b[0m`);
  }
}

// ---------------------------------------------------------------------------

rule("8. Specialization: return type as a function of parameter types");

const specProg = `
  function id(x) { return x; }          // polymorphic identity
  function sq(n) { return n * n; }       // monomorphic
  const a = id(1);
  const b = id("hello");
  const c = sq(9);
  0;`;
console.log(specProg.trim().replace(/^/gm, "  "));
console.log();
{
  const r = analyze(parse(specProg), kCFA(1)) as AnalysisResult<AVal<Loc>>;
  for (const f of r.specializations()) {
    const rows = f.specializations.map((s) => `(${s.params.join(", ")}) → ${s.returns}`).join("   |   ");
    const tag = f.monomorphic ? "monomorphic ✓" : `${f.specializations.length} specializations`;
    console.log(`  ${(f.name ?? "<anon>").padEnd(4)}(${f.paramNames.join(", ")})  ${tag.padEnd(18)} ${rows}`);
  }
  for (const w of r.warnings()) {
    if (w.kind === "polymorphic-function") console.log(`\n  \x1b[33m⚠ ${w.message}\x1b[0m`);
  }
  console.log("\n  Emit one specialized version per row; a ⊤/union return is the boxed fallback.");
}

console.log();
