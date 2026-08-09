import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval, kCFA } from "../src/index.js";
import type { ImportHooks, ImportSummary } from "../src/index.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

// Cross-module import summaries (docs/cross-module-summaries.md, C1+C2):
// the `importValue` hook binds imported names to export summaries instead of
// ⊤, and `summarizeBinding` extracts a module's export summaries for the
// next importer.  These tests cover both sides and their round trip.

const sigOfVar = (src: string, name: string, hooks?: ImportHooks): string => {
  const r = analyze(parse(src), kCFA(1), hooks);
  return r.domain.typeSig(r.valueOfVar(name));
};

// --- C1: the import side -----------------------------------------------------

test("without a hook an import binds ⊤ and is counted degraded", () => {
  const r = analyze(parse(`import { a } from "./m"; const y = a;`), kCFA(1));
  assert.equal(r.domain.typeSig(r.valueOfVar("y")), "⊤");
  assert.equal(r.metrics.degradedBindings, 1);
  assert.equal(r.metrics.summaryBindings, 0);
});

test("a hook miss behaves exactly like no hook", () => {
  const misses: Array<[string, string]> = [];
  const hooks: ImportHooks = {
    importValue: (source, imported) => {
      misses.push([source, imported]);
      return undefined;
    },
  };
  const r = analyze(parse(`import { a } from "./m"; const y = a;`), kCFA(1), hooks);
  assert.deepEqual(misses, [["./m", "a"]]);
  assert.equal(r.domain.typeSig(r.valueOfVar("y")), "⊤");
  assert.equal(r.metrics.degradedBindings, 1);
  assert.equal(r.metrics.summaryBindings, 0);
});

test("a summary hit binds the summary, not ⊤, and is not degraded", () => {
  const hooks: ImportHooks = {
    importValue: (source, imported) =>
      source === "./m" && imported === "a" ? { nums: [41] } : undefined,
  };
  const r = analyze(parse(`import { a } from "./m"; const y = a + 1;`), kCFA(1), hooks);
  assert.equal(r.domain.typeSig(r.valueOfVar("a")), "num");
  // constant propagation straight through the import: 41 + 1 = 42
  const y = r.valueOfVar("y") as { nums: { top: boolean; items: FinSet<number> } };
  assert.deepEqual(y.nums.items.toArray(), [42]);
  assert.equal(r.metrics.degradedBindings, 0);
  assert.equal(r.metrics.summaryBindings, 1);
});

test("a widened component ('any') is the type's ⊤, not value ⊤", () => {
  const hooks: ImportHooks = { importValue: () => ({ strs: "any" }) };
  assert.equal(sigOfVar(`import { s } from "./m"; const y = s;`, "y", hooks), "str");
});

test("a constant boolean summary folds branches", () => {
  const hooks: ImportHooks = { importValue: () => ({ bools: [false] }) };
  const r = analyze(parse(`import { DEBUG } from "./m"; const y = DEBUG ? 1 : 2;`), kCFA(1), hooks);
  const y = r.valueOfVar("y") as { nums: { items: FinSet<number> } };
  assert.deepEqual(y.nums.items.toArray(), [2]);
});

test("default and renamed imports ask for the right export names", () => {
  const asked: Array<[string, string]> = [];
  const hooks: ImportHooks = {
    importValue: (source, imported) => {
      asked.push([source, imported]);
      return { nums: [1] };
    },
  };
  const r = analyze(parse(`import d, { a as b } from "./m"; const y = d + b;`), kCFA(1), hooks);
  assert.deepEqual(asked.sort(), [
    ["./m", "a"],
    ["./m", "default"],
  ]);
  assert.equal(r.domain.typeSig(r.valueOfVar("b")), "num");
  assert.equal(r.metrics.summaryBindings, 2);
});

test("a namespace import asks for '*' and only accepts the object form", () => {
  // a primitive answer for "*" is a host bug: a namespace IS an object —
  // treat it as a miss (⊤ + degraded), never bind nonsense
  const asked: string[] = [];
  const hooks: ImportHooks = {
    importValue: (_source, imported) => {
      asked.push(imported);
      return { nums: [1] };
    },
  };
  const r = analyze(parse(`import * as ns from "./m"; const y = ns;`), kCFA(1), hooks);
  assert.deepEqual(asked, ["*"]);
  assert.equal(r.domain.typeSig(r.valueOfVar("y")), "⊤");
  assert.equal(r.metrics.degradedBindings, 1);
  assert.equal(r.metrics.summaryBindings, 0);
});

// --- C5: namespace-object summaries ------------------------------------------

test("a namespace object summary binds a shaped object with typed fields", () => {
  const hooks: ImportHooks = {
    importValue: (_source, imported) =>
      imported === "*"
        ? {
            fields: [
              { name: "RED", value: { nums: [1] } },
              { name: "NAME", value: { strs: ["red"] } },
              { name: "helper" }, // a function export: field holds ⊤
            ],
          }
        : undefined,
  };
  const r = analyze(
    parse(`import * as m from "./m";
           const a = m.RED + 1;
           const s = m.NAME;
           const f = m.helper;`),
    kCFA(1),
    hooks,
  );
  assert.equal(r.metrics.degradedBindings, 0);
  assert.equal(r.metrics.summaryBindings, 1);
  assert.equal(r.domain.typeSig(r.valueOfVar("m")), "obj");
  const a = r.valueOfVar("a") as { nums: { items: { toArray(): number[] } } };
  assert.deepEqual(a.nums.items.toArray(), [2]); // constant folded through the field
  assert.equal(r.domain.typeSig(r.valueOfVar("s")), "str");
  assert.equal(r.domain.typeSig(r.valueOfVar("f")), "⊤"); // unexpressed field = ⊤
  // the synthetic object's hidden class is interned like any local literal:
  // one shape, canonical field set, ordered witness in summary order
  const shapes = r.shapesOfVar("m");
  assert.equal(shapes.length, 1);
  assert.deepEqual(shapes[0]!.fields.map((f) => f.name).sort(), ["NAME", "RED", "helper"]);
  assert.deepEqual(r.fieldOrderOfShape(shapes[0]!), ["RED", "NAME", "helper"]);
});

test("a read of a field absent from the namespace summary is undefined, not ⊤", () => {
  // the field set is exact (namespace objects are immutable by spec), so a
  // miss reads as the spec's `undefined`
  const hooks: ImportHooks = {
    importValue: (_s, imported) =>
      imported === "*" ? { fields: [{ name: "a", value: { nums: [1] } }] } : undefined,
  };
  const r = analyze(parse(`import * as m from "./m"; const y = m.nope;`), kCFA(1), hooks);
  assert.equal(r.domain.typeSig(r.valueOfVar("y")), "undefined");
});

test("nested object summaries materialize as nested objects", () => {
  // `export * as inner` chains: a namespace field that is itself a namespace
  const hooks: ImportHooks = {
    importValue: (_s, imported) =>
      imported === "*"
        ? { fields: [{ name: "inner", value: { fields: [{ name: "K", value: { nums: [7] } }] } }] }
        : undefined,
  };
  const r = analyze(parse(`import * as m from "./m"; const k = m.inner.K;`), kCFA(1), hooks);
  const k = r.valueOfVar("k") as { nums: { items: { toArray(): number[] } } };
  assert.deepEqual(k.nums.items.toArray(), [7]);
});

test("calls through a namespace's function field degrade exactly like before", () => {
  const hooks: ImportHooks = {
    importValue: (_s, imported) => (imported === "*" ? { fields: [{ name: "f" }] } : undefined),
  };
  const r = analyze(parse(`import * as m from "./m"; const y = m.f(1);`), kCFA(1), hooks);
  assert.equal(r.domain.typeSig(r.valueOfVar("y")), "⊤");
  assert.ok(r.metrics.unknownCalls >= 1);
});

test("a named import whose summary is an object binds the object form too", () => {
  const hooks: ImportHooks = {
    importValue: (_s, imported) =>
      imported === "cfg" ? { fields: [{ name: "level", value: { nums: [3] } }] } : undefined,
  };
  const r = analyze(parse(`import { cfg } from "./m"; const y = cfg.level;`), kCFA(1), hooks);
  const y = r.valueOfVar("y") as { nums: { items: { toArray(): number[] } } };
  assert.deepEqual(y.nums.items.toArray(), [3]);
});

test("a summary past the widening bound widens to the type's ⊤", () => {
  const hooks: ImportHooks = { importValue: () => ({ nums: [1, 2, 3, 4, 5, 6] }) };
  assert.equal(sigOfVar(`import { n } from "./m"; const y = n;`, "y", hooks), "num");
});

test("the concrete domain enumerates a finite summary and tops a widened one", () => {
  const hooks: ImportHooks = { importValue: () => ({ nums: [1, 2] }) };
  const r = analyze(parse(`import { n } from "./m"; n;`), concreteEval(), hooks);
  const set = r.result as FinSet<CVal<Loc>>;
  assert.deepEqual([...set].map((v) => (v.t === "num" ? v.v : v.t)).sort(), [1, 2]);

  const topHooks: ImportHooks = { importValue: () => ({ nums: "any" }) };
  const rt = analyze(parse(`import { n } from "./m"; n;`), concreteEval(), topHooks);
  const topSet = rt.result as FinSet<CVal<Loc>>;
  assert.deepEqual([...topSet].map((v) => v.t), ["top"]);
});

// --- C2: the export side -----------------------------------------------------

test("summarizeBinding extracts primitive toplevel bindings", () => {
  const r = analyze(
    parse(`export const x = 42;
           export const name = "red";
           const flag = true;
           const nil = null;
           const undef = undefined;`),
    kCFA(1),
  );
  assert.deepEqual(r.summarizeBinding("x"), { nums: [42] });
  assert.deepEqual(r.summarizeBinding("name"), { strs: ["red"] });
  assert.deepEqual(r.summarizeBinding("flag"), { bools: [true] });
  assert.deepEqual(r.summarizeBinding("nil"), { nullP: true });
  assert.deepEqual(r.summarizeBinding("undef"), { undefP: true });
  assert.equal(r.summarizeBinding("missing"), undefined);
});

test("a toplevel reassignment joins into the summary (live bindings)", () => {
  const r = analyze(parse(`export let x = 1; x = "s";`), kCFA(1));
  assert.deepEqual(r.summarizeBinding("x"), { nums: [1], strs: ["s"] });
});

test("a binding assigned inside a source function has no summary", () => {
  // Even when the function IS called locally: an importer can call an export
  // with arguments the module-local fixpoint never saw, so any binding a
  // source function assigns is out of phase-one bounds.
  const r = analyze(parse(`export let x = 1; export function f(v) { x = v; } f(2);`), kCFA(1));
  assert.equal(r.summarizeBinding("x"), undefined);
});

test("a binding assigned in an arrow function has no summary", () => {
  const r = analyze(parse(`export let x = 1; const g = () => { x = 2; };`), kCFA(1));
  assert.equal(r.summarizeBinding("x"), undefined);
});

test("a toplevel loop assignment is still summarizable (scaffolding lambdas are not source lambdas)", () => {
  const r = analyze(parse(`export let x = 0; for (let i = 0; i < 3; i = i + 1) { x = x + 1; }`), kCFA(1));
  const s = r.summarizeBinding("x");
  assert.ok(s !== undefined, "loop-assigned toplevel binding should summarize");
  assert.ok(s.nums !== undefined, "summary should carry the numeric component");
  assert.equal(s.strs, undefined);
});

test("closure exports have no summary; object exports get a checked-tier shape", () => {
  const r = analyze(
    parse(`export function f() { return 1; }
           export const o = { a: 1, b: "s" };`),
    kCFA(1),
  );
  assert.equal(r.summarizeBinding("f"), undefined);
  assert.deepEqual(r.summarizeBinding("o"), {
    shape: [
      { name: "a", sig: "num" },
      { name: "b", sig: "str" },
    ],
  });
});

// --- C5b: checked-tier shape summaries (mutable object exports) --------------

test("a polymorphic or ⊤ object export has no shape summary", () => {
  const r = analyze(
    parse(`export const o = %unknown ? { a: 1 } : { b: 2 };`.replace("%unknown", "Math.random()")),
    kCFA(1),
  );
  assert.equal(r.summarizeBinding("o"), undefined); // two terminal classes
});

test("a shape summary binds an OPEN object: shape exact, values ⊤, misses ⊤", () => {
  const hooks: ImportHooks = {
    importValue: (_s, imported) =>
      imported === "cfg"
        ? {
            shape: [
              { name: "level", sig: "num" },
              { name: "tag", sig: "str" },
            ],
          }
        : undefined,
  };
  const r = analyze(
    parse(`import { cfg } from "./m";
           const v = cfg.level;
           const missing = cfg.whatever;`),
    kCFA(1),
    hooks,
  );
  // the shape is a fact the importing analysis interns…
  const shapes = r.shapesOfVar("cfg");
  assert.equal(shapes.length, 1);
  assert.deepEqual(r.fieldOrderOfShape(shapes[0]!), ["level", "tag"]);
  assert.deepEqual(shapes[0]!.fields.map((f) => `${f.name}:${f.type}`).sort(), ["level:num", "tag:str"]);
  // …but NO value claim leaves it: declared fields are ⊤, and an untracked
  // field is ⊤ too (another module may have added it), never `undefined`
  assert.equal(r.domain.typeSig(r.valueOfVar("v")), "⊤");
  assert.equal(r.domain.typeSig(r.valueOfVar("missing")), "⊤");
  assert.equal(r.metrics.summaryBindings, 1);
  assert.equal(r.metrics.degradedBindings, 0);
});

test("mutatedImports reports shape-changing writes to imported objects", () => {
  const hooks: ImportHooks = {
    importValue: (_s, imported) =>
      imported === "cfg" ? { shape: [{ name: "level", sig: "num" }] } : undefined,
  };
  const clean = analyze(parse(`import { cfg } from "./m"; const v = cfg.level;`), kCFA(1), hooks);
  assert.deepEqual(clean.mutatedImports(), []);

  const adds = analyze(parse(`import { cfg } from "./m"; cfg.extra = 1;`), kCFA(1), hooks);
  assert.deepEqual(adds.mutatedImports(), ["./m#cfg"]);

  const retypes = analyze(parse(`import { cfg } from "./m"; cfg.level = "high";`), kCFA(1), hooks);
  assert.deepEqual(retypes.mutatedImports(), ["./m#cfg"]);

  // a same-representation write keeps the declared class: shape-invisible
  const sameRepr = analyze(parse(`import { cfg } from "./m"; cfg.level = 5;`), kCFA(1), hooks);
  assert.deepEqual(sameRepr.mutatedImports(), []);
});

test("a namespace field that is a shaped object chains through", () => {
  const hooks: ImportHooks = {
    importValue: (_s, imported) =>
      imported === "*"
        ? { fields: [{ name: "config", value: { shape: [{ name: "k", sig: "num" }] } }] }
        : undefined,
  };
  const r = analyze(parse(`import * as m from "./m"; const c = m.config;`), kCFA(1), hooks);
  const shapes = r.shapesOfVar("c");
  assert.equal(shapes.length, 1);
  assert.deepEqual(r.fieldOrderOfShape(shapes[0]!), ["k"]);
});

test("shape summaries round-trip: exporter's object class reaches the importer", () => {
  const e = analyze(parse(`export const point = { x: 1.5, y: 2.5 };`), kCFA(1));
  const s = e.summarizeBinding("point");
  assert.ok(s !== undefined && s.shape !== undefined);
  const hooks: ImportHooks = { importValue: (_src, imported) => (imported === "point" ? s : undefined) };
  const i = analyze(parse(`import { point } from "./m"; const p = point;`), kCFA(1), hooks);
  const shapes = i.shapesOfVar("p");
  assert.equal(shapes.length, 1);
  assert.deepEqual(i.fieldOrderOfShape(shapes[0]!), ["x", "y"]);
});

test("a binding holding an import miss (⊤) has no summary", () => {
  const r = analyze(parse(`import { a } from "./m"; export const x = a;`), kCFA(1));
  assert.equal(r.summarizeBinding("x"), undefined);
});

// --- round trip: module A's summaries feed module B's analysis ---------------

test("summaries round-trip from an exporting analysis to an importing one", () => {
  const a = analyze(
    parse(`export const RED = 1;
           export let mode = "fast";
           mode = "slow";`),
    kCFA(1),
  );
  const summaries = new Map<string, ImportSummary>();
  for (const name of ["RED", "mode"]) {
    const s = a.summarizeBinding(name);
    if (s !== undefined) summaries.set(name, s);
  }
  const hooks: ImportHooks = {
    importValue: (source, imported) => (source === "./a" ? summaries.get(imported) : undefined),
  };
  const b = analyze(
    parse(`import { RED, mode } from "./a";
           const z = RED + 1;
           const m = mode;`),
    kCFA(1),
    hooks,
  );
  const z = b.valueOfVar("z") as { nums: { items: FinSet<number> } };
  assert.deepEqual(z.nums.items.toArray(), [2]);
  assert.equal(b.domain.typeSig(b.valueOfVar("m")), "str");
  assert.equal(b.metrics.degradedBindings, 0);
  assert.equal(b.metrics.summaryBindings, 2);
});

// --- C6: callable summaries (⊤-argument function results) --------------------

import { analyzeExports } from "../src/index.js";

test("analyzeExports summarizes primitive results of function exports", () => {
  const r = analyzeExports(
    parse(`export function one() { return 1; }
           export const tag = (x) => "t";
           function yes() { return true; }
           export { yes };
           export function ident(x) { return x; }`),
    kCFA(1),
  );
  assert.ok(r !== null);
  assert.deepEqual(r.summarizeExport("one"), { fn: { result: { nums: [1] } } });
  assert.deepEqual(r.summarizeExport("tag"), { fn: { result: { strs: ["t"] } } });
  assert.deepEqual(r.summarizeExport("yes"), { fn: { result: { bools: [true] } } });
  assert.deepEqual(r.summarizeExport("ident"), { fn: {} }); // ⊤-arg identity: result ⊤
  assert.equal(r.summarizeExport("nope"), undefined);
});

test("the harness loop covers repeated external calls (module-state ascent)", () => {
  // one straight-line ⊤-call would claim bump() ⊑ {1}; the repetition
  // fixpoint must widen it (external code can call bump many times)
  const r = analyzeExports(parse(`let n = 0; export function bump() { n = n + 1; return n; }`), kCFA(1));
  assert.ok(r !== null);
  const s = r.summarizeExport("bump");
  assert.ok(s !== undefined && s.fn !== undefined && s.fn.result !== undefined);
  assert.equal(s.fn.result.nums, "any");
});

test("an object result summarizes as its shape", () => {
  const r = analyzeExports(parse(`export function mk() { return { a: 1, b: "s" }; }`), kCFA(1));
  assert.ok(r !== null);
  assert.deepEqual(r.summarizeExport("mk"), {
    fn: {
      result: {
        shape: [
          { name: "a", sig: "num" },
          { name: "b", sig: "str" },
        ],
      },
    },
  });
});

test("analyzeExports is null when nothing is syntactically a function export", () => {
  assert.equal(analyzeExports(parse(`export const K = 7;`), kCFA(1)), null);
});

test("calling through a callable summary binds the result, still open-world", () => {
  const hooks: ImportHooks = {
    importValue: (_s, imported) =>
      imported === "f" ? { fn: { result: { nums: [41] } } } : undefined,
  };
  const r = analyze(
    parse(`import { f } from "./m";
           const y = f() + 1;
           const tf = typeof f;
           const p = f.someProp;`),
    kCFA(1),
    hooks,
  );
  const y = r.valueOfVar("y") as { nums: { items: { toArray(): number[] } } };
  assert.deepEqual(y.nums.items.toArray(), [42]);
  const tf = r.valueOfVar("tf") as { strs: { items: { toArray(): string[] } } };
  assert.deepEqual(tf.strs.items.toArray(), ["function"]);
  assert.equal(r.domain.typeSig(r.valueOfVar("p")), "⊤"); // properties live elsewhere
  assert.equal(r.metrics.degradedBindings, 0);
  assert.equal(r.metrics.summaryBindings, 1);
  assert.equal(r.metrics.summarizedCalls, 1);
  assert.ok(r.metrics.unknownCalls >= 1); // the open-world bit stays honest
});

test("a summary call in tail position returns its result (returnToKont)", () => {
  const hooks: ImportHooks = {
    importValue: (_s, imported) => (imported === "f" ? { fn: { result: { strs: ["ok"] } } } : undefined),
  };
  const r = analyze(
    parse(`import { f } from "./m";
           function g() { return f(); }
           const z = g();`),
    kCFA(1),
    hooks,
  );
  assert.equal(r.domain.typeSig(r.valueOfVar("z")), "str");
});

test("an object result materializes as an OPEN shaped object at the call site", () => {
  const hooks: ImportHooks = {
    importValue: (_s, imported) =>
      imported === "mk" ? { fn: { result: { shape: [{ name: "a", sig: "num" }] } } } : undefined,
  };
  const r = analyze(
    parse(`import { mk } from "./m";
           const o = mk();
           const a = o.a;
           const missing = o.zzz;`),
    kCFA(1),
    hooks,
  );
  const shapes = r.shapesOfVar("o");
  assert.equal(shapes.length, 1);
  assert.deepEqual(r.fieldOrderOfShape(shapes[0]!), ["a"]);
  assert.equal(r.domain.typeSig(r.valueOfVar("a")), "⊤"); // no value claims
  assert.equal(r.domain.typeSig(r.valueOfVar("missing")), "⊤"); // open, not undefined
});

test("a namespace's function field dispatches through the method path", () => {
  const hooks: ImportHooks = {
    importValue: (_s, imported) =>
      imported === "*"
        ? { fields: [{ name: "helper", value: { fn: { result: { nums: [7] } } } }] }
        : undefined,
  };
  const r = analyze(parse(`import * as m from "./m"; const y = m.helper();`), kCFA(1), hooks);
  const y = r.valueOfVar("y") as { nums: { items: { toArray(): number[] } } };
  assert.deepEqual(y.nums.items.toArray(), [7]);
  assert.equal(r.metrics.summarizedCalls, 1);
});

test("fn summaries round-trip exporter → importer, and re-export through toSummary", () => {
  const e = analyzeExports(parse(`export function greet() { return "hi"; }`), kCFA(1));
  assert.ok(e !== null);
  const s = e.summarizeExport("greet");
  assert.ok(s !== undefined);
  const hooks: ImportHooks = { importValue: (_src, imported) => (imported === "greet" ? s : undefined) };
  const i = analyze(
    parse(`import { greet } from "./m";
           export const hello = greet;
           const v = greet();`),
    kCFA(1),
    hooks,
  );
  assert.equal(i.domain.typeSig(i.valueOfVar("v")), "str");
  // the re-exported binding round-trips as a callable summary (id defaulted
  // to the import label by the normalizer)
  const re = i.summarizeBinding("hello");
  assert.ok(re !== undefined && re.fn !== undefined);
  assert.equal(re.fn.id, "./m#greet");
  assert.deepEqual(re.fn.result, { strs: ["hi"] });
});
