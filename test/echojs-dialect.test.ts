import { test } from "node:test";
import assert from "node:assert/strict";

import { analyze, concreteEval, kCFA, NormalizeError } from "../src/index.js";
import type { Program } from "../src/lang/ast.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

// These tests hand-build the ESTree *dialect* EchoJS emits (old-esprima style):
// `TryStatement.handlers`/`guardedHandlers` arrays, function-level `defaults` +
// `rest`, module wrappers left inline at the toplevel, and `%`-intrinsics the
// analyzer does not model. Each shape must be consumed (or degrade with a count),
// never crash the analysis.

// --- a minimal ESTree builder (echojs-dialect flavored) ----------------------

type N = Record<string, unknown>;
const id = (name: string): N => ({ type: "Identifier", name });
const lit = (value: unknown): N => ({ type: "Literal", value });
const call = (callee: N, args: N[]): N => ({ type: "CallExpression", callee, arguments: args, optional: false });
const ret = (argument: N): N => ({ type: "ReturnStatement", argument });
const exprStmt = (expression: N): N => ({ type: "ExpressionStatement", expression });
const assign = (left: N, right: N): N => ({ type: "AssignmentExpression", operator: "=", left, right });
const bin = (operator: string, left: N, right: N): N => ({ type: "BinaryExpression", operator, left, right });
const block = (body: N[]): N => ({ type: "BlockStatement", body });
const varDecl = (name: string, init: N): N =>
  ({ type: "VariableDeclaration", kind: "var", declarations: [{ type: "VariableDeclarator", id: id(name), init }] });
const program = (body: N[]): Program => ({ type: "Program", body, sourceType: "script" } as unknown as Program);

/** A function declaration carrying the echojs dialect extras. */
const fnDecl = (
  name: string,
  params: string[],
  body: N[],
  extras: { defaults?: (N | null)[]; rest?: N | null } = {},
): N => ({
  type: "FunctionDeclaration",
  id: id(name),
  params: params.map(id),
  defaults: extras.defaults ?? [],
  rest: extras.rest ?? null,
  body: block(body),
});

/** An echojs-dialect catch clause (`guard` is the SpiderMonkey-era extension). */
const catchClause = (param: N | null, body: N[], guard: N | null = null): N =>
  ({ type: "CatchClause", param, guard, body: block(body) });

/** An echojs-dialect try statement: `handlers`/`guardedHandlers` arrays, no `handler`. */
const tryStmt = (body: N[], handlers: N[], guardedHandlers: N[] = [], finalizer: N[] | null = null): N => ({
  type: "TryStatement",
  block: block(body),
  handlers,
  guardedHandlers,
  finalizer: finalizer ? block(finalizer) : null,
});

function analyzeConcrete(prog: Program) {
  return analyze(prog, concreteEval());
}

function concreteResult(prog: Program): unknown[] {
  const r = analyzeConcrete(prog);
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set]
    .map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t === "undef" ? "undefined" : v.t))
    .sort();
}

// --- try/catch: `handlers` array + `guardedHandlers` ------------------------

test("echojs `handlers` array: the catch clause is analyzed, not dropped", () => {
  // var x = 0; try { x = 1; } catch (e) { x = 2; }  x;
  const prog = program([
    varDecl("x", lit(0)),
    tryStmt([exprStmt(assign(id("x"), lit(1)))], [catchClause(id("e"), [exprStmt(assign(id("x"), lit(2)))])]),
    exprStmt(id("x")),
  ]);
  // x = 2 happens ONLY in the handler: seeing it proves the clause was analyzed.
  assert.deepEqual(concreteResult(prog), [1, 2]);
});

test("echojs `guardedHandlers`: a guarded clause is a reachable alternative", () => {
  // var x = 0; try { x = 1; } catch (e if e === 1) { x = 3; }  x;
  const prog = program([
    varDecl("x", lit(0)),
    tryStmt(
      [exprStmt(assign(id("x"), lit(1)))],
      [],
      [catchClause(id("e"), [exprStmt(assign(id("x"), lit(3)))], bin("===", id("e"), lit(1)))],
    ),
    exprStmt(id("x")),
  ]);
  assert.deepEqual(concreteResult(prog), [1, 3]);
});

test("the catch parameter is bound (to \u22a4) before its guard is evaluated", () => {
  // var y = 0; try { y = 1; } catch (e if (y = (e === undefined))) {}  y;
  // The guard's dataflow reads `e` \u2014 bound as \u22a4 (any value may be thrown) \u2014
  // and stores the comparison into `y`: seeing \u22a4 in the result pins that the
  // param binding wraps the guard. If the binding were missing, the guard's
  // read of `e` would be \u22a5 and the handler path would contribute NO value.
  const prog = program([
    varDecl("y", lit(0)),
    tryStmt(
      [exprStmt(assign(id("y"), lit(1)))],
      [],
      [catchClause(id("e"), [], assign(id("y"), bin("===", id("e"), id("undefined"))))],
    ),
    exprStmt(id("y")),
  ]);
  assert.deepEqual(concreteResult(prog), [1, "top"]);
});

test("echojs handlers + finally: both paths flow through the finalizer", () => {
  // var x = 0; try { x = 1; } catch (e) { x = 2; } finally { x = 7; }  x;
  const prog = program([
    varDecl("x", lit(0)),
    tryStmt(
      [exprStmt(assign(id("x"), lit(1)))],
      [catchClause(id("e"), [exprStmt(assign(id("x"), lit(2)))])],
      [],
      [exprStmt(assign(id("x"), lit(7)))],
    ),
    exprStmt(id("x")),
  ]);
  assert.deepEqual(concreteResult(prog), [7]);
});

test("a destructuring catch parameter is rejected loudly, not silently unbound", () => {
  const pattern: N = { type: "ObjectPattern", properties: [] };
  const prog = program([
    tryStmt([exprStmt(lit(1))], [catchClause(pattern, [exprStmt(lit(2))])]),
    exprStmt(lit(0)),
  ]);
  assert.throws(() => analyzeConcrete(prog), NormalizeError);
});

// --- functions: old-esprima `defaults` + `rest` ------------------------------

test("`defaults`: an omitted argument takes its default (which may read earlier params)", () => {
  // function f(a, b = a + 1) { return b; }  f(10);
  const prog = program([
    fnDecl("f", ["a", "b"], [ret(id("b"))], { defaults: [null, bin("+", id("a"), lit(1))] }),
    exprStmt(call(id("f"), [lit(10)])),
  ]);
  // The default's *value* (11, a number) is observable — an unevaluated or
  // skipped default would surface as `undefined` here instead.
  assert.deepEqual(concreteResult(prog), [11]);
});

test("`defaults`: a supplied argument wins over the default", () => {
  const prog = program([
    fnDecl("f", ["a", "b"], [ret(id("b"))], { defaults: [null, bin("+", id("a"), lit(1))] }),
    exprStmt(call(id("f"), [lit(10), lit(5)])),
  ]);
  assert.deepEqual(concreteResult(prog), [5]);
});

test("`rest`: extra arguments are tolerated and the positional params still bind", () => {
  // function g(a) /* ...r */ { return a; }  g(1, 2, 3);
  const prog = program([
    fnDecl("g", ["a"], [ret(id("a"))], { rest: id("r") }),
    exprStmt(call(id("g"), [lit(1), lit(2), lit(3)])),
  ]);
  assert.deepEqual(concreteResult(prog), [1]);
});

test("`rest`: the rest name binds an (empty) array and the degradation is observable", () => {
  const prog = program([
    fnDecl("g", ["a"], [ret(id("r"))], { rest: id("r") }),
    exprStmt(call(id("g"), [lit(1), lit(2), lit(3)])),
  ]);
  const r = analyzeConcrete(prog);
  const set = r.result as FinSet<CVal<Loc>>;
  // The right type tag (an array object, not `undefined`)…
  assert.deepEqual([...set].map((v) => v.t), ["obj"]);
  // …and the imprecision is NOT invisible: no unknown call was involved, but
  // the degraded binding shows up in both the metrics and the warnings.
  assert.equal(r.metrics.unknownCalls, 0);
  assert.equal(r.metrics.degradedBindings, 1);
  const warns = r.warnings().filter((w) => w.kind === "degraded-binding");
  assert.equal(warns.length, 1);
  assert.match(warns[0]!.message, /`r`/);
});

// --- unknown `%`-intrinsics: degrade and count, never throw ------------------

test("an unknown %intrinsic call degrades and is counted in metrics.unknownCalls", () => {
  // var t = %arrayFromSpread(1, 2);  t;
  const prog = program([
    varDecl("t", call(id("%arrayFromSpread"), [lit(1), lit(2)])),
    exprStmt(id("t")),
  ]);
  const r = analyzeConcrete(prog);
  const set = r.result as FinSet<CVal<Loc>>;
  assert.deepEqual([...set].map((v) => v.t), ["top"]); // \u22a4, not a made-up `undefined`
  assert.equal(r.metrics.unknownCalls, 1);
  assert.ok(r.warnings().some((w) => w.kind === "unknown-call"));
});

test("an unknown %intrinsic in return position degrades (no tail call to an unbound %name)", () => {
  // function h() { return %makeGenerator(); }  h();
  const prog = program([
    fnDecl("h", [], [ret(call(id("%makeGenerator"), []))]),
    exprStmt(call(id("h"), [])),
  ]);
  const r = analyzeConcrete(prog);
  const set = r.result as FinSet<CVal<Loc>>;
  assert.deepEqual([...set].map((v) => v.t), ["top"]); // \u22a4, not a made-up `undefined`
  assert.equal(r.metrics.unknownCalls, 1);
});

test("%constructSuperApply (formerly a hard error) now degrades with a count", () => {
  const prog = program([
    varDecl("t", call(id("%constructSuperApply"), [lit(0)])),
    exprStmt(id("t")),
  ]);
  const r = analyzeConcrete(prog);
  assert.equal(r.metrics.unknownCalls, 1);
});

test("a scope-BOUND %-named identifier is an ordinary callee, not an intrinsic", () => {
  // function inc(x) { return x + 1; }
  // function wrap(%fn) { var t = %fn(1); return %fn(t); }   wrap(inc);
  // `%fn` is a real parameter (like `%super` in class-desugar output): both the
  // let-position and the return-position call must invoke the bound closure —
  // 3 comes out, and nothing is counted as an unknown call.
  const prog = program([
    fnDecl("inc", ["x"], [ret(bin("+", id("x"), lit(1)))]),
    fnDecl("wrap", ["%fn"], [varDecl("t", call(id("%fn"), [lit(1)])), ret(call(id("%fn"), [id("t")]))]),
    exprStmt(call(id("wrap"), [id("inc")])),
  ]);
  const r = analyzeConcrete(prog);
  const set = r.result as FinSet<CVal<Loc>>;
  assert.deepEqual([...set].map((v) => (v.t === "num" ? v.v : v.t)), [3]);
  assert.equal(r.metrics.unknownCalls, 0);
});

// --- toplevel module wrappers left inline by the echojs desugar --------------

test("import/export wrappers inline in a Program body are tolerated", () => {
  // import { imp } from "./m"; export var x = 5; export { x };
  // export default (function () { return 42; })();  var y = imp;  x + 1;
  const prog = program([
    {
      type: "ImportDeclaration",
      specifiers: [{ type: "ImportSpecifier", local: id("imp"), imported: id("imp") }],
      source: lit("./m"),
    },
    { type: "ExportNamedDeclaration", declaration: varDecl("x", lit(5)), specifiers: [], source: null },
    { type: "ExportNamedDeclaration", declaration: null, specifiers: [{ type: "ExportSpecifier", local: id("x"), exported: id("x") }], source: null },
    {
      type: "ExportDefaultDeclaration",
      declaration: call(
        { type: "FunctionExpression", id: null, params: [], defaults: [], rest: null, body: block([ret(lit(42))]) },
        [],
      ),
    },
    varDecl("y", id("imp")), // the imported binding exists (degraded to `undefined`)
    exprStmt(bin("+", id("x"), lit(1))),
  ]);
  // The exported declaration is analyzed through its wrapper: x + 1 ⇒ 6.
  assert.deepEqual(concreteResult(prog), [6]);
});

// --- Phase 1 dialect coverage: templates, for-of, patterns, \u22a4 ------------

const tmplElem = (cooked: string, tail: boolean): N => ({ type: "TemplateElement", value: { cooked, raw: cooked }, tail });
const tmpl = (parts: string[], exprs: N[]): N => ({
  type: "TemplateLiteral",
  quasis: parts.map((p, i) => tmplElem(p, i === parts.length - 1)),
  expressions: exprs,
});
const arr = (elements: N[]): N => ({ type: "ArrayExpression", elements });
const mem = (o: N, p: string): N => ({ type: "MemberExpression", object: o, property: id(p), computed: false });
const fnExprN = (params: string[], body: N[]): N => ({
  type: "FunctionExpression", id: null, params: params.map(id), defaults: [], rest: null, body: block(body),
});
const objLit = (fields: [string, N][]): N => ({
  type: "ObjectExpression",
  properties: fields.map(([k, v]) => ({ type: "Property", key: lit(k), value: v, kind: "init", computed: false })),
});
const objPattern = (fields: [string, N][]): N => ({
  type: "ObjectPattern",
  properties: fields.map(([k, v]) => ({ type: "Property", key: lit(k), value: v, kind: "init", computed: false })),
});
const forOf = (name: string, right: N, body: N[]): N => ({
  type: "ForOfStatement",
  left: { type: "VariableDeclaration", kind: "var", declarations: [{ type: "VariableDeclarator", id: id(name), init: null }] },
  right,
  body: block(body),
});

function analyzeAbstract(prog: Program) {
  return analyze(prog, kCFA(1, "flow-sensitive", "call-site", 64, false, false, false, 512));
}

test("template literal: concatenation with ToString, string result", () => {
  // var x = `a${1 + 2}b`;  x;
  const prog = program([
    varDecl("x", tmpl(["a", "b"], [bin("+", lit(1), lit(2))])),
    exprStmt(id("x")),
  ]);
  assert.deepEqual(concreteResult(prog), ["a3b"]);
});

test("template literal over a degraded (\u22a4) expression is still string-typed", () => {
  // var u = %unk(); var x = `v=${u}`;  x;
  const prog = program([
    varDecl("u", call(id("%unk"), [])),
    varDecl("x", tmpl(["v=", ""], [id("u")])),
    exprStmt(id("x")),
  ]);
  const r = analyzeAbstract(prog);
  assert.equal(r.domain.typeSig(r.valueOfVar("x")), "str");
  assert.equal(r.domain.typeSig(r.valueOfVar("u")), "\u22a4");
});

test("tagged template: callee/args evaluated, result \u22a4, counted as unknown call", () => {
  // function tag(){ return 1; }  var t = tag`a${2}b`;  t;
  const prog = program([
    fnDecl("tag", [], [ret(lit(1))]),
    varDecl("t", { type: "TaggedTemplateExpression", tag: id("tag"), quasi: tmpl(["a", "b"], [lit(2)]) }),
    exprStmt(id("t")),
  ]);
  const r = analyzeConcrete(prog);
  const set = r.result as FinSet<CVal<Loc>>;
  assert.deepEqual([...set].map((v) => v.t), ["top"]);
  assert.equal(r.metrics.unknownCalls, 1);
});

test("for-of over a literal array: loop var gets the element-type join, nothing degraded", () => {
  // var s = 0; for (var x of [1, 2]) s = x;  s;
  // (abstract only: like for-in, the nondet exit-or-iterate loop model does
  // not terminate under exact concrete time)
  const prog = program([
    varDecl("s", lit(0)),
    forOf("x", arr([lit(1), lit(2)]), [exprStmt(assign(id("s"), id("x")))]),
    exprStmt(id("s")),
  ]);
  const r = analyzeAbstract(prog);
  assert.equal(r.domain.typeSig(r.valueOfVar("x")), "num");
  assert.equal(r.metrics.unknownCalls, 0);
});

test("for-of over an unknown value: loop var is \u22a4 and the degradation is counted", () => {
  // var u = %unk(); for (var x of u) {}  0;
  const prog = program([
    varDecl("u", call(id("%unk"), [])),
    forOf("x", id("u"), []),
    exprStmt(lit(0)),
  ]);
  const r = analyzeAbstract(prog);
  assert.equal(r.domain.typeSig(r.valueOfVar("x")), "\u22a4");
  assert.ok(r.metrics.unknownCalls >= 2, `unknownCalls=${r.metrics.unknownCalls}`); // %unk call + iteration
});

test("object-pattern params bind property values", () => {
  // function f({a, b}) { return a + b; }  f({a: 1, b: 2});
  const prog = program([
    fnDecl("f", [], [ret(bin("+", id("a"), id("b")))]),
    exprStmt(call(id("f"), [objLit([["a", lit(1)], ["b", lit(2)]])])),
  ]);
  (prog.body[0] as unknown as { params: N[] }).params = [objPattern([["a", id("a")], ["b", id("b")]])];
  assert.deepEqual(concreteResult(prog), [3]);
});

test("pattern default referencing an earlier binding (EIR `=== undefined` rule)", () => {
  // function g({x, y = x + 1}) { return y; }  g({x: 5});
  const prog = program([
    fnDecl("g", [], [ret(id("y"))]),
    exprStmt(call(id("g"), [objLit([["x", lit(5)]])])),
  ]);
  (prog.body[0] as unknown as { params: N[] }).params = [
    objPattern([["x", id("x")], ["y", { type: "AssignmentPattern", left: id("y"), right: bin("+", id("x"), lit(1)) }]]),
  ];
  assert.deepEqual(concreteResult(prog), [6]);
});

test("whole-pattern parameter default applies before destructuring", () => {
  // function d({a} = {a: 9}) { return a; }  d();
  const prog = program([
    fnDecl("d", [], [ret(id("a"))], { defaults: [objLit([["a", lit(9)]])] }),
    exprStmt(call(id("d"), [])),
  ]);
  (prog.body[0] as unknown as { params: N[] }).params = [objPattern([["a", id("a")]])];
  assert.deepEqual(concreteResult(prog), [9]);
});

test("array-pattern params read the (smashed) element bucket", () => {
  // function h([a, b]) { return b; }  h([7, 7]);
  // Array reads are element-join \u2294 undefined (the smashed model), so both
  // 7 and undefined are possible outcomes \u2014 pinned as documentation.
  const prog = program([
    fnDecl("h", [], [ret(id("b"))]),
    exprStmt(call(id("h"), [arr([lit(7), lit(7)])])),
  ]);
  (prog.body[0] as unknown as { params: N[] }).params = [{ type: "ArrayPattern", elements: [id("a"), id("b")] }];
  assert.deepEqual(concreteResult(prog), [7, "undefined"]);
});

test("array-pattern rest binds an array of the source's elements (echojs SpreadElement form)", () => {
  // function r([a, ...rs]) { return rs; }  r([1, 2, 3]);
  const prog = program([
    fnDecl("r", [], [ret(id("rs"))]),
    exprStmt(call(id("r"), [arr([lit(1), lit(2), lit(3)])])),
  ]);
  (prog.body[0] as unknown as { params: N[] }).params = [
    { type: "ArrayPattern", elements: [id("a"), { type: "SpreadElement", argument: id("rs") }] },
  ];
  const rc = analyzeConcrete(prog);
  assert.deepEqual([...(rc.result as FinSet<CVal<Loc>>)].map((v) => v.t), ["obj"]);
  const ra = analyzeAbstract(prog);
  assert.equal(ra.domain.typeSig(ra.valueOfVar("rs")), "obj");
  assert.equal(ra.metrics.unknownCalls, 0); // tracked source array: nothing degraded
});

test("destructuring variable declarations decompose into property reads", () => {
  // var {p, q} = {p: 1, q: 2};  p + q;
  const prog = program([
    {
      type: "VariableDeclaration",
      kind: "var",
      declarations: [{ type: "VariableDeclarator", id: objPattern([["p", id("p")], ["q", id("q")]]), init: objLit([["p", lit(1)], ["q", lit(2)]]) }],
    },
    exprStmt(bin("+", id("p"), id("q"))),
  ]);
  assert.deepEqual(concreteResult(prog), [3]);
});

// --- \u22a4-degradation and cap observability ---------------------------------

test("an unknown call's result is \u22a4, and typeof still knows it is a string", () => {
  // var t = %unk(); var s = typeof t;  — s must be string-typed, NOT the
  // constant "undefined" the old undefined-degradation would have produced.
  const prog = program([
    varDecl("t", call(id("%unk"), [])),
    varDecl("s", { type: "UnaryExpression", operator: "typeof", argument: id("t"), prefix: true }),
    exprStmt(id("s")),
  ]);
  const r = analyzeAbstract(prog);
  assert.equal(r.domain.typeSig(r.valueOfVar("t")), "\u22a4");
  assert.equal(r.domain.typeSig(r.valueOfVar("s")), "str");
});

test("stateCap saturation is observable in metrics and describe()", () => {
  // Three call sites against stateCap=1 forces widened returns.
  const prog = program([
    fnDecl("id1", ["v"], [ret(id("v"))]),
    exprStmt(call(id("id1"), [lit(1)])),
    exprStmt(call(id("id1"), [lit(2)])),
    exprStmt(call(id("id1"), [lit(3)])),
  ]);
  const capped = analyze(prog, kCFA(1, "flow-sensitive", "call-site", 0, false, false, false, /*stateCap*/ 1));
  assert.ok(capped.metrics.stateCapHits > 0, `stateCapHits=${capped.metrics.stateCapHits}`);
  assert.equal(capped.metrics.stateCapFuncs, 1);
  assert.match(capped.describe(), /caps:\s+stateCap [1-9]/);
  const uncapped = analyze(prog, kCFA(1, "flow-sensitive", "call-site", 0, false, false, false, 0));
  assert.equal(uncapped.metrics.stateCapHits, 0); // natural convergence is distinguishable
});

test("shapeCap saturation is observable in metrics", () => {
  // Field-by-field growth under weak updates against shapeCap=1.
  const prog = program([
    varDecl("o", objLit([])),
    exprStmt(assign(mem(id("o"), "a"), lit(1))),
    exprStmt(assign(mem(id("o"), "b"), lit(2))),
    exprStmt(assign(mem(id("o"), "c"), lit(3))),
    exprStmt(lit(0)),
  ]);
  const capped = analyze(prog, kCFA(0, "flow-sensitive", "call-site", /*shapeCap*/ 1));
  assert.ok(capped.metrics.shapeCapHits > 0, `shapeCapHits=${capped.metrics.shapeCapHits}`);
  const uncapped = analyze(prog, kCFA(0, "flow-sensitive", "call-site", 0));
  assert.equal(uncapped.metrics.shapeCapHits, 0);
});

// --- Chunk D review fixes: pins ---------------------------------------------

test("unknown `new` degrades to \u22a4 \u2014 property reads on it are not confidently undefined", () => {
  // import { Foo } from "m"; var f = new Foo(); var b = f.bar;  b;
  const prog = program([
    {
      type: "ImportDeclaration",
      specifiers: [{ type: "ImportSpecifier", local: id("Foo"), imported: id("Foo") }],
      source: lit("m"),
    },
    varDecl("f", { type: "NewExpression", callee: id("Foo"), arguments: [] }),
    varDecl("b", mem(id("f"), "bar")),
    exprStmt(id("b")),
  ]);
  const r = analyzeAbstract(prog);
  assert.equal(r.domain.typeSig(r.valueOfVar("f")), "\u22a4");
  assert.equal(r.domain.typeSig(r.valueOfVar("b")), "\u22a4");
  assert.ok(r.metrics.unknownCalls >= 1);
});

test("import degradation is counted, not silent", () => {
  const prog = program([
    {
      type: "ImportDeclaration",
      specifiers: [
        { type: "ImportSpecifier", local: id("a"), imported: id("a") },
        { type: "ImportSpecifier", local: id("b"), imported: id("b") },
      ],
      source: lit("m"),
    },
    exprStmt(lit(0)),
  ]);
  const r = analyzeAbstract(prog);
  assert.equal(r.metrics.degradedBindings, 2);
  const warns = r.warnings().filter((w) => w.kind === "degraded-binding");
  assert.equal(warns.length, 2);
  assert.match(warns[0]!.message, /import/);
});

test("rest parameter `length` is unknown, not the constant 1", () => {
  // function g(a) /* ...r */ { return r.length; }  g(1, 2, 3);
  const prog = program([
    fnDecl("g", ["a"], [ret(mem(id("r"), "length"))], { rest: id("r") }),
    exprStmt(call(id("g"), [lit(1), lit(2), lit(3)])),
  ]);
  const r = analyzeAbstract(prog);
  assert.equal(r.domain.typeSig(r.result), "\u22a4"); // joined up to \u22a4, never a pinned constant
});

test("array-pattern rest `length` is unknown, not the constant 1", () => {
  const prog = program([
    fnDecl("r", [], [ret(mem(id("rs"), "length"))]),
    exprStmt(call(id("r"), [arr([lit(1), lit(2), lit(3)])])),
  ]);
  (prog.body[0] as unknown as { params: N[] }).params = [
    { type: "ArrayPattern", elements: [id("a"), { type: "SpreadElement", argument: id("rs") }] },
  ];
  const r = analyzeAbstract(prog);
  assert.equal(r.domain.typeSig(r.result), "\u22a4");
});

test("for-of observes loop-body mutation of the iterated array", () => {
  // var a = [1]; for (var x of a) { a[1] = "s"; }  \u2014 x must join num AND str.
  const prog = program([
    varDecl("a", arr([lit(1)])),
    forOf("x", id("a"), [
      exprStmt({
        type: "AssignmentExpression", operator: "=",
        left: { type: "MemberExpression", object: id("a"), property: lit(1), computed: true },
        right: lit("s"),
      }),
    ]),
    exprStmt(lit(0)),
  ]);
  const r = analyzeAbstract(prog);
  assert.equal(r.domain.typeSig(r.valueOfVar("x")), "num|str");
  assert.equal(r.metrics.unknownCalls, 0);
});

test("for-of over an element bucket containing closures degrades (hand-rolled iterable fingerprint)", () => {
  // var o = {}; o[0] = function () { return 1; }; for (var x of o) {}  0;
  const prog = program([
    varDecl("o", objLit([])),
    exprStmt({
      type: "AssignmentExpression", operator: "=",
      left: { type: "MemberExpression", object: id("o"), property: lit(0), computed: true },
      right: fnExprN([], [ret(lit(1))]),
    }),
    forOf("x", id("o"), []),
    exprStmt(lit(0)),
  ]);
  const r = analyzeAbstract(prog);
  assert.equal(r.domain.typeSig(r.valueOfVar("x")), "\u22a4");
  assert.ok(r.metrics.unknownCalls >= 1);
});
