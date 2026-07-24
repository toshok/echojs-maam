import { test } from "node:test";
import assert from "node:assert/strict";

import { analyze, kCFA } from "../src/index.js";
import type { Program } from "../src/lang/ast.js";
import type { Node } from "estree";

// The node-identity type oracle (`nodeTypes()` / `typeOfNode()`): hand-built
// echojs-dialect trees, holding references to the exact node objects, then
// asserting the TypeSig each reports after analysis. Identity is the key —
// the last test pins that a structurally-identical foreign node gets nothing.

type N = Record<string, unknown>;
const id = (name: string): N => ({ type: "Identifier", name });
const lit = (value: unknown): N => ({ type: "Literal", value });
const call = (callee: N, args: N[]): N => ({ type: "CallExpression", callee, arguments: args, optional: false });
const ret = (argument: N): N => ({ type: "ReturnStatement", argument });
const exprStmt = (expression: N): N => ({ type: "ExpressionStatement", expression });
const bin = (operator: string, left: N, right: N): N => ({ type: "BinaryExpression", operator, left, right });
const block = (body: N[]): N => ({ type: "BlockStatement", body });
const varDecl = (name: string, init: N): N =>
  ({ type: "VariableDeclaration", kind: "var", declarations: [{ type: "VariableDeclarator", id: id(name), init }] });
const fnDecl = (name: string, params: N[], body: N[]): N =>
  ({ type: "FunctionDeclaration", id: id(name), params, defaults: [], rest: null, body: block(body) });
const program = (body: N[]): Program => ({ type: "Program", body, sourceType: "script" } as unknown as Program);
const arr = (elements: N[]): N => ({ type: "ArrayExpression", elements });
const objLit = (fields: [string, N][]): N => ({
  type: "ObjectExpression",
  properties: fields.map(([k, v]) => ({ type: "Property", key: lit(k), value: v, kind: "init", computed: false })),
});

const spec = () => kCFA(1, "flow-sensitive", "call-site", 64, false, false, false, 512);
const run = (prog: Program) => analyze(prog, spec());
const typeOf = (prog: Program, n: N) => run(prog).typeOfNode(n as unknown as Node);

test("(a) an Identifier read site reports its binding's type", () => {
  const readX = id("x"); // the read in `var y = x;`
  const prog = program([varDecl("x", lit(1)), varDecl("y", readX), exprStmt(id("y"))]);
  assert.equal(typeOf(prog, readX), "num");
});

test("(b) a BinaryExpression node reports the operator's result type", () => {
  const sum = bin("+", lit(1), lit(2));
  const cmp = bin("<", id("a"), lit(10));
  const prog = program([varDecl("a", sum), varDecl("b", cmp), exprStmt(id("b"))]);
  assert.equal(typeOf(prog, sum), "num");
  assert.equal(typeOf(prog, cmp), "bool");
});

test("(c) a call site reports the callee's return type, joined over contexts", () => {
  // function p(x){ return x; } function w(v){ return p(v); } w(1); w("s");
  // Both wrapper calls funnel through ONE `p(v)` call node: its type must be
  // the JOIN "num|str", not either alone.
  const innerCall = call(id("p"), [id("v")]);
  const prog = program([
    fnDecl("p", [id("x")], [ret(id("x"))]),
    fnDecl("w", [id("v")], [{ type: "ReturnStatement", argument: null }]),
    exprStmt(call(id("w"), [lit(1)])),
    exprStmt(call(id("w"), [lit("s")])),
  ]);
  // give w a real body referencing the shared call node
  ((prog.body[1] as unknown as { body: { body: N[] } }).body).body = [varDecl("r", innerCall), ret(id("r"))];
  assert.equal(typeOf(prog, innerCall), "num|str");
});

test("(d) a node in dead code returns undefined (fail-soft, not 'never')", () => {
  const deadBin = bin("+", lit(1), lit(2));
  const prog = program([
    { type: "IfStatement", test: lit(false), consequent: block([exprStmt(deadBin)]), alternate: null },
    exprStmt(lit(0)),
  ]);
  assert.equal(typeOf(prog, deadBin), undefined);
});

test("(e) a for-of loop variable Identifier reports the element type", () => {
  const loopVar = id("x");
  const prog = program([
    varDecl("a", arr([lit(1), lit(2)])),
    {
      type: "ForOfStatement",
      left: { type: "VariableDeclaration", kind: "var", declarations: [{ type: "VariableDeclarator", id: loopVar, init: null }] },
      right: id("a"),
      body: block([]),
    },
    exprStmt(lit(0)),
  ]);
  assert.equal(typeOf(prog, loopVar), "num");
});

test("(f) pattern leaf Identifiers report their destructured types", () => {
  // var {p, q} = {p: 1, q: "s"};
  const leafP = id("p");
  const leafQ = id("q");
  const prog = program([
    {
      type: "VariableDeclaration",
      kind: "var",
      declarations: [{
        type: "VariableDeclarator",
        id: {
          type: "ObjectPattern",
          properties: [
            { type: "Property", key: lit("p"), value: leafP, kind: "init", computed: false },
            { type: "Property", key: lit("q"), value: leafQ, kind: "init", computed: false },
          ],
        },
        init: objLit([["p", lit(1)], ["q", lit("s")]]),
      }],
    },
    exprStmt(lit(0)),
  ]);
  const r = run(prog);
  assert.equal(r.typeOfNode(leafP as unknown as Node), "num");
  assert.equal(r.typeOfNode(leafQ as unknown as Node), "str");
});

test("(g) node identity, not structure: an identical foreign node reports nothing", () => {
  const realRead = id("x");
  const impostor = id("x"); // structurally identical, different object
  const prog = program([varDecl("x", lit(1)), varDecl("y", realRead), exprStmt(id("y"))]);
  const r = run(prog);
  assert.equal(r.typeOfNode(realRead as unknown as Node), "num");
  assert.equal(r.typeOfNode(impostor as unknown as Node), undefined);
});

test("(h) a ⊤-degraded binding's read site reports ⊤", () => {
  const readT = id("t");
  const prog = program([varDecl("t", call(id("%unk"), [])), varDecl("u", readT), exprStmt(id("u"))]);
  assert.equal(typeOf(prog, readT), "⊤");
});

test("nodeTypes() is a stable identity-keyed map (one build, both surfaces agree)", () => {
  const sum = bin("+", lit(1), lit(2));
  const prog = program([varDecl("a", sum), exprStmt(id("a"))]);
  const r = run(prog);
  const m1 = r.nodeTypes();
  const m2 = r.nodeTypes();
  assert.equal(m1, m2); // cached — one build per result
  assert.equal(m1.get(sum as unknown as Node), r.typeOfNode(sum as unknown as Node));
});

test("reassignment widening: a variable-mapped node reports the variable's full join", () => {
  // var x = 1 + 2; x = "s";  — the BinaryExpression maps to `x` (first mapping
  // wins), so it reports the join of EVERYTHING x ever holds: "num|str".
  // Sound (\u2287 actual) for guarded consumption; NOT a value-at-site reading.
  const sum = bin("+", lit(1), lit(2));
  const prog = program([
    varDecl("x", sum),
    exprStmt({ type: "AssignmentExpression", operator: "=", left: id("x"), right: lit("s") }),
    exprStmt(id("x")),
  ]);
  assert.equal(typeOf(prog, sum), "num|str");
});

test("unbound (free) identifier reads are unmapped — no aliasing with fresh names", () => {
  // `t$0` is a plausible fresh-minted core name; a free identifier spelled the
  // same way must NOT report some temporary's type.
  const freeRead = id("t$0");
  const prog = program([varDecl("y", freeRead), exprStmt(id("y"))]);
  assert.equal(typeOf(prog, freeRead), undefined);
});

test("a node spliced into two binding sites (different core names) is poisoned: undefined", () => {
  // The same Identifier OBJECT declares two distinct bindings (echojs
  // common-ids splicing style). Any single answer would be wrong for the
  // other site \u2014 the oracle must report nothing.
  const shared = id("x");
  const decl = (init: N): N =>
    ({ type: "VariableDeclaration", kind: "var", declarations: [{ type: "VariableDeclarator", id: shared, init }] });
  const prog = program([decl(lit(1)), decl(lit("s")), exprStmt(id("x"))]);
  assert.equal(typeOf(prog, shared), undefined);
});

test("a node remapped to the SAME name stays mapped (benign duplicate)", () => {
  // The same Identifier READ object appears twice in statement position; both
  // reads resolve to the same binding name, so the duplicate is kept.
  const sharedRead = id("x");
  const prog = program([
    varDecl("x", lit(1)),
    exprStmt(sharedRead),
    exprStmt(sharedRead),
    exprStmt(id("x")),
  ]);
  assert.equal(typeOf(prog, sharedRead), "num");
});

// --- RestElement params (the Chunk E gap: post-desugar echojs keeps `...rest` in params) ---

test("a trailing RestElement param is accepted and treated exactly like the dialect `rest`", () => {
  // function g(a, ...r) { return r; }  g(1, 2, 3);
  const restTarget = id("r");
  const prog = program([
    {
      type: "FunctionDeclaration",
      id: id("g"),
      params: [id("a"), { type: "RestElement", argument: restTarget }],
      defaults: [],
      body: block([ret(id("r"))]),
    },
    exprStmt(call(id("g"), [lit(1), lit(2), lit(3)])),
  ]);
  const r = run(prog);
  // array-of-⊤ binding, counted degradation — identical to the `.rest` path
  assert.equal(r.domain.typeSig(r.valueOfVar("r")), "obj");
  assert.equal(r.metrics.degradedBindings, 1);
  assert.ok(r.warnings().some((w) => w.kind === "degraded-binding" && /rest parameter/.test(w.message)));
  // and the declaration node maps to the binding
  assert.equal(r.typeOfNode(restTarget as unknown as Node), "obj");
});

test("positional params before a RestElement still bind positionally", () => {
  // function g(a, ...r) { return a; }  g(7, 8, 9);  — concrete: a = 7
  const prog = program([
    {
      type: "FunctionDeclaration",
      id: id("g"),
      params: [id("a"), { type: "RestElement", argument: id("r") }],
      defaults: [],
      body: block([ret(id("a"))]),
    },
    exprStmt(call(id("g"), [lit(7), lit(8), lit(9)])),
  ]);
  const r = run(prog);
  assert.equal(r.domain.typeSig(r.valueOfVar("a")), "num");
});

// --- receiver shapes (echojs shapes-plan P4.3) -------------------------------

test("receiverShapesOfNode: a literal receiver reports one terminal shape with its ordered witness", () => {
  const recv = id("p"); // the object node of `p.x`
  const member = { type: "MemberExpression", object: recv, property: id("x"), computed: false };
  const prog = program([
    varDecl("p", objLit([["x", lit(1)], ["y", lit(2)]])),
    varDecl("s", member),
    exprStmt(id("s")),
  ]);
  const r = run(prog);
  const shapes = r.receiverShapesOfNode(recv as unknown as Node);
  assert.ok(shapes && shapes.length === 1, "one terminal shape");
  const s = shapes![0]!;
  assert.deepEqual(
    [...s.fields].map((f) => `${f.name}:${f.type}`).sort(),
    ["x:num", "y:num"]
  );
  assert.deepEqual(r.fieldOrderOfShape(s), ["x", "y"]);
});

test("receiverShapesOfNode: construction intermediates are subsumed to the terminal", () => {
  const recv = id("q");
  const member = { type: "MemberExpression", object: recv, property: id("b"), computed: false };
  const prog = program([
    varDecl("q", objLit([["a", lit(1)]])),
    // q.b = 2 — the receiver passes through {a} then settles at {a, b}
    exprStmt({
      type: "AssignmentExpression",
      operator: "=",
      left: { type: "MemberExpression", object: id("q"), property: id("b"), computed: false },
      right: lit(2),
    }),
    varDecl("t", member),
    exprStmt(id("t")),
  ]);
  const r = run(prog);
  const shapes = r.receiverShapesOfNode(recv as unknown as Node);
  assert.ok(shapes && shapes.length === 1, "intermediates subsumed");
  assert.equal(shapes![0]!.fields.length, 2);
  assert.deepEqual(r.fieldOrderOfShape(shapes![0]!), ["a", "b"]);
});

test("receiverShapesOfNode: a foreign node fail-softs to undefined", () => {
  const prog = program([varDecl("p", objLit([["x", lit(1)]])), exprStmt(id("p"))]);
  const r = run(prog);
  assert.equal(r.receiverShapesOfNode(id("nowhere") as unknown as Node), undefined);
});

test("fieldOrderOfShape: the megamorphic top shape has no ordered witness", () => {
  const prog = program([varDecl("p", objLit([["x", lit(1)]])), exprStmt(id("p"))]);
  const r = run(prog);
  const top = r.shapesOfVar; // silence unused-var pattern; query ⊤ via the table below
  void top;
  // build ⊤ indirectly: any shape with megamorphic=true reports undefined
  assert.equal(r.fieldOrderOfShape({ id: -1, fields: [], megamorphic: true }), undefined);
});
