import { test } from "node:test";
import assert from "node:assert/strict";

import { analyze, concreteEval } from "../src/index.js";
import type { Program } from "../src/lang/ast.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

// These tests hand-build the ESTree shape EchoJS emits *after* its desugar passes
// — including the `%`-prefixed intrinsic identifiers acorn cannot parse — to
// confirm the analyzer consumes the real IR. Feed the analyzer a JSON dump of the
// AST at that stage: `analyze(JSON.parse(dump), spec)`.

// --- a minimal ESTree builder ----------------------------------------------

type N = Record<string, unknown>;
const id = (name: string): N => ({ type: "Identifier", name });
const lit = (value: unknown): N => ({ type: "Literal", value });
const mem = (o: N, p: string): N => ({ type: "MemberExpression", object: o, property: id(p), computed: false });
const call = (callee: N, args: N[]): N => ({ type: "CallExpression", callee, arguments: args, optional: false });
const fnExpr = (params: string[], body: N[]): N => ({
  type: "FunctionExpression",
  id: null,
  params: params.map(id),
  body: { type: "BlockStatement", body },
});
const fnDecl = (name: string, params: string[], body: N[]): N => ({
  type: "FunctionDeclaration",
  id: id(name),
  params: params.map(id),
  body: { type: "BlockStatement", body },
});
const ret = (argument: N): N => ({ type: "ReturnStatement", argument });
const exprStmt = (expression: N): N => ({ type: "ExpressionStatement", expression });
const assign = (left: N, right: N): N => ({ type: "AssignmentExpression", operator: "=", left, right });
const bin = (operator: string, left: N, right: N): N => ({ type: "BinaryExpression", operator, left, right });
const prop = (key: string, value: N): N => ({ type: "Property", key: lit(key), value, kind: "init", computed: false });
const obj = (props: N[]): N => ({ type: "ObjectExpression", properties: props });
const varDecl = (name: string, init: N): N =>
  ({ type: "VariableDeclaration", kind: "var", declarations: [{ type: "VariableDeclarator", id: id(name), init }] });
const program = (body: N[]): Program => ({ type: "Program", body, sourceType: "script" } as unknown as Program);

const defineProperty = (target: N, key: string, desc: N): N =>
  exprStmt(call(mem(id("Object"), "defineProperty"), [target, lit(key), desc]));

function concreteResult(prog: Program): unknown[] {
  const r = analyze(prog, concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set]
    .map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t === "undef" ? "undefined" : v.t))
    .sort();
}

// --- the tests -------------------------------------------------------------

test("%objectCreate and %setPrototypeOf intrinsics build a prototype chain", () => {
  // var Base = (function(){ function Base(){} Object.defineProperty(Base.prototype,"greet",{value:...}); return Base; })();
  const baseIIFE = call(
    fnExpr([], [
      fnDecl("Base", [], []),
      defineProperty(mem(id("Base"), "prototype"), "greet", obj([prop("value", fnExpr([], [ret(lit("hi"))]))])),
      ret(id("Base")),
    ]),
    [],
  );
  // var Derived = (function(%super){ function Derived(){} %setPrototypeOf(Derived.prototype, %objectCreate(%super.prototype)); return Derived; })(Base);
  const derivedIIFE = call(
    fnExpr(["%super"], [
      fnDecl("Derived", [], []),
      exprStmt(
        call(id("%setPrototypeOf"), [
          mem(id("Derived"), "prototype"),
          call(id("%objectCreate"), [mem(id("%super"), "prototype")]),
        ]),
      ),
      ret(id("Derived")),
    ]),
    [id("Base")],
  );
  const prog = program([
    varDecl("Base", baseIIFE),
    varDecl("Derived", derivedIIFE),
    varDecl("d", { type: "NewExpression", callee: id("Derived"), arguments: [] }),
    exprStmt(call(mem(id("d"), "greet"), [])), // d.greet()  ⇒ inherited "hi"
  ]);
  assert.deepEqual(concreteResult(prog), ["hi"]);
});

test("%constructSuper runs the parent constructor on `this`", () => {
  // var Animal = (function(){ function Animal(name){ this.name = name; } %setConstructorKindBase(Animal); return Animal; })();
  const animalIIFE = call(
    fnExpr([], [
      fnDecl("Animal", ["name"], [exprStmt(assign(mem({ type: "ThisExpression" }, "name"), id("name")))]),
      exprStmt(call(id("%setConstructorKindBase"), [id("Animal")])),
      ret(id("Animal")),
    ]),
    [],
  );
  // var Dog = (function(%super){ function Dog(name){ %constructSuper(%super, name); } %setPrototypeOf(Dog.prototype, %objectCreate(%super.prototype)); return Dog; })(Animal);
  const dogIIFE = call(
    fnExpr(["%super"], [
      fnDecl("Dog", ["name"], [exprStmt(call(id("%constructSuper"), [id("%super"), id("name")]))]),
      exprStmt(
        call(id("%setPrototypeOf"), [
          mem(id("Dog"), "prototype"),
          call(id("%objectCreate"), [mem(id("%super"), "prototype")]),
        ]),
      ),
      ret(id("Dog")),
    ]),
    [id("Animal")],
  );
  const prog = program([
    varDecl("Animal", animalIIFE),
    varDecl("Dog", dogIIFE),
    varDecl("d", { type: "NewExpression", callee: id("Dog"), arguments: [lit("rex")] }),
    exprStmt(mem(id("d"), "name")), // d.name ⇒ "rex" (set by the super constructor)
  ]);
  assert.deepEqual(concreteResult(prog), ["rex"]);
});

test("Object.defineProperties accessor descriptor from the desugarer works", () => {
  // var Rect = (function(){ function Rect(w,h){this.w=w;this.h=h;} Object.defineProperties(Rect.prototype, { area: { get: function(){ return this.w*this.h; } } }); return Rect; })();
  const rectIIFE = call(
    fnExpr([], [
      fnDecl("Rect", ["w", "h"], [
        exprStmt(assign(mem({ type: "ThisExpression" }, "w"), id("w"))),
        exprStmt(assign(mem({ type: "ThisExpression" }, "h"), id("h"))),
      ]),
      exprStmt(
        call(mem(id("Object"), "defineProperties"), [
          mem(id("Rect"), "prototype"),
          obj([
            prop(
              "area",
              obj([prop("get", fnExpr([], [ret(bin("*", mem({ type: "ThisExpression" }, "w"), mem({ type: "ThisExpression" }, "h")))]))]),
            ),
          ]),
        ]),
      ),
      ret(id("Rect")),
    ]),
    [],
  );
  const prog = program([
    varDecl("Rect", rectIIFE),
    varDecl("r", { type: "NewExpression", callee: id("Rect"), arguments: [lit(3), lit(4)] }),
    exprStmt(mem(id("r"), "area")), // r.area ⇒ 12 (via the inherited getter)
  ]);
  assert.deepEqual(concreteResult(prog), [12]);
});
