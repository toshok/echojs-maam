import { test } from "node:test";
import assert from "node:assert/strict";

import { parse } from "../src/lang/parse.js";
import { analyze, concreteEval } from "../src/index.js";
import type { CVal } from "../src/lang/values.js";
import type { FinSet } from "../src/data/finset.js";
import type { Loc } from "../src/lang/core.js";

function concreteResult(src: string): unknown[] {
  const r = analyze(parse(src), concreteEval());
  const set = r.result as FinSet<CVal<Loc>>;
  return [...set]
    .map((v) => (v.t === "num" || v.t === "bool" || v.t === "str" ? v.v : v.t === "undef" ? "undefined" : v.t))
    .sort();
}

// EchoJS lowers `super(...)` to `%super.call(this, ...)` and `super.m(x)` to
// `(%super.prototype.m).call(this, x)`. We test the valid-JS `.call` form the
// desugarer produces (acorn cannot parse the `%super` identifier itself).

test("super constructor runs the parent body on the derived instance", () => {
  const src = `
    function Animal(name) { this.name = name; }
    function Dog(name) { Animal.call(this, name); this.legs = 4; }
    Object.setPrototypeOf(Dog.prototype, Object.create(Animal.prototype));
    const d = new Dog("rex");
    d.name;`;
  assert.deepEqual(concreteResult(src), ["rex"]);
});

test("the derived constructor also sets its own fields", () => {
  const src = `
    function Animal(name) { this.name = name; }
    function Dog(name) { Animal.call(this, name); this.legs = 4; }
    Object.setPrototypeOf(Dog.prototype, Object.create(Animal.prototype));
    const d = new Dog("rex");
    d.legs;`;
  assert.deepEqual(concreteResult(src), [4]);
});

test("`fn.call(thisArg, ...)` invokes with the given receiver, no allocation", () => {
  const src = `
    function greet(greeting) { return greeting + " " + this.who; }
    const ctx = { who: "world" };
    greet.call(ctx, "hello");`;
  assert.deepEqual(concreteResult(src), ["hello world"]);
});

test("super method call: (Super.prototype.m).call(this) chains to the parent method", () => {
  const src = `
    function Animal(n) { this.n = n; }
    Object.defineProperty(Animal.prototype, "describe", { value: function () { return this.n; } });
    function Dog(n) { Animal.call(this, n); }
    Object.setPrototypeOf(Dog.prototype, Object.create(Animal.prototype));
    Object.defineProperty(Dog.prototype, "describe", {
      value: function () { return Animal.prototype.describe.call(this) + "!"; }
    });
    const d = new Dog("rex");
    d.describe();`;
  assert.deepEqual(concreteResult(src), ["rex!"]);
});

test("`.call()` with no arguments uses an undefined receiver", () => {
  const src = `
    function f() { return 5; }
    f.call();`;
  assert.deepEqual(concreteResult(src), [5]);
});
