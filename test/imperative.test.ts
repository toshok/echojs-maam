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

test("variable reassignment", () => {
  assert.deepEqual(concreteResult(`let x = 1; x = 5; x;`), [5]);
});

test("compound assignment on a variable", () => {
  assert.deepEqual(concreteResult(`let x = 10; x += 3; x -= 1; x;`), [12]);
});

test("compound assignment on a property", () => {
  assert.deepEqual(concreteResult(`const o = { n: 5 }; o.n *= 2; o.n;`), [10]);
});

test("postfix ++ returns the old value; prefix ++ returns the new", () => {
  assert.deepEqual(concreteResult(`let i = 0; const a = i++; a + "," + i;`), ["0,1"]);
  assert.deepEqual(concreteResult(`let i = 0; const a = ++i; a + "," + i;`), ["1,1"]);
});

test("sequence expression evaluates to its last operand", () => {
  assert.deepEqual(concreteResult(`const x = (1, 2, 3); x;`), [3]);
});

test("a closure sees mutations to a captured variable", () => {
  const src = `
    let count = 0;
    const inc = () => { count = count + 1; return count; };
    inc(); inc();
    inc();`;
  assert.deepEqual(concreteResult(src), [3]);
});

test("expanded operators: bitwise, shift, exponent, void, loose equality", () => {
  assert.deepEqual(concreteResult(`(5 & 3) + (1 << 4);`), [17]);
  assert.deepEqual(concreteResult(`2 ** 10;`), [1024]);
  assert.deepEqual(concreteResult(`~0;`), [-1]);
  assert.deepEqual(concreteResult(`void 5;`), ["undefined"]);
  assert.deepEqual(concreteResult(`(1 == "1");`), [true]);
  assert.deepEqual(concreteResult(`(null == undefined);`), [true]);
});

test("unary plus coerces to number", () => {
  assert.deepEqual(concreteResult(`+"42";`), [42]);
});
