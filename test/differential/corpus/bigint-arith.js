// BigInt arithmetic on matching operands: the concrete domain evaluates
// these exactly; the abstract domain has no bigint constituent and widens
// every bigint to ⊤ — the containment lane checks it never claims `num`
// for a bigint-valued node (the ⊤-operand refinement bug class).
var a = 10n;
var b = 3n;
var sum = a + b;
var diff = a - b;
var prod = a * b;
var quot = a / b;
var rem = a % b;
var pow = a ** b;
var neg = -a;
var not = ~a;
var s =
  "" + sum + "," + diff + "," + prod + "," + quot + "," + rem + "," + pow + "," + neg + "," + not;
s;
