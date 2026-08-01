// BigInts flowing through functions, branches, and loops — bigint-valued
// call results and joins must stay ⊤ (never `num`) on the abstract side.
function twice(x) {
  return x * 2n;
}
function pick(flag) {
  if (flag) return 1n;
  return 100;
}
var acc = 0n;
var i = 0;
while (i < 4) {
  acc = acc + twice(2n);
  i = i + 1;
}
var mixed = pick(true);
var alsoMixed = pick(false);
"" + acc + "," + mixed + "," + alsoMixed;
