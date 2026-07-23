// DELIBERATE SKIP (review F2): a nested-block `var` captured by a function in
// the enclosing scope. Function-scope hoisting out of blocks is not modeled;
// the normalizer counts it as a degraded binding so this file SKIPs visibly
// instead of silently computing on a ⊥ binding.
function s() { n = "x"; }
if (true) { var n = 0; }
s();
n;
