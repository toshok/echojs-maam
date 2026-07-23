// DELIBERATE SKIP (review R1): a destructuring-pattern LEAF captured by a
// closure created before its declaration. Hoisted pattern-leaf capture is not
// modeled; the normalizer counts it as a degraded binding so this file SKIPs
// visibly instead of answering 1 (real JS: 9) with zero degradation.
var f = function () { a = 9; };
var [a, b] = [1, 2];
f();
a;
