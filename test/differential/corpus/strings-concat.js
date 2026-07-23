// Concatenation and template literals over mixed primitives.
var n = 3;
var s = "x" + n + true + null + undefined;
var t = `n=${n} sum=${n + 1} flag=${n > 2}`;
s + "|" + t;
