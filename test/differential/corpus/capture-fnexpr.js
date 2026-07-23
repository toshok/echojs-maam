// Review F1 probe: a function EXPRESSION created textually before the var it
// writes — pre-fix, the write was silently dropped (concrete said 0, node "x").
var f = function () { n = "x" + m; };
var n = 0;
var m = 7;
f();
n;
