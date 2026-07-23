// Exact Math static coverage, including the round-half-up edge.
var a = Math.floor(-3.5);
var b = Math.ceil(-3.5);
var c = Math.round(-2.5);
var d = Math.round(2.5);
var e = Math.trunc(-3.9);
var f = Math.sign(-7);
var g = Math.sqrt(2);
var h = Math.min(3, -1, 2) + Math.max(3, -1, 2);
var i = Math.hypot(3, 4);
var j = Math.atan2(1, 1);
"" + a + ":" + b + ":" + c + ":" + d + ":" + e + ":" + f + ":" + g + ":" + h + ":" + i + ":" + j;
