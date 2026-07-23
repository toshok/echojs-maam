// typeof over every dialect value kind.
function f() { return 1; }
var o = { x: 1 };
var u;
typeof 1 + ":" + typeof "s" + ":" + typeof true + ":" + typeof u + ":" + typeof null + ":" + typeof f + ":" + typeof o + ":" + typeof Math.floor;
