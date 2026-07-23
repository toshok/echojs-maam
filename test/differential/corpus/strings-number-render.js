// Number parsing intrinsics and number→string round trips.
var a = parseInt("42");
var b = parseInt("0x10", 16);
var c = parseInt("12px");
var d = parseFloat("3.5e2");
var e = Number("  7  ");
var f = String(1 / 3);
"" + a + ":" + b + ":" + c + ":" + d + ":" + e + ":" + f;
