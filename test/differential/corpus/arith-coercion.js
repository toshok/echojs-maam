// String/number/bool/null coercion in arithmetic (null is 0, not NaN).
var a = "5" * 2;
var b = "5" + 2;
var c = true + 1;
var d = 1 + null;
var e = "" - 1;
"" + a + ":" + b + ":" + c + ":" + d + ":" + e;
