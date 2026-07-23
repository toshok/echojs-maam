// Exact String.prototype coverage (pure primitive methods).
var s = "Hello, World";
var a = s.toUpperCase();
var b = s.slice(7, 12);
var c = s.indexOf("o");
var d = s.charCodeAt(0);
var e = "ab".repeat(3);
var f = "  pad  ".trim();
var g = s.includes("World") && s.startsWith("He") && !s.endsWith("x");
a + "|" + b + "|" + c + "|" + d + "|" + e + "|" + f + "|" + g;
