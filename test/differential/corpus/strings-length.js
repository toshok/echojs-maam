// String .length on literals and computed strings (was confident-undefined).
var s = "hello";
var t = s + "!!";
var empty = "";
s.length + t.length + empty.length + "abc".length;
