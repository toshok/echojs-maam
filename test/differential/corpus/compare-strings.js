// String relationals are lexicographic, NOT numeric (harness-found machine bug).
var a = "a" < "b";
var b = "10" < "9";
var c = "abc" <= "abc";
var d = "z" > "yy";
var e = 1 < "2";
"" + a + b + c + d + e;
