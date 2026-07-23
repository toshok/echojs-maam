// Function values: identity equality, functions as data.
function f(x) { return x; }
function g(x) { return x; }
var same = f === f;
var diff = f === g;
var picked = (1 < 2 ? f : g)(7);
"" + same + diff + picked;
