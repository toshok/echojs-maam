// Mutual recursion.
function isEven(n) { return n === 0 ? true : isOdd(n - 1); }
function isOdd(n) { return n === 0 ? false : isEven(n - 1); }
"" + isEven(10) + isOdd(7) + isEven(3);
