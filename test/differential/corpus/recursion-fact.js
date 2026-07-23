// Direct recursion with an accumulator variant.
function fact(n) { return n < 2 ? 1 : n * fact(n - 1); }
function factAcc(n, acc) { return n < 2 ? acc : factAcc(n - 1, n * acc); }
fact(10) === factAcc(10, 1) ? fact(10) : -1;
