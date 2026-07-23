// Operator precedence and mixed integer/float arithmetic, plus the
// exponentiation family (`**`, `**=`) — esprima (the ejs front end) cannot
// parse `**`, so this file is the ejs lane's expected N/A.
var a = 2 + 3 * 4 - 10 / 4;
var b = (7 % 3) * 2 ** 3;
var c = a + b;
c **= 1;
c;
