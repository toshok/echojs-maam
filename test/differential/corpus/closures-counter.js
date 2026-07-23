// A closure over a mutable binding: state survives across calls.
function makeCounter(start) {
  var n = start;
  return function () { n = n + 1; return n; };
}
var c1 = makeCounter(10);
var c2 = makeCounter(100);
c1(); c1(); c2();
c1() + c2();
