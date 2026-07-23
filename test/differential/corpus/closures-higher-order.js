// Higher-order composition and partial application.
function compose(f, g) { return function (x) { return f(g(x)); }; }
function add(a) { return function (b) { return a + b; }; }
function double(x) { return x * 2; }
var addFive = add(5);
var h = compose(addFive, double);
h(10) + compose(double, addFive)(10);
