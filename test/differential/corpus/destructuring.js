// Object/array patterns with defaults (post-desugar dialect shapes).
var { a, b = 5 } = { a: 2 };
var [x, y] = [7, 8];
a + b + x + y;
