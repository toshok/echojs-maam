// DELIBERATE SKIP (analysis timeout): same shape as skip-forof-diverges.js —
// for-in is nondet over the key set, so an accumulating loop diverges under
// unbounded concrete time.
var o = { a: 1, b: 2, c: 3 };
var total = 0;
for (var k in o) total = total + o[k];
total;
