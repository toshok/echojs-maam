// Numeric relational edges: NaN comparisons are all false; -0 === 0.
var nan = 0 / 0;
var r1 = nan < 1;
var r2 = nan >= nan;
var r3 = -0 === 0;
var r4 = 2 <= 2;
"" + r1 + r2 + r3 + r4;
