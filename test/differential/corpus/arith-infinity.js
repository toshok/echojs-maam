// Infinity arithmetic edges.
var inf = 1 / 0;
var ninf = -1 / 0;
var indeterminate = inf + ninf;
var overflow = Number.MAX_VALUE * 2;
"" + inf + ":" + ninf + ":" + indeterminate + ":" + (overflow === inf);
