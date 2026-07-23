// DELIBERATE SKIP: array prototype methods touch the smashed elements bucket —
// unknowable exactly, so the concrete run degrades visibly and the harness skips.
var joined = [1, 2, 3].join(",");
joined;
