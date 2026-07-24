// Shapes lane (b): freeze/seal semantics in sloppy mode — writes and deletes
// fail silently, delete on a sealed object returns false.
var f = Object.freeze({ a: 1, b: 2 });
f.a = 99;
f.c = 3;
var s = Object.seal({ p: 1 });
s.p = 2;
var r1 = Object.isFrozen(f) + "," + f.a + "," + ("c" in f);
var r2 = Object.isSealed(s) + "," + s.p + "," + (delete s.p);
r1 + "|" + r2;
