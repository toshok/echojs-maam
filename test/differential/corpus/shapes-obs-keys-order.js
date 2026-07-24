// Shapes lane (b): Object.keys insertion order — literal keys first, then
// appended fields; a second object built field-by-field from empty.
var o = { b: 1, a: 2 };
o.c = 3;
o.d = 4;
var p = {};
p.z = 1;
p.y = 2;
p.x = 3;
Object.keys(o).join(",") + "|" + Object.keys(p).join(",");
