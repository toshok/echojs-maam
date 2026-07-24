// Shapes lane (a): a representation transition — the same field re-assigned
// num → str interns a different type-aware hidden class; the concrete
// intermediates all need abstract witnesses.
var o = { v: 1 };
o.v = o.v + 1;
o.v = "s" + o.v;
o.v;
