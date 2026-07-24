// Shapes lane (b): delete-then-readd moves the key to the END of enumeration
// order (dictionary-migration territory in a shaped runtime).
var o = { a: 1, b: 2, c: 3 };
delete o.b;
var mid = Object.keys(o).join(",");
o.b = 9;
mid + "|" + Object.keys(o).join(",") + "|" + o.b;
