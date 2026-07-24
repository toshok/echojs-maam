// Shapes lane (b): enumeration order of constructor-built objects (a clean
// straight-line store prefix — the born-with-shape candidate) plus a field
// appended after construction.
function Pt(x, y) {
  this.x = x;
  this.y = y;
}
var a = new Pt(1, 2);
a.tag = "t";
Object.keys(a).join(",") + "|" + a.x + "," + a.y + "," + a.tag;
