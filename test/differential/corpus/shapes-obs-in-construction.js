// Shapes lane (b): `in` during construction — THE born-with-shape observable
// (echojs shapes-plan P4.4): an object born with its terminal shape would
// wrongly report not-yet-assigned fields present. The fence must decline this
// constructor; behavior must match node either way.
function Point(x, y) {
  this.trace = ("x" in this) ? "1" : "0";
  this.x = x;
  this.trace += ("x" in this) ? "1" : "0";
  this.trace += ("y" in this) ? "1" : "0";
  this.y = y;
  this.trace += ("y" in this) ? "1" : "0";
}
var p = new Point(1, 2);
p.trace + "|" + ("x" in p) + "|" + ("z" in p);
