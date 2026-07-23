// Constructor functions, prototype methods, instance state.
function Point(x, y) { this.x = x; this.y = y; }
Point.prototype.norm1 = function () { return Math.abs(this.x) + Math.abs(this.y); };
var p = new Point(-3, 4);
var q = new Point(1, 2);
p.norm1() + q.norm1();
