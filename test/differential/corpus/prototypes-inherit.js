// Prototype-chain inheritance with method override and a super-style call, in
// the post-desugar dialect shape: methods assigned onto F.prototype, chain
// linked with Object.setPrototypeOf (what class-extends lowers to).
// (`F.prototype = Object.create(...)` — prototype REASSIGNMENT — is unmodeled
// and degrades visibly; tracked in the Phase 3.5 results note.)
function Shape(name) { this.name = name; }
Shape.prototype.area = function () { return 0; };
Shape.prototype.describe = function () { return this.name + ":" + this.area(); };
function Square(side) { Shape.call(this, "square"); this.side = side; }
Object.setPrototypeOf(Square.prototype, Shape.prototype);
Square.prototype.area = function () { return this.side * this.side; };
var s = new Square(5);
var base = new Shape("blob");
s.describe() + "|" + base.describe();
