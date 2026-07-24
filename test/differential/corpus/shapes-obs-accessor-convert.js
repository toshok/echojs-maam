// Shapes lane (b): converting a data property to an accessor (dictionary
// migration in a shaped runtime) — behavior and enumeration order preserved.
var o = { a: 1, b: 2 };
var log = "";
Object.defineProperty(o, "a", {
  get: function () { return 42; },
  set: function (v) { log += "set" + v; },
  enumerable: true,
  configurable: true
});
o.a = 7;
Object.keys(o).join(",") + "|" + o.a + "|" + log + "|" + o.b;
