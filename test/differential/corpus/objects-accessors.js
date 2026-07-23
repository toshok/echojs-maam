// Getter/setter dispatch via Object.defineProperty (the dialect's accessor shape).
var celsius = { _c: 25 };
Object.defineProperty(celsius, "f", {
  get: function () { return this._c * 9 / 5 + 32; },
  set: function (v) { this._c = (v - 32) * 5 / 9; }
});
var before = celsius.f;
celsius.f = 212;
before + ":" + celsius._c;
