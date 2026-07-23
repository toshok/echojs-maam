// Review F1 probe: object-literal-method variant of capture-fnexpr.js.
var counter = {
  tick: function () { count = count + 1; return count; }
};
var count = 40;
counter.tick();
counter.tick() + count;
