// Review F1 probe: arrow variant of capture-fnexpr.js.
var bump = () => { total = total + step; };
var total = 100;
var step = 11;
bump();
bump();
total;
