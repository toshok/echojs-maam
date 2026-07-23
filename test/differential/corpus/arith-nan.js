// NaN production and propagation; NaN never equals itself.
var nan = 0 / 0;
var viaUndef = 1 + undefined;
var eq = nan === nan;
var neq = nan !== nan;
"" + (nan !== nan) + ":" + (eq === false) + ":" + isNaN(viaUndef);
