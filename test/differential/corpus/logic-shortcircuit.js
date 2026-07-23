// && / || return operand VALUES, not booleans; evaluation order via effects.
var log = "";
function t(tag, v) { log = log + tag; return v; }
var a = t("a", 0) || t("b", "x");
var c = t("c", 2) && t("d", null);
"" + a + ":" + c + ":" + log;
