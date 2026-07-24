// Shapes lane (a): a conditional field add gives one allocation site two
// terminal hidden classes — both must appear in the abstract shape set.
function mk(flag) {
  var o = { kind: 1 };
  if (flag) {
    o.extra = "e";
  }
  return o;
}
var a = mk(true);
var b = mk(false);
(a.extra === "e" ? 1 : 0) + (b.extra === undefined ? 1 : 0) + a.kind + b.kind;
