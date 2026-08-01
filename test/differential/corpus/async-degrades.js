// Async (and generator) functions are not modeled: their bindings hold ⊤
// and calling one degrades as an unknown call, so this file SKIPs — with
// the reason printed — instead of silently mis-modeling `f()` as its
// body's return value (a real call returns a Promise). The file starts
// running for real the day the machine models async.
async function f() {
  return 1;
}
var p = f();
var tag = typeof p;
tag;
