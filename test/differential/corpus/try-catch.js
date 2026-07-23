// throw / catch / finally ordering, with two documented machine
// over-approximations in play:
//   - the handler is modeled as ALWAYS reachable (nondet, caught value ⊤), so
//     this file is membership-checked (PASS-CONTAINS) and the caught value must
//     not flow into the final string;
//   - `return` INSIDE try/finally would bypass the finalizer in the model
//     (normTry routes fall-through completion only — harness finding, tracked
//     in the Phase 3.5 results note), so completion here falls through and the
//     function returns after the try statement.
var trace = "";
function risky(x) {
  var out;
  try {
    if (x > 2) throw "boom:" + x;
    trace = trace + "ok";
    out = x;
  } catch (e) {
    trace = trace + "caught";
    out = -1;
  } finally {
    trace = trace + ";";
  }
  return out;
}
var r = risky(1) + risky(5);
r + ":" + trace;
