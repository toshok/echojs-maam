// DELIBERATE SKIP (analysis timeout): for-of iteration is nondeterministic in
// the machine (smashed array elements) and concrete time is unbounded, so an
// accumulating for-of loop never converges — the exploration grows forever.
// The harness's per-file worker timeout turns that into a VISIBLE skip.
// Machine limitation, tracked in the Phase 3.5 results note.
var sum = 0;
for (var v of [1, 2, 3, 4]) sum = sum + v;
sum;
