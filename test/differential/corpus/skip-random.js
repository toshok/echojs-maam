// DELIBERATE SKIP: Math.random is nondeterministic — never exact. This file
// exists to prove skips are visible, not silent.
var r = Math.random();
r < 2;
