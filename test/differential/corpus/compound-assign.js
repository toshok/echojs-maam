// Compound assignment operators (review F6a: the machine handles these
// exactly; the corpus previously never exercised them). `**=` lives in
// arith-basic.js instead — esprima cannot parse the exponentiation family,
// and keeping it out of THIS file preserves its ejs-lane coverage.
var x = 10;
x += 5; x -= 2; x *= 3; x /= 2; x %= 12;
var b = 0xf0;
b &= 0x3c; b |= 0x03; b ^= 0xff; b <<= 2; b >>= 1; b >>>= 1;
var s = "a";
s += "b"; s += 1;
x + ":" + b + ":" + s;
