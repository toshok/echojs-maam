// BigInt bit operations, comparisons (including cross-type bigint/number
// relational and loose equality, which JS defines exactly), strict
// equality, truthiness, and typeof.
var a = 10n;
var b = 3n;
var band = a & b;
var bor = a | b;
var bxor = a ^ b;
var shl = a << 2n;
var shr = a >> 1n;
var cmp1 = a < 11;
var cmp2 = a >= b;
var cmp3 = 2 > b;
var eq1 = a === 10n;
var eq2 = a === b;
var eq3 = a == 10;
var eq4 = a != 3;
var t = 0n ? "t" : "f";
var ty = typeof a;
var s = "" + band + "," + bor + "," + bxor + "," + shl + "," + shr;
s + "|" + cmp1 + cmp2 + cmp3 + "|" + eq1 + eq2 + eq3 + eq4 + "|" + t + "|" + ty;
