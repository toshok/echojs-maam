// Bitwise and shift semantics: ToInt32/ToUint32 wrapping, sign propagation.
var a = (0xff & 0x0f) | 0x30;
var b = ~5;
var c = -8 >> 1;
var d = -8 >>> 28;
var e = 1 << 31;
var f = (5 ^ 3) << 2;
a + b + c + d + e + f;
