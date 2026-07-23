// break / continue interplay.
var acc = 0;
for (var i = 0; i < 20; i = i + 1) {
  if (i % 2 === 0) continue;
  if (i > 11) break;
  acc = acc + i;
}
acc;
