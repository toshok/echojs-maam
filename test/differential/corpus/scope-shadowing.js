// let/const block shadowing (no-TDZ dialect: declaration-order use only).
let x = 1;
function probe() {
  let x = 2;
  { let x = 3; x = x + 1; }
  return x;
}
const y = probe();
x + ":" + y;
