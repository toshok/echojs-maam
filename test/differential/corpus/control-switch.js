// switch with fallthrough and default.
function classify(x) {
  var r = "";
  switch (x) {
    case 1:
    case 2:
      r = "small";
      break;
    case 3:
      r = "three";
    case 4:
      r = r + "+four";
      break;
    default:
      r = "big";
  }
  return r;
}
classify(1) + "|" + classify(3) + "|" + classify(9);
