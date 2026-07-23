// Negative zero: produced by * and unary minus; === conflates, 1/x separates.
var z = 0 * -1;
var conflated = z === 0;
var separated = 1 / z === -Infinity ? "neg" : "pos";
conflated && separated === "neg" ? z : "wrong";
