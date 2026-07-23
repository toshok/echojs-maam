// Object literals, nested reads, methods with this.
var point = {
  x: 3,
  y: 4,
  len: function () { return Math.sqrt(this.x * this.x + this.y * this.y); }
};
var box = { inner: { value: 10 } };
point.len() + box.inner.value;
