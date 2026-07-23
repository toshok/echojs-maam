// Array literals: exact length; index reads go through the smashed elements
// bucket (PASS-CONTAINS territory, deliberately kept in the corpus).
var a = [10, 20, 30];
var len = a.length;
var first = a[0];
len * 100 + first;
