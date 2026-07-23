// Double rounding + number-to-string edges (exponential thresholds).
var tenth = 0.1 + 0.2;
var big = 1e21;
var small = 0.0000001;
"" + tenth + ":" + big + ":" + small + ":" + (tenth === 0.3);
