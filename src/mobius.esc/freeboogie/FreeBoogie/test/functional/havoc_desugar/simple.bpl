function P(int) returns (bool);
function Q(int, int) returns (bool);

procedure I() returns (x : int where P(x)) {
  var y : int where Q(x, y);
entry:
  havoc x;
  havoc y;
  havoc x, y;
  return;
}

