procedure swap(x : ref, y : ref) returns (xx : ref, yy : ref);
  ensures x == yy;
  ensures y == xx;

implementation swap(x : ref, y : ref) returns (xx : ref, yy : ref) {
entry:
  yy := x;
  xx := y;
  goto post_check;

post_check:
  assert x == yy; // simulates desugaring of ensures
  assert y == xx;
  return;
}


procedure even(x : int) returns (y : int);
  ensures x / 2 == y / 2;
  ensures y % 2 == 0;

implementation even(x : int) returns (y : int) {
entry:
  y := x;
  goto a, b;
a:
  assume x % 2 == 0;
  goto post_check;

b:
  assume x % 2 != 0;
  y := y - 1;
  goto post_check;

post_check:
  assert old(x) / 2 == y / 2;
  assert y % 2 == 0;
  return;
}

var mem : [ref] int;

procedure pswap(x : ref, y : ref);
  ensures mem[x] == old(mem[y]);
  ensures mem[y] == old(mem[x]);

implementation pswap(x : ref, y : ref) {
  var tmp : int;
entry:
  tmp := mem[x];
  mem[x] := mem[y];
  mem[y] := tmp;
  goto post_check;

post_check:
  assert mem[old(x)] == old(mem[old(y)]);
  assert mem[old(y)] == old(mem[old(x)]);
  return;
}

