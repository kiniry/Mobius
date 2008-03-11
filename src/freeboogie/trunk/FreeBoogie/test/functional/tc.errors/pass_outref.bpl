procedure swap(x : ref, y : ref) returns (xx : ref, yy : ref);
  ensures x == yy;
  ensures y == xx;

implementation swap(x : ref, y : ref) returns (xx : ref, yy : ref) {
entry:
  assume yy_1 == x;
  assume xx_1 == y;
  goto post_check;

post_check:
  assert x == yy_1;
  assert y == xx_1;
  return;
}


procedure even(x : int) returns (y : int);
  ensures x / 2 == y / 2;
  ensures y % 2 == 0;

implementation even(x : int) returns (y : int) {
entry:
  assume y_1 == x;
  goto a, b;
a:
  assume x % 2 == 0;
  goto copy1;

copy1:
  assume y_2 == y_1;
  goto post_check;

b:
  assume x % 2 != 0;
  assume y_2 == y_1 - 1;
  goto post_check;

post_check:
  assert x / 2 == y_2 / 2;
  assert y_2 % 2 == 0;
  return;
}

var mem : [ref] int;

procedure pswap(x : ref, y : ref);
  ensures mem[x] == old(mem[y]);
  ensures mem[y] == old(mem[x]);

implementation pswap(x : ref, y : ref) {
  var tmp : int;
entry:
  assume tmp_1 == mem[x];
  assume mem_1 == store(mem, x, mem[y]); // ** array store **
  assume mem_2 == store(mem_1, y, tmp);
  goto post_check;

post_check:
  assert mem_2[x] == mem[y];
  assert mem_2[y] == mem[x];
  return;
}

