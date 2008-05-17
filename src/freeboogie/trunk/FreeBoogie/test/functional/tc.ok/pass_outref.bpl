procedure swap(x : ref, y : ref) returns (xx : ref, yy : ref);
  ensures x == yy;
  ensures y == xx;

implementation swap(x : ref, y : ref) returns (xx : ref, yy : ref) {
  var xx_1 : ref, yy_1 : ref; // added
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
  var y_1 : int, y_2 : int; // added
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

var heap<x> : [ref, <x>name]x;

procedure pswap(x : ref, y : ref);
  ensures mem[x] == old(mem[y]);
  ensures mem[y] == old(mem[x]);

function store1d<x,z>(oa: [x]z, idx : x, val : z) returns (na : [x]z);
function store2d<x,y,z>([x,y]z,x,y,z) returns ([x,y]z);

procedure boo<x>(heap : [ref, <x>name]x, o : ref, n : <x>name) returns ($ : x) {
  var t : x;
  entry:
    $ := heap[o,n];
    return;
}

implementation pswap(x : ref, y : ref) {
  var tmp : int;
  var tmp_1 : int, mem_1 : [ref] int, mem_2 : [ref] int; // added
entry:
  assume tmp_1 == mem[x];
  assume mem_1 == store1d(mem, x, mem[y]); // ** array store **
  assume mem_2 == store1d(mem_1, y, tmp);
  goto post_check;

post_check:
  assert mem_2[x] == mem[y];
  assert mem_2[y] == mem[x];
  return;
}

