var Heap : [ref]int;
function P(x : int) returns (bool);
function Q(x : int, y : int) returns (bool);
procedure Callee(x : int) returns (y : int);
  requires P(x);
  modifies Heap;
  ensures Q(x, y);

procedure Caller(v : int) returns (w : int) {
entry:
  call w := Callee(v); return;
}

