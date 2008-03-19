var heap<x> : [ref, <x>name]x;

procedure swap<x>(o : ref, a : <x>name, b : <x>name) {
  var tmp : x;
  entry:
    tmp := heap[o,a];
    heap[o,a] := heap[o,b];
    heap[o,b] := tmp;
    return;
}
