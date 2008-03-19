var heap<x> : [ref, <x>name]x;

const fi : <int>name;
const fr : <int>name;

procedure swap<x>(o : ref, a : <x>name, b : <x>name) {
  var tmp : x;
  entry:
    tmp := heap[o,a];
    heap[o,a] := heap[o,b];
    heap[o,b] := tmp;
    return;
}

procedure main() {
  var o : ref;
  entry:
    call swap(o,fi,fr); /* swap<`int> should be inferred */
    call swap<`int>(o, fi, fi);
    call swap<`ref>(o, fr, fr); /* should give an error */
    return;
}

