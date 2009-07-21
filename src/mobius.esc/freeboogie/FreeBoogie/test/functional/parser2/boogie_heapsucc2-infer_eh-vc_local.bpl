type name;
type ref;
const unique null : ref;
var Heap : [ref, name]int;
const FIELD : name;
const OTHERFIELD : name;
var x : int;
var y : int;
var z : int;
procedure M(this : ref);
  modifies Heap, y, x;
  

implementation M(this : ref) {
  start: x := Heap[this, FIELD]; goto StartCheck, id$then, id$else;
  StartCheck: assert (x == Heap[this, FIELD]); return;
  id$then: y := x; goto $$then~a;
  $$then~a: Heap := Heap[this, OTHERFIELD := 2]; goto ThenCheck, join;
  ThenCheck: assert (((y == x) && (x == Heap[this, FIELD])) && (Heap[this, OTHERFIELD] == 2)); return;
  id$else: y := Heap[this, FIELD]; goto ElseCheck, join;
  ElseCheck: assert ((y == x) && (x == Heap[this, FIELD])); return;
  join: goto JoinCheck;
  JoinCheck: assert ((y == x) && (x == Heap[this, FIELD])); return;
  
}

