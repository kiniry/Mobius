type name;
type ref;
const unique null : ref;
var Heap : [ref, name]int;
const FIELD : name;
const OTHERFIELD : name;
var x : int;
var y : int;
var z : int;
procedure M(this : ref, that : ref);
  modifies Heap, z, y;
  

implementation M(this : ref, that : ref) {
  start: y := Heap[this, FIELD]; goto $$start~b;
  $$start~b: Heap := Heap[that, FIELD := x]; goto $$start~a;
  $$start~a: z := Heap[this, FIELD]; goto StartCheck;
  StartCheck: assert ((x == Heap[that, FIELD]) && (z == Heap[this, FIELD])); return;
  
}

