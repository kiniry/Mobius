type name;
type ref;
const unique null : ref;
var Heap : [ref, name]int;
const FIELD : name;
var x : int;
var y : int;
var z : int;
procedure M(this : ref);
  modifies z, y;
  

implementation M(this : ref) {
  start: y := Heap[this, FIELD]; goto $$start~a;
  $$start~a: z := Heap[this, FIELD]; goto StartCheck, Return;
  StartCheck: assert ((y == Heap[this, FIELD]) && (z == y)); return;
  Return: return;
  
}

