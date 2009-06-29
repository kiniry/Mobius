type name;
type ref;
const unique null : ref;
var Heap : [ref, name]int;
const FIELD : name;
var x : int;
var y : int;
var z : int;
procedure M(this : ref);
  modifies z, y, x;
  

implementation M(this : ref) {
  start: x := Heap[this, FIELD]; goto $$start~a;
  $$start~a: y := Heap[this, FIELD]; goto id$then, StartCheck, id$else;
  StartCheck: assert ((x == y) && (x == Heap[this, FIELD])); return;
  id$then: y := 3; goto $$then~a;
  $$then~a: z := x; goto join, ThenCheck;
  ThenCheck: assert (((3 == y) && (x == z)) && (x == Heap[this, FIELD])); return;
  id$else: z := Heap[this, FIELD]; goto ElseCheck, join;
  ElseCheck: assert (((x == y) && (y == z)) && (x == Heap[this, FIELD])); return;
  join: assume ((x == z) && (x == Heap[this, FIELD])); return;
  
}

procedure M0(this : ref);
  modifies z, y, x;
  

implementation M0(this : ref) {
  start: x := Heap[this, FIELD]; goto $$start~b;
  $$start~b: y := Heap[this, FIELD]; goto id$then, id$else;
  id$then: y := 3; goto $$then~b;
  $$then~b: z := x; goto join;
  id$else: z := Heap[this, FIELD]; goto join;
  join: assert (y == 3); return;
  
}

procedure M1(this : ref);
  modifies z, y, x;
  

implementation M1(this : ref) {
  start: x := Heap[this, FIELD]; goto $$start~c;
  $$start~c: y := Heap[this, FIELD]; goto id$then, id$else;
  id$then: y := 3; goto $$then~c;
  $$then~c: z := x; goto join;
  id$else: z := Heap[this, FIELD]; goto join;
  join: assert (x == y); return;
  
}

procedure M2(this : ref);
  modifies z, y, x;
  

implementation M2(this : ref) {
  start: x := Heap[this, FIELD]; goto $$start~d;
  $$start~d: y := Heap[this, FIELD]; goto id$then, id$else;
  id$then: y := 3; goto $$then~d;
  $$then~d: z := x; goto join;
  id$else: z := Heap[this, FIELD]; goto join;
  join: assert (x == z); return;
  
}

procedure M3(this : ref);
  modifies z, y, x;
  

implementation M3(this : ref) {
  start: x := Heap[this, FIELD]; goto $$start~e;
  $$start~e: y := Heap[this, FIELD]; goto id$then, id$else;
  id$then: y := 3; goto $$then~e;
  $$then~e: z := x; goto join;
  id$else: z := Heap[this, FIELD]; goto join;
  join: assert (z == y); return;
  
}

