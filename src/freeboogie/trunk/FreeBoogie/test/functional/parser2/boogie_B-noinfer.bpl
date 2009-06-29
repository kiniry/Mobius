type name;
type ref;
const unique null : ref;
var Heap : [ref, name]int;
const N : name;
procedure Q0();
implementation Q0() {
  var h : int;
  entry: goto id$else;
  id$then: h := 15; goto id$end;
  id$else: assume (h == 0); goto id$end;
  id$end: assert (0 <= h); return;
  
}

procedure Q1();
implementation Q1() {
  var h : int;
  entry: goto id$else;
  id$then: h := -15; goto id$end;
  id$else: assume (h == 0); goto id$end;
  id$end: h := -h; goto $$end~a;
  $$end~a: assert (0 <= h); return;
  
}

procedure P0(this : ref);
  modifies Heap;
  

implementation P0(this : ref) {
  entry: goto id$else;
  id$then: Heap := Heap[this, N := 15]; goto id$end;
  id$else: assume (Heap[this, N] == 0); goto id$end;
  id$end: assert (0 <= Heap[this, N]); return;
  
}

procedure P1(this : ref);
  modifies Heap;
  

implementation P1(this : ref) {
  entry: goto id$else;
  id$then: Heap := Heap[this, N := -15]; goto id$end;
  id$else: assume (Heap[this, N] == 0); goto id$end;
  id$end: Heap := Heap[this, N := -Heap[this, N]]; goto $$end~b;
  $$end~b: assert (0 <= Heap[this, N]); return;
  
}

