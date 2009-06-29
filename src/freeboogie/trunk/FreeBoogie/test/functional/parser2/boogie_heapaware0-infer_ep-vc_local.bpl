type name;
type ref;
const unique null : ref;
var Heap : [ref, name]int;
const N : name;
procedure M(this : ref);
implementation M(this : ref) {
  var i : int;
  var m : int;
  start: assume (0 <= Heap[this, N]); goto $$start~b;
  $$start~b: i := 0; goto $$start~a;
  $$start~a: m := 0; goto StartCheck, body, id$end;
  StartCheck: assert (((0 <= Heap[this, N]) && (i == 0)) && (m == 0)); return;
  body: assume (i < Heap[this, N]); goto BodyCheck, id$then, id$else;
  id$then: m := i; goto ThenCheck, join;
  id$else: goto ElseCheck, join;
  join: i := (i + 1); goto JoinCheck, body, id$end;
  BodyCheck: assert (((i < Heap[this, N]) && (0 <= m)) && (0 <= i)); return;
  ThenCheck: assert (((i < Heap[this, N]) && (0 <= i)) && (i == m)); return;
  ElseCheck: assert (((i < Heap[this, N]) && (0 <= m)) && (0 <= i)); return;
  JoinCheck: assert (((i <= Heap[this, N]) && (0 <= m)) && (1 <= i)); return;
  id$end: return;
  
}

