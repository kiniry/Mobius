type name;
type ref;
const unique null : ref;
const TEST : name;
procedure P();
implementation P() {
  var i : int;
  var N : int;
  start: assume (N >= 0); goto $$start~b;
  $$start~b: i := 0; goto $$start~a;
  $$start~a: assert (i <= N); goto LoopHead;
  LoopHead: goto LoopBody, AfterLoop;
  LoopBody: assume (i < N); goto $$LoopBody~a;
  $$LoopBody~a: i := (i + 1); goto LoopHead;
  AfterLoop: assume !(i < N); goto $$AfterLoop~a;
  $$AfterLoop~a: assert (i == N); return;
  
}

