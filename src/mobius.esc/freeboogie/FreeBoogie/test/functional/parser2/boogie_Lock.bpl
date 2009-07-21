type name;
type ref;
const unique null : ref;
procedure LockingExample();
implementation LockingExample() {
  var x : int;
  var y : int;
  var held : int;
  start: held := 0; goto $$start~a;
  $$start~a: x := 0; goto LoopHead;
  LoopHead: assert (held == 0); goto $$LoopHead~b;
  $$LoopHead~b: held := 1; goto $$LoopHead~a;
  $$LoopHead~a: y := x; goto UnlockNow, LoopEnd;
  UnlockNow: assert (held == 1); goto $$UnlockNow~b;
  $$UnlockNow~b: held := 0; goto $$UnlockNow~a;
  $$UnlockNow~a: x := (x + 1); goto LoopEnd;
  LoopEnd: goto ContinueIteration, EndIteration;
  ContinueIteration: assume (x != y); goto LoopHead;
  EndIteration: assume (x == y); goto AfterLoop;
  AfterLoop: assert (held == 1); goto $$AfterLoop~a;
  $$AfterLoop~a: held := 0; return;
  
}

