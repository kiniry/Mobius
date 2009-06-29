type name;
type ref;
const unique null : ref;
procedure main();
implementation main() {
  var x : int;
  var y : int;
  var z : int;
  start: x := 2; goto $$start~a;
  $$start~a: y := 6; goto LoopHead;
  LoopHead: assert (y < 10); goto LoopBody, LoopEnd;
  LoopBody: havoc y; goto LoopHead;
  LoopEnd: return;
  
}

procedure SimpleWhile5() returns (returnValue : int);
implementation SimpleWhile5() returns (returnValue : int) {
  var i : int;
  start: returnValue := 1; goto $$start~b;
  $$start~b: havoc i; goto LoopHead;
  LoopHead: goto LoopBody, LoopEnd;
  LoopBody: i := 1; goto IncLoopHead;
  IncLoopHead: goto IncI, IncDone;
  IncI: i := (i + 1); goto IncLoopHead;
  IncDone: assert (1 <= i); goto $$IncDone~b;
  $$IncDone~b: returnValue := (returnValue * i); goto $$IncDone~a;
  $$IncDone~a: i := (i - 1); goto LoopHead;
  LoopEnd: assert (returnValue >= 1); return;
  
}

