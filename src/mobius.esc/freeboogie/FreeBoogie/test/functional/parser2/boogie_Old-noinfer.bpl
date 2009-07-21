type name;
type ref;
const unique null : ref;
var x : int;
var y : int;
procedure P();
  modifies x;
  ensures (x == (old(x) + 1));
  

implementation P() {
  start: x := (1 + x); return;
  
}

procedure Q();
  modifies x;
  ensures (x == (old(x) + 1));
  

implementation Q() {
  start: x := (1 + x); return;
  
}

procedure R();
  modifies x;
  ensures (x == (old(x) + 1));
  

implementation R() {
  start: return;
  
}

procedure Swap();
  modifies y, x;
  ensures ((x == old(y)) && (y == old(x)));
  

implementation Swap() {
  var t : int;
  start: goto A, B;
  A: t := x; goto $$A~b;
  $$A~b: x := y; goto $$A~a;
  $$A~a: y := t; goto id$end;
  B: x := (x - y); goto $$B~b;
  $$B~b: y := (y + x); goto $$B~a;
  $$B~a: x := (y - x); goto id$end;
  id$end: return;
  
}

procedure OutParam0(x : int) returns (y : int);
  ensures (y == (x + 1));
  

implementation OutParam0(x : int) returns (y : int) {
  start: y := (x + 1); return;
  
}

procedure OutParam1(x : int) returns (y : int);
  ensures (y == (x + 1));
  

implementation OutParam1(x : int) returns (y : int) {
  start: y := (x + 1); return;
  
}

var a : [ref]int;
var b : [ref]int;
procedure SwapElems(o : ref) returns (p : ref);
  modifies b, a;
  ensures ((a[o] == old(b[p])) && (b[o] == old(a[p])));
  

implementation SwapElems(o : ref) returns (p : ref) {
  var ta : int;
  var tb : int;
  start: goto A, B, C;
  A: havoc p; goto B, C;
  B: ta := a[p]; goto $$B~e;
  $$B~e: tb := b[p]; goto $$B~d;
  $$B~d: a := a[o := tb]; goto $$B~c;
  $$B~c: b := b[o := ta]; return;
  C: assume (a[o] == b[o]); goto $$C~b;
  $$C~b: assume false; goto $$C~a;
  $$C~a: p := o; return;
  
}

var Global0 : int;
procedure OldInCode0();
  requires (Global0 >= 0);
  ensures (Global0 <= (old(Global0) + 1));
  modifies Global0;
  

implementation OldInCode0() {
  var local0 : int;
  start: goto A, B;
  A: assert (Global0 == old(Global0)); return;
  B: local0 := (Global0 + 1); goto $$B~g;
  $$B~g: local0 := (local0 - 1); goto $$B~f;
  $$B~f: Global0 := old((local0 + 1)); return;
  
}

