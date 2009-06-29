type name;
type ref;
const unique null : ref;
procedure P();
implementation P() {
  var a : int;
  var b : int;
  var t : bool;
  start: assume (a == b); goto $$start~b;
  $$start~b: t := (a == b); goto $$start~a;
  $$start~a: assert t; return;
  
}

function f($$unnamed~a : bool) returns ($$unnamed~b : int);
const A : int;
const B : int;
axiom (f((A < B)) == 5);
procedure Q();
implementation Q() {
  start: assume (A < B); goto $$start~c;
  $$start~c: assert (f(true) == 5); return;
  
}

procedure PX();
implementation PX() {
  var a : int;
  var b : int;
  var t : bool;
  start: assume (a == b); goto $$start~e;
  $$start~e: t := (a == b); goto $$start~d;
  $$start~d: assert !t; return;
  
}

procedure QX();
implementation QX() {
  start: assume (A < B); goto $$start~f;
  $$start~f: assert (f(true) < 2); return;
  
}

