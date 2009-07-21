type name;
type ref;
const unique null : ref;
procedure Bar() returns (barresult : ref);
procedure Foo();
implementation Foo() {
  var x : ref;
  entry: call x := Bar(); goto $$entry~c;
  $$entry~c: assume (x == null); goto $$entry~b;
  $$entry~b: call x := Bar(); goto $$entry~a;
  $$entry~a: assert (x == null); return;
  
}

procedure DifferentFormalNames(x : int, y : int) returns (z : int);
  requires (x < y);
  ensures (z == x);
  

implementation DifferentFormalNames(x : int, y : int) returns (z : int) {
  start: assert (x < y); goto $$start~a;
  $$start~a: z := x; return;
  
}

implementation DifferentFormalNames(y : int, x : int) returns (w : int) {
  start: goto A, B;
  A: assert (y < x); goto $$A~a;
  $$A~a: assume false; return;
  B: w := y; return;
  
}

implementation DifferentFormalNames(y : int, x : int) returns (w : int) {
  start: assert (x < y); goto $$start~b;
  $$start~b: w := y; return;
  
}

implementation DifferentFormalNames(y : int, x : int) returns (w : int) {
  start: w := x; return;
  
}

