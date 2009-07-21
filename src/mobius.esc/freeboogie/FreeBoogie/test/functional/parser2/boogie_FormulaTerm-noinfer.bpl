type name;
type ref;
const unique null : ref;
procedure plus(x : int, y : int) returns (z : int);
  ensures (z == (x + y));
  

implementation plus(x : int, y : int) returns (z : int) {
  start: assume (z == 3); return;
  
}

implementation plus(x : int, y : int) returns (z : int) {
  start: z := (x + y); return;
  
}

implementation plus(x : int, y : int) returns (z : int) {
  start: z := (x + y); goto $$start~a;
  $$start~a: z := (0 + z); return;
  
}

procedure plus2(x : int, y : int) returns (z : int);
  ensures (z == (x + y));
  

implementation plus2(x : int, y : int) returns (z : int) {
  start: z := (x + y); return;
  
}

procedure or(x : int, y : int, a : int, b : int) returns (z : int);
  requires (a == b);
  

implementation or(x : int, y : int, a : int, b : int) returns (z : int) {
  var t : bool;
  start: t := ((((((x < y) || (x > y)) || (x == y)) || (x != y)) && (a >= b)) && (a <= b)); goto $$start~c;
  $$start~c: assert ((((((x < y) || (x > y)) || (x == y)) || (x != y)) && (a >= b)) && (a <= b)); goto $$start~b;
  $$start~b: assert t; return;
  
}

procedure less(x : int, y : int) returns (z : bool);
  requires (x < y);
  ensures (z == (x < y));
  

implementation less(x : int, y : int) returns (z : bool) {
  start: z := (x < y); return;
  
}

implementation less(x : int, y : int) returns (z : bool) {
  start: goto yes, no;
  yes: assume (x < y); goto $$yes~a;
  $$yes~a: z := true; return;
  no: assume !(x < y); goto $$no~a;
  $$no~a: z := false; return;
  
}

implementation less(x : int, y : int) returns (z : bool) {
  start: goto yes, no;
  yes: assume (x < y); goto $$yes~b;
  $$yes~b: z := true; return;
  no: assume (x >= y); goto $$no~b;
  $$no~b: z := false; return;
  
}

procedure LESS(x : int, y : int) returns (z : bool);
  requires (x < y);
  ensures (z <==> (x < y));
  

implementation LESS(x : int, y : int) returns (z : bool) {
  start: z := (x < y); return;
  
}

implementation LESS(x : int, y : int) returns (z : bool) {
  start: goto yes, no;
  yes: assume (x < y); goto $$yes~c;
  $$yes~c: z := true; return;
  no: assume !(x < y); goto $$no~c;
  $$no~c: z := false; return;
  
}

implementation LESS(x : int, y : int) returns (z : bool) {
  start: goto yes, no;
  yes: assume (x < y); goto $$yes~d;
  $$yes~d: z := true; return;
  no: assume (x >= y); goto $$no~d;
  $$no~d: z := false; return;
  
}

