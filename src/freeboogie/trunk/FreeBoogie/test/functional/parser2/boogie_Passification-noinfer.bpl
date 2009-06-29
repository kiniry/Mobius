type name;
type ref;
const unique null : ref;
procedure good0(x : int) returns (y : int, z : int);
  ensures ((z == 4) || (z == (4 + x)));
  

implementation good0(x : int) returns (y : int, z : int) {
  var t : int;
  A: t := y; goto $$A~a;
  $$A~a: z := 3; goto B, C;
  B: z := (z + x); goto D;
  C: goto D;
  D: z := (z + 1); goto $$D~a;
  $$D~a: y := t; return;
  
}

procedure good1(x : int) returns (y : int, z : int);
  ensures (z == (x + 4));
  

implementation good1(x : int) returns (y : int, z : int) {
  var t : int;
  A: t := y; goto $$A~e;
  $$A~e: z := 3; goto $$A~d;
  $$A~d: z := (z + x); goto $$A~c;
  $$A~c: z := (z + 1); goto $$A~b;
  $$A~b: y := t; return;
  
}

procedure bad0(x : int) returns (y : int, z : int);
  ensures (y == 4);
  

implementation bad0(x : int) returns (y : int, z : int) {
  var t : int;
  A: t := z; goto $$A~h;
  $$A~h: z := 3; goto $$A~g;
  $$A~g: z := (z + 1); goto $$A~f;
  $$A~f: y := t; return;
  
}

procedure Loop();
implementation Loop() {
  start: goto start;
  
}

procedure UnreachableBlock();
implementation UnreachableBlock() {
  start: return;
  notReached: goto start;
  reallyNeverReached: goto reallyNeverReached;
  
}

procedure Loop0() returns (z : int);
  ensures (10 <= z);
  

implementation Loop0() returns (z : int) {
  var x : int;
  A: goto B, C;
  B: assume (x < 10); goto $$B~a;
  $$B~a: x := (x + 1); goto A;
  C: assume !(x < 10); goto $$C~a;
  $$C~a: z := x; return;
  
}

const A0 : name;
const A1 : name;
const A2 : name;
procedure Array0() returns (z : int);
  ensures (z >= 5);
  

implementation Array0() returns (z : int) {
  var a : [name, name]int;
  L0: a := a[A0, A2 := 5]; goto $$L0~b;
  $$L0~b: a := a[A0, A1 := 20]; goto $$L0~a;
  $$L0~a: assert (a[A0, A1] == 20); goto L1, L2;
  L1: a := a[A0, A2 := 18]; goto $$L1~a;
  $$L1~a: assert (a[A0, A2] == 18); goto L2;
  L2: assert (a[A0, A1] == 20); goto $$L2~a;
  $$L2~a: z := a[A0, A2]; return;
  
}

procedure Array1(o0 : ref, o1 : ref) returns (z : int);
  ensures (z >= 5);
  

implementation Array1(o0 : ref, o1 : ref) returns (z : int) {
  var a : [ref, name]int;
  L0: a := a[o1, A0 := 5]; goto $$L0~d;
  $$L0~d: a := a[o0, A0 := 20]; goto $$L0~c;
  $$L0~c: assert (a[o0, A0] == 20); goto L1, L2;
  L1: a := a[o1, A0 := 18]; goto $$L1~b;
  $$L1~b: assert (a[o1, A0] == 18); goto L2;
  L2: assert (a[o0, A0] == 20); goto $$L2~b;
  $$L2~b: z := a[o1, A0]; return;
  
}

procedure Array2(o0 : ref, o1 : ref) returns (z : int);
  ensures (z >= 5);
  

implementation Array2(o0 : ref, o1 : ref) returns (z : int) {
  var a : [ref, name]int;
  L0: assume (o1 != o0); goto $$L0~g;
  $$L0~g: a := a[o1, A0 := 5]; goto $$L0~f;
  $$L0~f: a := a[o0, A0 := 20]; goto $$L0~e;
  $$L0~e: assert (a[o0, A0] == 20); goto L1, L2;
  L1: a := a[o1, A0 := 18]; goto $$L1~c;
  $$L1~c: assert (a[o1, A0] == 18); goto L2;
  L2: assert (a[o0, A0] == 20); goto $$L2~c;
  $$L2~c: z := a[o1, A0]; return;
  
}

procedure P();
implementation P() {
  var t : int;
  L0: t := 0; goto L1, L2;
  L1: t := 1; goto L2;
  L2: assert (t == 1); return;
  
}

procedure Q();
implementation Q() {
  var t : int;
  L0: t := 0; goto L1, L2;
  L1: t := 1; goto L2;
  L2: assert (t == 0); return;
  
}

