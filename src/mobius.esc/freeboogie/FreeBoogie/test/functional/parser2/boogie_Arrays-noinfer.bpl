type name;
type ref;
const unique null : ref;
var A : [ref]int;
procedure P0(o : ref, q : ref, y : int);
  requires (o != q);
  modifies A;
  ensures (A[o] == (old(A[o]) + y));
  ensures (forall p : ref :: ((A[p] == old(A[p])) || (p == o)));
  

implementation P0(o : ref, q : ref, y : int) {
  var k : int;
  start: k := A[q]; goto $$start~b;
  $$start~b: A := A[o := (y + A[o])]; goto $$start~a;
  $$start~a: A := A[q := k]; return;
  
}

procedure P1(o : ref, q : ref, y : int);
  modifies A;
  ensures (forall p : ref :: ((A[p] == old(A[p])) || (p == o)));
  

implementation P1(o : ref, q : ref, y : int) {
  var k : int;
  start: k := A[q]; goto $$start~d;
  $$start~d: A := A[o := (y + A[o])]; goto $$start~c;
  $$start~c: A := A[q := k]; return;
  
}

procedure P2(o : ref, q : ref, y : int);
  modifies A;
  ensures (A[o] == (old(A[o]) + y));
  

implementation P2(o : ref, q : ref, y : int) {
  var k : int;
  start: k := A[q]; goto $$start~f;
  $$start~f: A := A[o := (y + A[o])]; goto $$start~e;
  $$start~e: A := A[q := k]; return;
  
}

var B : [ref, name]int;
const F : name;
procedure Q0(o : ref, q : ref, y : int, G : name);
  requires ((o != q) && (F != G));
  modifies B;
  ensures (B[o, F] == (old(B[o, F]) + y));
  ensures (forall p : ref, f : name :: ((B[p, f] == old(B[p, f])) || ((p == o) && (f == F))));
  

implementation Q0(o : ref, q : ref, y : int, G : name) {
  var k : int;
  start: k := B[q, G]; goto $$start~h;
  $$start~h: B := B[o, F := (y + B[o, F])]; goto $$start~g;
  $$start~g: B := B[q, G := k]; return;
  
}

procedure Q1(o : ref, q : ref, y : int, G : name);
  modifies B;
  ensures (forall p : ref, f : name :: ((B[p, f] == old(B[p, f])) || ((p == o) && (f == F))));
  

implementation Q1(o : ref, q : ref, y : int, G : name) {
  var k : int;
  start: k := B[q, G]; goto $$start~j;
  $$start~j: B := B[o, F := (y + B[o, F])]; goto $$start~i;
  $$start~i: B := B[q, G := k]; return;
  
}

procedure Q2(o : ref, q : ref, y : int, G : name);
  requires (F != G);
  modifies B;
  ensures (B[o, F] == (old(B[o, F]) + y));
  

implementation Q2(o : ref, q : ref, y : int, G : name) {
  var k : int;
  start: k := B[q, G]; goto $$start~l;
  $$start~l: B := B[o, F := (y + B[o, F])]; goto $$start~k;
  $$start~k: B := B[q, G := k]; return;
  
}

procedure Q3(o : ref, q : ref, y : int, G : name);
  requires (o != q);
  modifies B;
  ensures (B[o, F] == (old(B[o, F]) + y));
  

implementation Q3(o : ref, q : ref, y : int, G : name) {
  var k : int;
  start: k := B[q, G]; goto $$start~n;
  $$start~n: B := B[o, F := (y + B[o, F])]; goto $$start~m;
  $$start~m: B := B[q, G := k]; return;
  
}

procedure Q4(o : ref, q : ref, y : int, G : name);
  modifies B;
  ensures (B[o, F] == (old(B[o, F]) + y));
  

implementation Q4(o : ref, q : ref, y : int, G : name) {
  var k : int;
  start: k := B[q, G]; goto $$start~p;
  $$start~p: B := B[o, F := (y + B[o, F])]; goto $$start~o;
  $$start~o: B := B[q, G := k]; return;
  
}

procedure Skip0(o : ref, q : ref, G : name, H : name);
  modifies B, A;
  ensures (forall p : ref :: (A[p] == old(A[p])));
  ensures (forall p : ref, g : name :: (B[p, g] == old(B[p, g])));
  

implementation Skip0(o : ref, q : ref, G : name, H : name) {
  start: return;
  
}

procedure Skip1(o : ref, q : ref, G : name, H : name);
  modifies B, A;
  ensures (forall p : ref :: (A[p] == old(A[p])));
  ensures (forall p : ref, g : name :: (B[p, g] == old(B[p, g])));
  

implementation Skip1(o : ref, q : ref, G : name, H : name) {
  var k : int;
  var l : int;
  start: k := A[o]; goto $$start~q;
  $$start~q: l := A[q]; goto oneWay, theOtherWay;
  oneWay: A := A[o := k]; goto $$oneWay~a;
  $$oneWay~a: A := A[q := l]; goto next;
  theOtherWay: A := A[q := l]; goto $$theOtherWay~a;
  $$theOtherWay~a: A := A[o := k]; goto next;
  next: k := B[o, G]; goto $$next~a;
  $$next~a: l := B[q, H]; goto Lx, Ly;
  Lx: B := B[o, G := k]; goto $$Lx~a;
  $$Lx~a: B := B[q, H := l]; return;
  Ly: B := B[q, H := l]; goto $$Ly~a;
  $$Ly~a: B := B[o, G := k]; return;
  
}

