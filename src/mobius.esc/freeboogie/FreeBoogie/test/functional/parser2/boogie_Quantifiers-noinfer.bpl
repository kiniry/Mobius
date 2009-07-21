type name;
type ref;
const unique null : ref;
function f($$unnamed~b : int, $$unnamed~a : int) returns ($$unnamed~c : int);
axiom (forall x : int, y : int :: (f(x, y) < (x + y)));
axiom (forall x : int :: {f(x, 10)} (f(x, 10) == 3));
procedure P(a : int, b : int);
  requires ((a <= 25) && (b <= 30));
  

implementation P(a : int, b : int) {
  start: assert (f(a, b) <= 100); return;
  
}

procedure Q(a : int, b : int);
  requires ((a + 2) <= b);
  

implementation Q(a : int, b : int) {
  start: assert (f(a, b) == 3); return;
  
}

procedure R(a : int, b : int);
  requires ((a + 2) <= b);
  

implementation R(a : int, b : int) {
  start: assume ((b <= 10) && (8 <= a)); goto $$start~a;
  $$start~a: assert (f(a, b) == 3); return;
  
}

function g($$unnamed~e : int, $$unnamed~d : int) returns ($$unnamed~f : int);
axiom (forall x : int, y : int :: {g(x, 10), g(x, y)} (g(x, y) == 3));
procedure S(a : int, b : int);
  requires ((a + 2) <= b);
  

implementation S(a : int, b : int) {
  start: assert (g(a, b) == 3); return;
  
}

procedure T(a : int, b : int);
  requires ((a + 2) <= b);
  

implementation T(a : int, b : int) {
  start: assume ((b <= 10) && (8 <= a)); goto $$start~b;
  $$start~b: assert (g(a, b) == 3); return;
  
}

function h($$unnamed~h : int, $$unnamed~g : int) returns ($$unnamed~i : int);
axiom (forall y : int :: {g(y, y)} {h(y, h(y, 10))} (h(y, h(y, y)) == y));
procedure U0(a : int);
implementation U0(a : int) {
  start: assert (h(a, h(a, a)) == a); return;
  
}

procedure U1(a : int, b : int);
implementation U1(a : int, b : int) {
  start: assume (g(a, b) == 5); goto $$start~c;
  $$start~c: assert (h(a, h(a, a)) == a); return;
  
}

procedure V0(a : int, b : int);
  requires (a == b);
  

implementation V0(a : int, b : int) {
  start: assume (g(a, b) == 5); goto $$start~d;
  $$start~d: assert (h(a, h(a, a)) == a); return;
  
}

procedure V1(a : int, b : int);
implementation V1(a : int, b : int) {
  start: assume (a == 10); goto $$start~e;
  $$start~e: assert (h(a, h(a, a)) == a); return;
  
}

procedure V2(a : int, b : int);
implementation V2(a : int, b : int) {
  start: assume (0 <= h(a, h(a, 10))); goto $$start~g;
  $$start~g: assume (a == 17); goto $$start~f;
  $$start~f: assert (h(a, h(a, a)) == a); return;
  
}

function ka($$unnamed~j : ref) returns ($$unnamed~k : int);
function kb($$unnamed~l : ref) returns ($$unnamed~m : int);
function isA($$unnamed~o : ref, $$unnamed~n : name) returns ($$unnamed~p : bool);
function isB($$unnamed~r : ref, $$unnamed~q : name) returns ($$unnamed~s : bool);
const $T : name;
axiom (forall o : ref :: (isA(o, $T) ==> (ka(o) < ka(o))));
axiom (forall o : ref :: {:nopats isB(o, $T)} (isB(o, $T) ==> (kb(o) < kb(o))));
procedure W(o : ref, e : int);
  requires isB(o, $T);
  

implementation W(o : ref, e : int) {
  start: assert (e > 20); return;
  
}

procedure X0(o : ref, e : int);
  requires isA(o, $T);
  

implementation X0(o : ref, e : int) {
  start: assert (e > 20); return;
  
}

procedure X1(o : ref, e : int, u : int);
  requires isB(o, $T);
  

implementation X1(o : ref, e : int, u : int) {
  start: assume (f(kb(o), kb(o)) == u); goto $$start~h;
  $$start~h: assert (e > 20); return;
  
}

