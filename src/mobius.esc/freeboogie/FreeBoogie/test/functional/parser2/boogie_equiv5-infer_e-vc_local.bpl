type name;
type ref;
const unique null : ref;
function $f($$unnamed~a : int) returns ($$unnamed~b : int);
var x : int;
var y : int;
procedure M(this : ref);
  modifies x;
  

implementation M(this : ref) {
  start: x := 3; goto StartCheck, id$then, id$else;
  StartCheck: assert (x == 3); return;
  id$then: x := $f(x); goto $$then~a;
  $$then~a: assume (x == 3); goto ThenCheck, join;
  ThenCheck: assert ((x == 3) && (x == $f(3))); return;
  id$else: x := $f($f(x)); goto $$else~a;
  $$else~a: assume (x == 3); goto join, ElseCheck;
  ElseCheck: assert ((x == 3) && (x == $f($f(3)))); return;
  join: assert ((x == 3) && (x == $f($f(x)))); return;
  
}

procedure MPrime(this : ref);
  modifies x;
  

implementation MPrime(this : ref) {
  start: x := 3; goto StartCheck, id$then, id$else;
  StartCheck: assert (x == 3); return;
  id$then: x := $f(x); goto $$then~b;
  $$then~b: assume (x == 3); goto ThenCheck, join;
  ThenCheck: assert ((x == 3) && (x == $f(3))); return;
  id$else: x := $f($f(x)); goto $$else~b;
  $$else~b: assume (x == 3); goto join, ElseCheck;
  ElseCheck: assert ((x == 3) && (x == $f($f(3)))); return;
  join: assert (x == $f(x)); return;
  
}

