type name;
type ref;
const unique null : ref;
function $f($$unnamed~a : int) returns ($$unnamed~b : int);
var x : int;
var y : int;
procedure M(this : ref);
  modifies y, x;
  

implementation M(this : ref) {
  start: x := 3; goto StartCheck, id$then, id$else;
  StartCheck: assert (x == 3); return;
  id$then: y := 3; goto ThenCheck, join;
  ThenCheck: assert ((x == 3) && (y == 3)); return;
  id$else: y := x; goto ElseCheck, join;
  ElseCheck: assert ((x == 3) && (y == 3)); return;
  join: assert ((x == 3) && (y == 3)); return;
  
}

