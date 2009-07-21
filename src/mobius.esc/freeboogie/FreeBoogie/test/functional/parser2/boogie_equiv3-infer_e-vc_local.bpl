type name;
type ref;
const unique null : ref;
function $f($$unnamed~a : int) returns ($$unnamed~b : int);
var x : int;
var y : int;
procedure M(this : ref);
implementation M(this : ref) {
  start: goto id$then, id$else;
  id$then: assume (x == $f(x)); goto ThenCheck, join;
  ThenCheck: assert (x == $f(x)); return;
  id$else: assume (x == $f($f(x))); goto ElseCheck, join;
  ElseCheck: assert (x == $f($f(x))); return;
  join: goto JoinCheck, Return;
  JoinCheck: assert (x == $f($f(x))); return;
  Return: return;
  
}

