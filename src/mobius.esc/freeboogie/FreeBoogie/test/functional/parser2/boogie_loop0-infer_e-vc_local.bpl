type name;
type ref;
const unique null : ref;
function $f($$unnamed~a : int) returns ($$unnamed~b : int);
var x : int;
var y : int;
procedure M(this : ref);
implementation M(this : ref) {
  start: assume (x == $f(x)); goto StartCheck, head;
  StartCheck: assert (x == $f(x)); return;
  head: goto HeadCheck, body, id$end;
  HeadCheck: assert (x == $f(x)); return;
  body: goto BodyCheck, head;
  BodyCheck: assert (x == $f(x)); return;
  id$end: assert (x == $f(x)); return;
  
}

