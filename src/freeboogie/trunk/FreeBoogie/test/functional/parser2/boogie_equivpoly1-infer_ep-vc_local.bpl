type name;
type ref;
const unique null : ref;
function $f($$unnamed~a : int) returns ($$unnamed~b : int);
procedure M();
implementation M() {
  var i : int;
  var n : int;
  start: i := 0; goto StartCheck, body;
  StartCheck: assert (i == 0); return;
  body: assume (i <= $f(n)); goto BodyCheck, join;
  BodyCheck: assert ((i <= $f(n)) && (0 <= i)); return;
  join: i := (i + 1); goto JoinCheck, body;
  JoinCheck: assert ((i <= ($f(n) + 1)) && (1 <= i)); return;
  
}

