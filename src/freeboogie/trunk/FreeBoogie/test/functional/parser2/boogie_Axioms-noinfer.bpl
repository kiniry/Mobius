type name;
type ref;
const unique null : ref;
const Seven : int;
axiom (Seven == 7);
function inc($$unnamed~a : int) returns ($$unnamed~b : int);
axiom (forall j : int :: (inc(j) == (j + 1)));
procedure P();
implementation P() {
  start: assert (4 <= Seven); goto $$start~b;
  $$start~b: assert (Seven < inc(Seven)); goto $$start~a;
  $$start~a: assert ((inc(5) + inc(inc(2))) == (Seven + 3)); return;
  
}

procedure Q();
implementation Q() {
  start: assert ((inc(5) + inc(inc(2))) == Seven); return;
  
}

