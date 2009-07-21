type name;
type ref;
const unique null : ref;
procedure Test1();
implementation Test1() {
  entry: assert (!true == false); return;
  
}

procedure Test2();
implementation Test2() {
  var b : bool;
  entry: assume (b != false); goto $$entry~a;
  $$entry~a: assert b; return;
  
}

