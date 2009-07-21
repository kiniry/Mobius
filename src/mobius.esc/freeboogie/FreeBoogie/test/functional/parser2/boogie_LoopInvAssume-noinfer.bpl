type name;
type ref;
const unique null : ref;
var x : int;
procedure Test();
  modifies x;
  

implementation Test() {
  entry: goto loophead, exit;
  loophead: assume (x >= 0); goto $$loophead~a;
  $$loophead~a: x := 0; goto loophead, exit;
  exit: assume (x < 0); goto $$exit~a;
  $$exit~a: assert false; return;
  
}

