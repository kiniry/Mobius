type name;
type ref;
const unique null : ref;
procedure Test();
implementation Test() {
  var i : int;
  entry: i := 0; goto block850;
  block850: assert (i == 0); goto $$block850~a;
  $$block850~a: havoc i; goto block850;
  
}

