type name;
type ref;
const unique null : ref;
var x : int;
var y : int;
var z : int;
procedure M(this : ref);
  modifies z, y, x;
  

implementation M(this : ref) {
  start: x := 3; goto $$start~b;
  $$start~b: y := x; goto $$start~a;
  $$start~a: z := x; goto CheckStart, Return;
  CheckStart: assert (((x == 3) && (y == 3)) && (z == 3)); return;
  Return: return;
  
}

