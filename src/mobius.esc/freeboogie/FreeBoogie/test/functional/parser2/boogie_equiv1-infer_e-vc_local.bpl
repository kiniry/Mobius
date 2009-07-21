type name;
type ref;
const unique null : ref;
var x : int;
var y : int;
var z : int;
procedure M(this : ref);
  modifies z, y;
  

implementation M(this : ref) {
  start: y := (x + 3); goto $$start~a;
  $$start~a: z := (x + 3); goto CheckStart, Return;
  CheckStart: assert ((y == (x + 3)) && (z == y)); return;
  Return: return;
  
}

