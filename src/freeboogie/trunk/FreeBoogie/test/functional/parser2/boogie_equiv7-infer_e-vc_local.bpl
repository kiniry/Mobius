type name;
type ref;
const unique null : ref;
function $f($$unnamed~a : int) returns ($$unnamed~b : int);
var x : int;
var y : int;
var z : int;
procedure M(this : ref);
  modifies z;
  

implementation M(this : ref) {
  start: z := $f(x); goto $$start~d;
  $$start~d: z := $f(y); goto $$start~c;
  $$start~c: z := 3; goto $$start~b;
  $$start~b: assume (x == y); goto $$start~a;
  $$start~a: assume (z == $f(x)); goto StartCheck, Return;
  StartCheck: assert (((y == x) && (z == 3)) && (z == $f(y))); return;
  Return: return;
  
}

