type S;
type Z;
function Zeq_bool(Z, Z) returns (bool);

function S_to_Z(S) returns (Z);
function Z_to_S(Z) returns (S);
axiom (forall x:Z :: S_to_Z(Z_to_S(x)) == x);
function S_to_bool(S) returns (bool);
axiom (forall x:S :: S_to_Z(x) == S_to_Z(x)); // not needed
axiom (forall y:S, x:S :: (x == y) ==> (S_to_bool(x) == S_to_bool(y))); // not needed
axiom (forall x:Z :: Zeq_bool(x, x) == true);
axiom (forall x:Z, y:Z :: x == y ==> Zeq_bool(x, x) == true);
axiom (forall x:Z, y:Z :: x != y ==> Zeq_bool(x, x) == false); // perhaps simplify
axiom (forall b:bool :: !!b == b); // not needed
function select(S, S) returns (S);
function store(S, S, S) returns(S);
function arr_store(S, Z, S) returns (S);

axiom (forall obj:S, val:S, $var:S :: select(store($var, obj, val), obj) == val);
axiom (forall $var:S, val:Z, obj2:S, obj1:S ::
  (obj1 != obj2) ==> select(store_int($var,obj1,val),obj2) == select($var,obj2)); 
function store_int(S, S, Z) returns(S);


