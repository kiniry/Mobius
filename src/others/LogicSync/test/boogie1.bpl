/*
 negb <-> !
 integralLE <--> <
 Zeq_bool -> ==
 = --> ==
 \/ -> ||   (*)
 bor -> ||

 forall <-> forall

 (S_to_Z x) <-> cast(x, Z)
 (Z_to_S x) <-> cast(x, S)
 (S_to_bool x) <-> cast(x, bool)

 Z <-> int
 Prop -> bool
 bool -> bool

 ignore:
    Z_to_S_elim   
    T
 */

type S;

function select(S, S) returns (S); 
  // ask TypeChecker.checkType(); make it public if it isn't
function store(S, S, S) returns (S); 
function select(S, Z, S) returns (S); 

axiom arrayLenghtAx :
  (forall a : S :: 0 < cast(arrayLength(a),Z));
axiom N F;

