Axiom S_to_bool_det: 
         forall x y: S,  x = y -> (S_to_bool x) = (S_to_bool y).

Axiom Z_to_S_elim : forall x,  S_to_Z (Z_to_S x) = x.
Require Import Bool.
Require Import ZArith.
Require Import Zdiv.
Require Import Zbool.
Require Import Classical.
Open Scope Z_scope.


Variable S: Set.




(* Some arithmetic things *)
Variable S_to_Z : S -> Z.
Variable Z_to_S : Z -> S.
Axiom Z_to_S_elim : forall x,  S_to_Z (Z_to_S x) = x.
Variable S_to_bool : S -> bool.
Axiom S_to_Z_det: 
         forall x : S,   (S_to_Z x) = (S_to_Z x).
Axiom S_to_bool_det: 
         forall x y: S,  x = y -> (S_to_bool x) = (S_to_bool y).

Hint Immediate S_to_Z_det S_to_bool_det.
Hint Rewrite Z_to_S_elim:escj.

Lemma Zeq_bool_sym : forall (x:Z), Zeq_bool x x = true.


Lemma Zeq_bool_true:
forall x y: Z, x = y ->Zeq_bool x y = true.

Lemma Zeq_bool_false:
forall x y: Z, x <> y ->Zeq_bool x y = false.

Lemma negb_elim :
    forall b, negb (negb b) = b.



Hint Rewrite negb_elim :escj.
Hint Resolve Zeq_bool_sym Zeq_bool_true Zeq_bool_false.


Definition integralGE : Z -> Z -> Prop := fun (x y : Z) => x >= y.
Definition integralGT : Z -> Z -> Prop := fun (x y : Z) =>  x > y.
Definition integralLE : Z-> Z -> Prop := fun (x y : Z) => x <= y.
Definition integralLT : Z -> Z -> Prop := fun (x y : Z) => x < y.

Definition integralEQ_bool : Z -> Z -> bool := fun (x y : Z) => Zeq_bool x  y.
Definition integralGE_bool : Z -> Z -> bool := fun (x y : Z) => Zge_bool x y.
Definition integralGT_bool : Z -> Z -> bool := fun (x y : Z) => Zgt_bool x y.
Definition integralLE_bool : Z -> Z -> bool := fun (x y : Z) =>  Zle_bool x y.
Definition integralLT_bool : Z -> Z -> bool := fun (x y : Z) => Zlt_bool x y.

Definition integralDiv : Z -> Z -> Z := 
             fun (x y : Z) =>(x  / y).
Definition integralAdd : Z -> Z -> Z := 
             fun (x y : Z) =>(x  + y).
Definition integralSub : Z -> Z -> Z := 
             fun (x y : Z) =>(x - y).
Definition integralMul : Z -> Z -> Z := 
             fun (x y : Z) =>(x  * y).
Definition integralNeg : Z -> Z := 
             fun (x : Z) =>(0 - x).


Variable select: S -> S -> S.
Variable store : S -> S -> S -> S.
Variable arr_store: S -> Z -> S -> S.

Axiom select_store1: 
    forall(var val obj :S), (select (store var obj val) obj) = val.
Axiom select_store2: 
    forall(var val obj1 obj2 :S), 
         obj1 <> obj2 -> 
                 (select (store var obj1 val) obj2) = (select var obj2).

Variable store_int: S -> S -> Z -> S.
Variable arr_store_int: S -> Z -> Z -> S.
Axiom select_store_int1: 
    forall(var : S) (val: Z) (obj :S), S_to_Z (select (store_int var obj val) obj) = val.
Axiom select_store_int2: 
    forall(var : S) (val: Z)( obj1 obj2 :S), 
         obj1 <> obj2 -> 
                 (select (store_int var obj1 val) obj2) = (select var obj2).

Variable store_bool: S -> S -> bool -> S.
Variable arr_store_bool: S -> Z -> bool -> S.
Axiom arr_select_store_bool : 
 forall (var: S) (val: bool) (i : Z) (j: S),
      i = (S_to_Z j) -> S_to_bool (select (arr_store_bool var i val) j) = val.
Axiom select_store_bool1: 
    forall(var : S) (val: bool) (obj :S), S_to_bool (select (store_bool var obj val) obj) = val.
Axiom select_store_bool2: 
    forall(var : S) (val: bool)( obj1 obj2 :S), 
         obj1 <> obj2 -> 
                 S_to_bool (select (store_bool var obj1 val) obj2) = S_to_bool (select var obj2).
Hint Resolve select_store2 select_store_int2 select_store_bool2.
Hint Rewrite  -> select_store1 select_store_int1 select_store_bool1: escj_select.

Variable null : S.
Variable isAllocated: S -> S -> Prop.
Variable fClosedTime : S -> S.

(* The following are grabbed from Jack's Coq Plugin *)
Variable refEQ : S -> S-> bool.
Variable refEQ_refl : forall x, refEQ x x = true. 
Variable refEQ_eq : forall x y, refEQ x y = true -> x = y. 
Lemma refEQ_eq_true : forall x y, x = y-> refEQ x y = true.
 
Lemma refEQ_eq_not_false : forall x y, x=y-> refEQ x y <> false.

Lemma refEQ_false_not_eq :  forall x y, refEQ x y = false -> x <> y.

Definition exists_refEQ_eq : forall x y, {b:bool  | refEQ x y = b}.

Lemma not_eq_false_refEQ : forall x y, x <> y -> refEQ x y = false.

(* End of the stolen part *)




Hint Rewrite refEQ_refl : escj.
 
Variable Types : Set.
Variable subtypes: Types -> Types-> Prop.
Variable typeof : S -> Types.
Variable lockLT : S -> S -> Prop.
(*Variable is : S -> S -> Prop. *)
Variable isField : S -> Prop.
Variable allocNew_ : S.


Variable asField: S -> Types -> Prop.
Variable asElems: S -> Prop.
Variable asLockSet: S -> Prop.

Variable eClosedTime: S ->S.

(* Array Logic *)
Variable arrayFresh : S -> S -> S -> S -> S -> Types -> S -> Prop.
Variable arrayShapeOne: S -> S.
Variable arrayShapeMore: S -> S-> S.
Variable isNewArray: S -> Prop.
Variable arrayLength: S -> S.
Axiom arrayLengthAx :
      forall (a : S), (integralLE 0 (S_to_Z (arrayLength a))).

(* array axioms2 *)
(* Axiom array_axiom2_1 : 
      forall (a, a0, b0, e, n : S) (T: Types) (v : S):
        arrayFresh(a, a0, b0, e, arrayShapeOne(n), T, v) ->
        (a0 <= (vAllocTime a)). *)
Axiom array_axiom2_2 : 
      forall (a  a0  b0  e  n: S)  (T: Types)  (v : S),
        (arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (isAllocated a  b0).
Axiom array_axiom2_3 : 
     forall (a  a0  b0  e  n: S)  (T: Types)  (v : S),
        (arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (a <> null). 
Axiom array_axiom2_4 : 
     forall (a  a0  b0  e  n: S)  (T: Types)  (v : S),
        (arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (typeof a) = T.
Axiom array_axiom2_5 : 
     forall (a  a0  b0  e  n: S)  (T: Types)  (v : S),
        (arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         (arrayLength a) = n.
Axiom array_axiom2_6 : 
     forall (a  a0  b0  e  n: S)  (T: Types)  (v : S),
        (arrayFresh a  a0  b0 e (arrayShapeOne n) T v) ->
         forall (i : S),
           (select (select e a) i) = v.

(* maybe another day... Hint Resolve array_axiom2_2 array_axiom2_3 array_axiom2_4 array_axiom2_5 array_axiom2_6. *)




Variable ecReturn : S.
Variable ecThrow : S.
Axiom distinctAxiom : ecReturn <> ecThrow.
Hint Immediate distinctAxiom.




(* Sans elimOr/elimAnd c'est un peu la deche *)
(**
 ** elimAnd
 elimAnd is used mainly to eliminate and within the hypothesis.
For the goals the preferred tactic is still split. *)


Inductive Plist : Prop :=
  | Pnil : Plist
  | Pcons : Prop -> Plist -> Plist.


Inductive PPlProd : Prop :=
 | PPlPair : Plist -> Prop -> PPlProd.









Definition distr_or : forall A B, ~ (A \/ B) ->  ~ A.


Definition distr_or_inv : forall A B, ~ (A \/ B) ->  ~B.







Definition int := Z.
Definition Field := S.

Definition Path := S.
Definition RefType := Types.
Definition time := S.
Coercion S_to_Z : S >-> Z.
Coercion Z_to_S : Z >-> S.
