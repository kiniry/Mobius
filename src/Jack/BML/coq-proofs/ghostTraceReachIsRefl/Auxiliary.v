Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Export List.
Open Scope Z_scope.

(**************************)

(* program variables  *)
Definition var := Set.
Parameter var_dec: forall x y : var, {x = y} + {x <> y}.
Definition eqVar : var -> var -> bool :=   (fun x y => if (var_dec x y) then true else false).
(**************************)

(* ghost variables *)
Definition gVar := Set.
Parameter gVar_dec: forall x y : var, {x = y} + {x <> y}.
Definition geqVar : gVar -> gVar -> bool := (fun x y => if (var_dec x y) then true else false).
(**************************)

Definition state := var -> Z. 
Definition ghost := gVar -> Z.

Lemma compSideCond : forall (P Q R:  state -> gVar ->  state -> gVar ->  Prop ),  
(forall s1 s2 s3 g1 g2 g3,  P   s1 g1  s2 g2 ->  Q s2 g2 s3 g3  -> R s1 g1 s3 g3 ) ->

forall s1 s2 s3, (forall g1, exists g2, P   s1 g1  s2 g2 ) ->  (forall g2, exists g3, Q s2 g2 s3 g3 )   -> 
(forall g1, exists g3, R s1 g1 s3 g3). 
Proof. 

intros. 
assert ( H11:= H0 g1).
elim H11.
intros.
assert (H12 := H1 x). 
elim H12.
intros.
exists x0.
apply (  H s1 s2 s3 g1 x x0).
assumption.
assumption.
Qed.                     