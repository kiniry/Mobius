Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef.
Require Import Logic_n.
Require Import Language.
Require Import Semantic.
Require Import Wp_propag.
Require Import Classical.
Require Import Wp.

Ltac caseEq t := 
 generalize (refl_equal t); pattern t at -1; case t.



Fixpoint is_in (x:var) (l:list var) {struct l} : bool :=
 match l with 
 | nil => false
 | cons y l => if eq_var x y then true else is_in x l
 end.

 

Axiom Zeq_bool_diff : forall x y, x <> y -> Zeq_bool x y = false.
Axiom Zeq_bool_refl : forall x, Zeq_bool x x = true.
Axiom Zeq_bool_implies_eq : forall v1 v2, Zeq_bool v1 v2 = true -> v1 = v2. 
Axiom Zneq_bool_implies_neq : forall v1 v2 , Zeq_bool v1 v2 = false -> v1 <> v2.
Axiom is_In_false : forall x l, is_in x l = false -> ~In x l. 
Axiom not_In_is_in_false : forall x l, ~In x l -> is_in x l = false. 



 
  
                           
Axiom conjAssoc: forall  ( P1 P2 P3 : assertion ),
 ( fun s => ( (P1  s /\ P2 s  ) /\ P3 s  ) ) =
 ( fun s => ( P1  s /\ ( P2 s   /\ P3 s )) ) .


Axiom conjPerm :  forall lVar (e : expr ) inv pre , 
  forall s ,  (exists  st,  eval_expr s e <> 0 /\ inv s /\ 
                    ( forall x0: var, ~ In x0 lVar -> s x0 = st x0 ) /\ pre st   )   ->
                  (exists  st,  pre st  /\ eval_expr s e <> 0 /\ inv s /\ 
                    ( forall x0: var, ~ In x0 lVar -> s x0 = st x0 )   ).





Axiom extentional : forall (A B:Set) (f g : A->B), (forall x, f x = g x) -> f = g.

Axiom extentionalType: forall (A B:Type ) (f g : A->B), (forall x, f x = g x) -> f = g.
 
Axiom etaExp: forall (A B : Type ) (f : A -> B ),
forall state,  (fun  s : A => f s) state  = f state . 

Axiom etaExpansion : forall (A B : Type ) (f : A -> B ) ,
  ( fun s => f s ) = f. 


(*
(*exists x ( A x /\ B) < = > exists x (A x) /\ B *)
Axiom  freeEx : forall P1 P2 : assertion , 
forall s ,   ( exists x,  P1 s /\ P2 x) = ( P1 s /\ ( exists x,  P2 x )) .  

(*exists x ( A x /\ B) < = > exists x (A x) /\ B *)
Lemma  freeEx1 : forall P1 P2 : assertion , 
forall s ,   ( exists x,  P1 s /\ P2 x)  -> ( P1 s /\ ( exists x,  P2 x )) .  
Proof.
  intros P1  P2 s H.
  destruct H as [  x H ] . 
  destruct H as [ H1  H2].
  split.
  assumption.
  exists x; auto.
Qed.
*)

Axiom not_not_eq_impl_eq : forall  (A : Set)( v1 v2 : A) ,
  ~ v1 <>  v2 -> v1 = v2. 



Axiom wpConjunctive : forall stmt  P1 P2 ,
  ( wp_propag_stmt stmt ( fun s => P1 s /\ P2 s) ) = 
  ( fun s => 
          ( wp_propag_stmt stmt ( fun s => P1 s) s)  /\
          ( wp_propag_stmt stmt ( fun s => P2 s) s)).





Axiom eqRefl : forall v , eq_var v v = true.

Axiom eq_v1v2_true : forall v y, eq_var v y = true -> v = y.
