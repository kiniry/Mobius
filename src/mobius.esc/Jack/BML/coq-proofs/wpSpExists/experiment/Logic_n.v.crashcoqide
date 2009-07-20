Require Import BasicDef.

Definition assertion := state -> Prop.

Definition preProg := state -> Prop.
Definition postProg := state -> state -> Prop.

Fixpoint assertionIndex (n:nat) : Type := 
 match n with 
 | O => Prop
 | S n => state -> assertionIndex n
 end.

Inductive listP : Type :=
 | nilP  : listP
 | consP : Prop -> listP -> listP.

Fixpoint appendP (l1 l2:listP) {struct l1} : listP :=
 match l1 with 
 | nilP => l2
 | consP p l1 => consP p (appendP l1 l2)
 end.

Fixpoint InP (P:Prop) (l:listP) {struct l} : Prop :=
 match l with
 | nilP => False
 | consP P' l => P = P' \/ InP P l
 end.


(*added by mariela : to be proven*)
Axiom InPappendl1l2_InPl1_or_InPl2 : forall l1 l2, 
    ( forall P , InP P ( appendP  l1 l2 )  -> (  InP P l1 ) \/ (  InP P l2 ) ).

Lemma InP_appendP_l : forall l1 l2,
   (forall P, InP P (appendP l1 l2) -> P) -> 
   (forall P, InP P l1 -> P).
Proof.
 induction l1;simpl;intros.
 elim H0.
 destruct H0. apply H;auto. apply (IHl1 l2);auto.
 intros;apply H;auto.
Qed.

Lemma InP_appendP_r : forall l1 l2,
   (forall P, InP P (appendP l1 l2) -> P) -> 
   (forall P, InP P l2 -> P).
Proof.
 induction l1;simpl;intros.
 apply H;trivial.
 apply (IHl1 l2);intros.
 apply H;auto. auto.
Qed.

Lemma InP_appendP : forall l1 l2,
   (forall P, InP P l1 -> P) ->
   (forall P, InP P l2 -> P) -> 
   (forall P, InP P (appendP l1 l2) -> P).
Proof.
 induction l1;simpl;trivial;intros.
 destruct H1. apply H;auto. 
 apply (IHl1 l2);trivial;intros. apply H;auto.
Qed.









(*todo*)
Axiom allIn_P_list_impl_head_list : forall (head : Prop) tail,
( forall P, InP P  ( consP head tail) -> P ) ->
head .    

Axiom allIn_P_list_impl_tail_list : forall (head : Prop) tail,
( forall P, InP P  ( consP head tail) -> P ) ->
( forall P, InP P tail -> P).





















Fixpoint mkLambda (n:nat) (P:Prop) {struct n} : assertionIndex n :=
 match n return assertionIndex n with 
 | O => P
 | S n => fun s => mkLambda n P
 end.

Fixpoint mkImp (n:nat) : 
   assertionIndex n -> assertionIndex n -> assertionIndex n :=
 match n return assertionIndex n -> assertionIndex n -> assertionIndex n with
 | O => fun P Q => P -> Q
 | S n => fun P Q => fun s => mkImp n (P s) (Q s)
 end.

Fixpoint mkAnd (n:nat) : 
   assertionIndex n -> assertionIndex n -> assertionIndex n :=
 match n return assertionIndex n -> assertionIndex n -> assertionIndex n with
 | O => fun P Q => P /\ Q
 | S n => fun P Q => fun s => mkAnd n (P s) (Q s)
 end.

Fixpoint mkEq (s:state) (p n : nat) {struct n} : assertionIndex n :=
 match n return assertionIndex n with
 | O => True 
 | S m =>
   fun sn => 
     match p with
     | O => mkLambda m (s=sn) 
     | S q => mkEq s q m
     end
 end.
  
Fixpoint mkProd (n:nat) : assertionIndex n -> Prop :=
 match n return assertionIndex n -> Prop with
 | O => fun P => P
 | S n => fun P => forall s, mkProd n (P s)
 end.

Axiom mkProd_mkImp_refl : forall n A, mkProd n (mkImp n A A).

Axiom mkProd_imp_imp : forall n H1 H2 concl,
 mkProd n (mkImp n H2 H1) -> 
 mkProd n (mkImp n H1 concl) ->
 mkProd n (mkImp n H2 concl).

Axiom mkProd_and_l : forall n Q1 Q2,
   mkProd n (mkImp n (mkAnd n Q1 Q2) Q1).

Axiom mkProd_and_r : forall n Q1 Q2,
   mkProd n (mkImp n (mkAnd n Q1 Q2) Q2).

Axiom mkProd_mkImp : forall n P Q,
  mkProd n P ->
  mkProd n (mkImp n (mkImp n P Q) Q).
 
Axiom mkProd_mkLambda : forall n (P:Prop),
 P -> mkProd n (mkLambda n P).
