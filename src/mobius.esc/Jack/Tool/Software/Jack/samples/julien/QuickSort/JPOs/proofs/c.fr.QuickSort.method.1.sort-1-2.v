Require Import Bool.
Require Import ZArith.
Require Import Classical.
Add LoadPath "/home/jcharles/sources/runtime-workspace/QuickSort/JPOs".
Require Import "fr_QuickSort_classes".
Load "user_extensions.v".
Require Import "fr_QuickSort".
Import JackLogic.
Open Scope Z_scope.
Open Scope J_Scope.

Section JackProof.

Variable this : Reference.
Hypothesis req1 : f_tab this <> null.
Hypothesis hyp1 : ~ 0 < arraylength (f_tab this).
Hypothesis hyp2 : f_tab this <> null.
Hypothesis hyp3 : instances this.
Hypothesis hyp4 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.
Ltac purify := simpl_pure.

Lemma l: 
   forall l_i1 : t_int,
   0 <= l_i1 /\ l_i1 <= arraylength (f_tab this) - 1 ->
   exists l_j2 : t_int,
     (0 <= l_j2 /\ l_j2 <= arraylength (f_tab this) - 1) /\
     intelements (f_tab this) l_j2 = intelements (f_tab this) l_i1.
Proof with autoJ.
(* Write your proof here *)
intros l_i.
startJack.
exists l_i...



Qed.
End JackProof.
