Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable this : REFERENCES.
Variable l_i0 : t_int.
Hypothesis req1 : true = true /\ true = true.
Hypothesis hyp1 : false = false.
Hypothesis hyp2 : ~ f_tab this <> null.
Hypothesis hyp3 : instances this.
Hypothesis hyp4 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   l_i0 < arraylength (f_tab this).
Proof with autoJ.
(* Write your proof here *)
startJack.

Qed.
End JackProof.
