Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable this : REFERENCES.
Variable l_lo : t_int.
Variable l_hi : t_int.
Hypothesis req1 : ((((f_tab this <> null /\ 0 <= l_lo) /\
               l_lo < arraylength (f_tab this)) /\ 
              0 <= l_hi) /\ l_hi < arraylength (f_tab this)) /\ 
            true = true.
Hypothesis hyp1 : f_tab this <> null.
Hypothesis hyp2 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp3 : ~ ~ l_lo < l_hi.
Hypothesis hyp4 : instances this.
Hypothesis hyp5 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_i45 : t_int,
   l_lo <= l_i45 /\ l_i45 <= l_hi - 1 ->
   exists l_j45 : t_int,
     (l_lo <= l_j45 /\ l_j45 <= l_hi) /\
     intelements (f_tab this) l_j45 = intelements (f_tab this) l_i45.
Proof with autoJ.
(* Write your proof here *)
startJack.
exists l_i45; repeat split; auto.
j_omega.
Qed.
End JackProof.
