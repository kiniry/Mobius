Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable l_i0_1 : t_int.
Variable this : REFERENCES.
Variable l_i0 : t_int.
Variable l_hi : t_int.
Variable l_pivot0 : t_int.
Hypothesis req1 : (((f_tab this <> null /\ 0 <= l_i0) /\
              l_i0 < arraylength (f_tab this)) /\
             (f_tab this <> null /\ 0 <= l_hi) /\
             l_hi < arraylength (f_tab this)) /\ true = true.
Hypothesis hyp1 : f_tab this <> null.
Hypothesis hyp2 : ~ intelements (f_tab this) l_i0_1 <= l_pivot0.
Hypothesis hyp3 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_i0_1.
Hypothesis hyp4 : l_i0_1 < l_hi.
Hypothesis hyp5 : forall l_k71 : t_int,
            l_i0 <= l_k71 /\ l_k71 < l_i0_1 ->
            intelements (f_tab this) l_k71 <= l_pivot0.
Hypothesis hyp6 : instances this.
Hypothesis hyp7 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_k67 : t_int,
   l_i0 <= l_k67 /\ l_k67 < l_i0_1 ->
   intelements (f_tab this) l_k67 <= l_pivot0.
Proof with autoJ.
(* Write your proof here *)
startJack.
apply hyp5...
Qed.
End JackProof.
