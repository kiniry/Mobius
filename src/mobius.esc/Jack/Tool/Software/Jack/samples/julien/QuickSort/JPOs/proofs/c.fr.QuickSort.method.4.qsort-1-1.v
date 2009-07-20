Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable this : REFERENCES.
Variable l_beg : t_int.
Variable l_end : t_int.
Hypothesis req1 : (((f_tab this <> null /\ 0 <= l_beg) /\
              l_beg < arraylength (f_tab this)) /\
             (f_tab this <> null /\ 0 <= l_end) /\
             l_end < arraylength (f_tab this)) /\ true = true.
Hypothesis hyp1 : ~ l_beg + 1 < l_end.
Hypothesis hyp2 : instances this.
Hypothesis hyp3 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_i : t_int,
   t_int ->
   forall l_j94 : t_int,
   l_beg <= l_i /\ l_i <= l_end ->
   l_beg <= l_j94 /\ l_j94 <= l_end ->
   l_i < l_j94 ->
   intelements (f_tab this) l_i <= intelements (f_tab this) l_j94.
Proof with autoJ.
(* Write your proof here *)
startJack.
destruct l_end; 
destruct l_beg; j_omega.
destruct l_i; destruct l_j94; j_omega.
de.

Qed.
End JackProof.
