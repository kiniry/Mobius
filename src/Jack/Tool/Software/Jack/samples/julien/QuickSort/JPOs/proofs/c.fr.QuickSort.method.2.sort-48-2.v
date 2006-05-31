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
Hypothesis hyp1 : ~ l_lo < l_hi.
Hypothesis hyp2 : instances this.
Hypothesis hyp3 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_i37 : t_int,
   l_lo <= l_i37 /\ l_i37 <= l_hi ->
   exists l_j37 : t_int,
     (l_lo <= l_j37 /\ l_j37 <= l_hi) /\
     intelements (f_tab this) l_j37 = intelements (f_tab this) l_i37.
Proof with autoJ.
(* Write your proof here *)
intros l_i.
startJack.
exists l_i...



Qed.
End JackProof.
