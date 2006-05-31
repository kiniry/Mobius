Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_20 : REFERENCES -> t_int -> t_int.
Variable l_right40_3 : t_int.
Variable l_left40_3 : t_int.
Variable this : REFERENCES.
Variable l_lo : t_int.
Variable l_hi : t_int.
Hypothesis req1 : ((((f_tab this <> null /\ 0 <= l_lo) /\
               l_lo < arraylength (f_tab this)) /\ 
              0 <= l_hi) /\ l_hi < arraylength (f_tab this)) /\ 
            true = true.
Hypothesis hyp1 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_20 x0 = intelements x0.
Hypothesis hyp2 : forall T216 : REFERENCES,
            singleton REFERENCES (f_tab this) T216 ->
            forall x0 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x0 ->
            intelements_20 T216 x0 = intelements T216 x0.
Hypothesis hyp3 : ~ l_left40_3 < l_right40_3.
Hypothesis hyp4 : f_tab this <> null.
Hypothesis hyp5 : (((((l_lo <= l_left40_3 /\ l_left40_3 <= l_right40_3) /\
                l_right40_3 <= l_hi) /\
               (forall l_m : t_int,
                l_lo <= l_m /\ l_m < l_left40_3 ->
                intelements_20 (f_tab this) l_m <=
                intelements (f_tab this) l_hi)) /\
              (forall l_n : t_int,
               l_right40_3 < l_n /\ l_n <= l_hi ->
               intelements (f_tab this) l_hi <=
               intelements_20 (f_tab this) l_n)) /\
             intelements (f_tab this) l_hi <=
             intelements_20 (f_tab this) l_right40_3) /\
            (forall l_i51 : t_int,
             l_lo <= l_i51 /\ l_i51 <= l_hi - 1 ->
             exists l_j51 : t_int,
               (l_lo <= l_j51 /\ l_j51 <= l_hi) /\
               intelements (f_tab this) l_j51 =
               intelements_20 (f_tab this) l_i51).
Hypothesis hyp6 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp7 : ~ ~ l_lo < l_hi.
Hypothesis hyp8 : instances this.
Hypothesis hyp9 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_j85 : t_int,
   l_left40_3 < l_j85 /\ l_j85 <= l_hi ->
   intelements (f_tab this) l_hi <= intelements_20 (f_tab this) l_j85.
Proof with autoJ.
(* Write your proof here *)
startJack.
subst.
apply H6...







Qed.
End JackProof.
