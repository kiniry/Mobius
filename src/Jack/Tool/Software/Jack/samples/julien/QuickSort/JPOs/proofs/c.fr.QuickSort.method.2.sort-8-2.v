Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_18 : REFERENCES -> t_int -> t_int.
Variable l_right34_3 : t_int.
Variable l_left34_3 : t_int.
Variable this : REFERENCES.
Variable l_lo : t_int.
Variable l_hi : t_int.
Hypothesis req1 : ((((f_tab this <> null /\ 0 <= l_lo) /\
               l_lo < arraylength (f_tab this)) /\ 
              0 <= l_hi) /\ l_hi < arraylength (f_tab this)) /\ 
            true = true.
Hypothesis hyp1 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_18 x0 = intelements x0.
Hypothesis hyp2 : forall T173 : REFERENCES,
            singleton REFERENCES (f_tab this) T173 ->
            forall x0 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x0 ->
            intelements_18 T173 x0 = intelements T173 x0.
Hypothesis hyp3 : ~ l_left34_3 < l_right34_3.
Hypothesis hyp4 : f_tab this <> null.
Hypothesis hyp5 : ((((l_lo <= l_left34_3 /\ l_left34_3 <= l_right34_3) /\
               l_right34_3 <= l_hi) /\
              (forall l_m : t_int,
               l_lo <= l_m /\ l_m < l_left34_3 ->
               intelements_18 (f_tab this) l_m <=
               intelements (f_tab this) l_hi)) /\
             (forall l_n : t_int,
              l_right34_3 < l_n /\ l_n <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_18 (f_tab this) l_n)) /\
            (forall l_i44 : t_int,
             l_lo <= l_i44 /\ l_i44 <= l_hi - 1 ->
             exists l_j44 : t_int,
               (l_lo <= l_j44 /\ l_j44 <= l_hi) /\
               intelements (f_tab this) l_j44 =
               intelements_18 (f_tab this) l_i44).
Hypothesis hyp6 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp7 : ~ ~ l_lo < l_hi.
Hypothesis hyp8 : instances this.
Hypothesis hyp9 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_j72 : t_int,
   l_left34_3 < l_j72 /\ l_j72 <= l_hi ->
   intelements (f_tab this) l_hi <= intelements_18 (f_tab this) l_j72.
Proof with autoJ.
(* Write your proof here *)
startJack.
subst...

Qed.
End JackProof.
