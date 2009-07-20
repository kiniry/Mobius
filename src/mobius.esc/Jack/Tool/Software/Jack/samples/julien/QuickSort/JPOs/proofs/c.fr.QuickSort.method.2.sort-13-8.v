Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable l_right34_1 : t_int.
Variable l_left34_1 : t_int.
Variable intelements_17 : REFERENCES -> t_int -> t_int.
Variable l_right34_2 : t_int.
Variable l_left34_2 : t_int.
Variable this : REFERENCES.
Variable l_lo : t_int.
Variable l_hi : t_int.
Hypothesis req1 : ((((f_tab this <> null /\ 0 <= l_lo) /\
               l_lo < arraylength (f_tab this)) /\ 
              0 <= l_hi) /\ l_hi < arraylength (f_tab this)) /\ 
            true = true.
Hypothesis hyp1 : false <> true.
Hypothesis hyp2 : f_tab this <> null.
Hypothesis hyp3 : ~ l_left34_1 < l_right34_1.
Hypothesis hyp4 : ~ l_left34_1 < l_right34_1.
Hypothesis hyp5 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_left34_1.
Hypothesis hyp6 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_17 x0 = intelements x0.
Hypothesis hyp7 : forall T170 : REFERENCES,
            singleton REFERENCES (f_tab this) T170 ->
            forall x0 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x0 ->
            intelements_17 T170 x0 = intelements T170 x0.
Hypothesis hyp8 : l_left34_1 < l_right34_2.
Hypothesis hyp9 : l_left34_2 < l_right34_2.
Hypothesis hyp10 : f_tab this <> null.
Hypothesis hyp11 : (forall l_k62 : t_int,
              l_lo <= l_k62 /\ l_k62 < l_left34_1 ->
              intelements_17 (f_tab this) l_k62 <=
              intelements (f_tab this) l_hi) /\
             (forall l_k63 : t_int,
              l_right34_1 < l_k63 /\ l_k63 <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_17 (f_tab this) l_k63).
Hypothesis hyp12 : ((l_left34_1 <= l_right34_1 /\ l_right34_1 <= l_hi) /\
              (forall l_k56 : t_int,
               l_lo <= l_k56 /\ l_k56 < l_left34_1 ->
               intelements_17 (f_tab this) l_k56 <=
               intelements (f_tab this) l_hi)) /\
             (forall l_k57 : t_int,
              l_right34_1 < l_k57 /\ l_k57 <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_17 (f_tab this) l_k57).
Hypothesis hyp13 : ~
             intelements_17 (f_tab this) l_left34_1 <=
             intelements (f_tab this) l_hi.
Hypothesis hyp14 : (l_lo <= l_left34_1 /\ l_left34_1 <= l_right34_2) /\
             (forall l_k50 : t_int,
              l_lo <= l_k50 /\ l_k50 < l_left34_1 ->
              intelements_17 (f_tab this) l_k50 <=
              intelements (f_tab this) l_hi).
Hypothesis hyp15 : ((((l_lo <= l_left34_2 /\ l_left34_2 <= l_right34_2) /\
                l_right34_2 <= l_hi) /\
               (forall l_m : t_int,
                l_lo <= l_m /\ l_m < l_left34_2 ->
                intelements_17 (f_tab this) l_m <=
                intelements (f_tab this) l_hi)) /\
              (forall l_n : t_int,
               l_right34_2 < l_n /\ l_n <= l_hi ->
               intelements (f_tab this) l_hi <=
               intelements_17 (f_tab this) l_n)) /\
             (forall l_i44 : t_int,
              l_lo <= l_i44 /\ l_i44 <= l_hi - 1 ->
              exists l_j44 : t_int,
                (l_lo <= l_j44 /\ l_j44 <= l_hi) /\
                intelements (f_tab this) l_j44 =
                intelements_17 (f_tab this) l_i44).
Hypothesis hyp16 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp17 : ~ ~ l_lo < l_hi.
Hypothesis hyp18 : instances this.
Hypothesis hyp19 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   l_right34_1 - l_left34_1 < l_right34_1 - l_left34_1.
Proof with autoJ.
(* Write your proof here *)
startJack.

Qed.
End JackProof.
