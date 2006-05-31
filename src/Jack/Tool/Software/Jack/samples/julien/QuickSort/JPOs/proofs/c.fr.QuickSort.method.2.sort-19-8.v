Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_7 : REFERENCES -> t_int -> t_int.
Variable intelements_8 : REFERENCES -> t_int -> t_int.
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
Hypothesis hyp1 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_7 x0 = intelements_8 x0.
Hypothesis hyp2 : f_tab this <> null.
Hypothesis hyp3 : forall T108 : REFERENCES,
            singleton REFERENCES (f_tab this) T108 ->
            forall x0 : t_int,
            ~ singleton t_int l_right34_1 x0 ->
            intelements_7 T108 x0 = intelements_8 T108 x0.
Hypothesis hyp4 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_right34_1.
Hypothesis hyp5 : false <> true.
Hypothesis hyp6 : l_left34_1 < l_right34_1.
Hypothesis hyp7 : l_left34_1 < l_right34_1.
Hypothesis hyp8 : forall x1 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x1 ->
            intelements_8 x1 = intelements_17 x1.
Hypothesis hyp9 : forall T109 : REFERENCES,
            singleton REFERENCES (f_tab this) T109 ->
            forall x2 : t_int,
            ~ singleton t_int l_left34_1 x2 ->
            intelements_8 T109 x2 = intelements_17 T109 x2.
Hypothesis hyp10 : intelements_7 (f_tab this) l_left34_1 =
             intelements_17 (f_tab this) l_right34_1 /\
             intelements_7 (f_tab this) l_right34_1 =
             intelements_17 (f_tab this) l_left34_1.
Hypothesis hyp11 : forall x3 : REFERENCES,
             ~ singleton REFERENCES (f_tab this) x3 ->
             intelements_17 x3 = intelements x3.
Hypothesis hyp12 : forall T170 : REFERENCES,
             singleton REFERENCES (f_tab this) T170 ->
             forall x4 : t_int,
             ~ interval l_lo (j_sub l_hi 1) x4 ->
             intelements_17 T170 x4 = intelements T170 x4.
Hypothesis hyp13 : ~ l_left34_1 < l_right34_2.
Hypothesis hyp14 : l_left34_2 < l_right34_2.
Hypothesis hyp15 : f_tab this <> null.
Hypothesis hyp16 : ~
             intelements (f_tab this) l_hi <=
             intelements_17 (f_tab this) l_right34_1.
Hypothesis hyp17 : (forall l_k62 : t_int,
              l_lo <= l_k62 /\ l_k62 < l_left34_1 ->
              intelements_17 (f_tab this) l_k62 <=
              intelements (f_tab this) l_hi) /\
             (forall l_k63 : t_int,
              l_right34_1 < l_k63 /\ l_k63 <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_17 (f_tab this) l_k63).
Hypothesis hyp18 : ((l_left34_1 <= l_right34_1 /\ l_right34_1 <= l_hi) /\
              (forall l_k56 : t_int,
               l_lo <= l_k56 /\ l_k56 < l_left34_1 ->
               intelements_17 (f_tab this) l_k56 <=
               intelements (f_tab this) l_hi)) /\
             (forall l_k57 : t_int,
              l_right34_1 < l_k57 /\ l_k57 <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_17 (f_tab this) l_k57).
Hypothesis hyp19 : (l_lo <= l_left34_1 /\ l_left34_1 <= l_right34_2) /\
             (forall l_k50 : t_int,
              l_lo <= l_k50 /\ l_k50 < l_left34_1 ->
              intelements_17 (f_tab this) l_k50 <=
              intelements (f_tab this) l_hi).
Hypothesis hyp20 : ((((l_lo <= l_left34_2 /\ l_left34_2 <= l_right34_2) /\
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
              l_left34_2 <= l_i44 /\ l_i44 <= l_right34_2 - 1 ->
              exists l_j44 : t_int,
                (l_lo <= l_j44 /\ l_j44 <= l_hi) /\
                intelements (f_tab this) l_j44 =
                intelements_17 (f_tab this) l_i44).
Hypothesis hyp21 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp22 : ~ ~ l_lo < l_hi.
Hypothesis hyp23 : instances this.
Hypothesis hyp24 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   l_right34_1 - l_left34_1 < l_right34_1 - l_left34_1.
Proof with autoJ.
(* Write your proof here *)
startJack.
subst...
j_omega.
Qed.
End JackProof.
