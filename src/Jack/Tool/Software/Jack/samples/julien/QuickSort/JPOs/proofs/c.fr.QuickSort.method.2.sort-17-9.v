Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_8 : REFERENCES -> t_int -> t_int.
Variable intelements_9 : REFERENCES -> t_int -> t_int.
Variable l_right34_1 : t_int.
Variable l_left34_1 : t_int.
Variable intelements_18 : REFERENCES -> t_int -> t_int.
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
            intelements_8 x0 = intelements_9 x0.
Hypothesis hyp2 : f_tab this <> null.
Hypothesis hyp3 : forall T122 : REFERENCES,
            singleton REFERENCES (f_tab this) T122 ->
            forall x0 : t_int,
            ~ singleton t_int l_right34_1 x0 ->
            intelements_8 T122 x0 = intelements_9 T122 x0.
Hypothesis hyp4 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_right34_1.
Hypothesis hyp5 : f_tab this <> null.
Hypothesis hyp6 : l_left34_1 < l_right34_1.
Hypothesis hyp7 : l_left34_1 < l_right34_1.
Hypothesis hyp8 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_left34_1.
Hypothesis hyp9 : forall x1 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x1 ->
            intelements_9 x1 = intelements_18 x1.
Hypothesis hyp10 : forall T123 : REFERENCES,
             singleton REFERENCES (f_tab this) T123 ->
             forall x2 : t_int,
             ~ singleton t_int l_left34_1 x2 ->
             intelements_9 T123 x2 = intelements_18 T123 x2.
Hypothesis hyp11 : intelements_8 (f_tab this) l_left34_1 =
             intelements_18 (f_tab this) l_right34_1 /\
             intelements_8 (f_tab this) l_right34_1 =
             intelements_18 (f_tab this) l_left34_1.
Hypothesis hyp12 : forall x3 : REFERENCES,
             ~ singleton REFERENCES (f_tab this) x3 ->
             intelements_18 x3 = intelements x3.
Hypothesis hyp13 : forall T204 : REFERENCES,
             singleton REFERENCES (f_tab this) T204 ->
             forall x4 : t_int,
             ~ interval l_lo (j_sub l_hi 1) x4 ->
             intelements_18 T204 x4 = intelements T204 x4.
Hypothesis hyp14 : l_left34_1 < l_right34_2.
Hypothesis hyp15 : l_right34_1 < l_right34_2.
Hypothesis hyp16 : l_left34_2 <= l_left34_1.
Hypothesis hyp17 : l_left34_2 < l_right34_2.
Hypothesis hyp18 : f_tab this <> null.
Hypothesis hyp19 : ~
             intelements (f_tab this) l_hi <=
             intelements_18 (f_tab this) l_right34_1.
Hypothesis hyp20 : (forall l_k69 : t_int,
              l_lo <= l_k69 /\ l_k69 < l_left34_1 ->
              intelements_18 (f_tab this) l_k69 <=
              intelements (f_tab this) l_hi) /\
             (forall l_k70 : t_int,
              l_right34_1 < l_k70 /\ l_k70 <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_18 (f_tab this) l_k70).
Hypothesis hyp21 : ((l_left34_1 <= l_right34_1 /\ l_right34_1 <= l_hi) /\
              (forall l_k63 : t_int,
               l_lo <= l_k63 /\ l_k63 < l_left34_1 ->
               intelements_18 (f_tab this) l_k63 <=
               intelements (f_tab this) l_hi)) /\
             (forall l_k64 : t_int,
              l_right34_1 < l_k64 /\ l_k64 <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_18 (f_tab this) l_k64).
Hypothesis hyp22 : ~
             intelements_18 (f_tab this) l_left34_1 <=
             intelements (f_tab this) l_hi.
Hypothesis hyp23 : (l_lo <= l_left34_1 /\ l_left34_1 <= l_right34_2) /\
             (forall l_k56 : t_int,
              l_lo <= l_k56 /\ l_k56 < l_left34_1 ->
              intelements_18 (f_tab this) l_k56 <=
              intelements (f_tab this) l_hi).
Hypothesis hyp24 : (((((l_lo <= l_left34_2 /\ l_left34_2 <= l_right34_2) /\
                 l_right34_2 <= l_hi) /\
                (forall l_m : t_int,
                 l_lo <= l_m /\ l_m < l_left34_2 ->
                 intelements_18 (f_tab this) l_m <=
                 intelements (f_tab this) l_hi)) /\
               (forall l_n : t_int,
                l_right34_2 < l_n /\ l_n <= l_hi ->
                intelements (f_tab this) l_hi <=
                intelements_18 (f_tab this) l_n)) /\
              intelements (f_tab this) l_hi <=
              intelements_18 (f_tab this) l_right34_2) /\
             (forall l_i45 : t_int,
              l_lo <= l_i45 /\ l_i45 <= l_hi - 1 ->
              exists l_j45 : t_int,
                (l_lo <= l_j45 /\ l_j45 <= l_hi) /\
                intelements (f_tab this) l_j45 =
                intelements_18 (f_tab this) l_i45).
Hypothesis hyp25 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp26 : ~ ~ l_lo < l_hi.
Hypothesis hyp27 : instances this.
Hypothesis hyp28 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   l_right34_1 - l_left34_1 < l_right34_2 - l_left34_2.
Proof with autoJ.
(* Write your proof here *)
startJack.
j_omega.




Qed.
End JackProof.
