Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
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
Hypothesis hyp1 : f_tab this <> null.
Hypothesis hyp2 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_left34_1.
Hypothesis hyp3 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_18 x0 = intelements x0.
Hypothesis hyp4 : forall T194 : REFERENCES,
            singleton REFERENCES (f_tab this) T194 ->
            forall x0 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x0 ->
            intelements_18 T194 x0 = intelements T194 x0.
Hypothesis hyp5 : l_left34_1 < l_right34_2.
Hypothesis hyp6 : l_left34_2 < l_right34_2.
Hypothesis hyp7 : f_tab this <> null.
Hypothesis hyp8 : ~
            intelements_18 (f_tab this) l_left34_1 <=
            intelements (f_tab this) l_hi.
Hypothesis hyp9 : (l_lo <= l_left34_1 /\ l_left34_1 <= l_right34_2) /\
            (forall l_k52 : t_int,
             l_lo <= l_k52 /\ l_k52 < l_left34_1 ->
             intelements_18 (f_tab this) l_k52 <=
             intelements (f_tab this) l_hi).
Hypothesis hyp10 : (((((l_lo <= l_left34_2 /\ l_left34_2 <= l_right34_2) /\
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
Hypothesis hyp11 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp12 : ~ ~ l_lo < l_hi.
Hypothesis hyp13 : instances this.
Hypothesis hyp14 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   0 <= l_right34_2 - l_left34_1.
Proof with autoJ.
(* Write your proof here *)
startJack.

Qed.
End JackProof.
