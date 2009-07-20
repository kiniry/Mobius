Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_9 : REFERENCES -> t_int.
Variable shortelements_2 : REFERENCES -> t_short.
Variable byteelements_2 : REFERENCES -> t_byte.
Variable booleanelements_2 : REFERENCES -> bool.
Variable charelements_2 : REFERENCES -> t_char.
Variable refelements_2 : REFERENCES -> REFERENCES.
Variable newObject_8 : REFERENCES.
Variable l_right34_0 : t_int.
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
Hypothesis hyp1 : ~ instances newObject_8.
Hypothesis hyp2 : newObject_8 <> null.
Hypothesis hyp3 : f_tab this <> null.
Hypothesis hyp4 : ~ interval 0 (j_sub (arraylength (f_tab this)) 1) l_right34_0.
Hypothesis hyp5 : f_tab this <> null.
Hypothesis hyp6 : l_left34_1 < l_right34_0.
Hypothesis hyp7 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_left34_1.
Hypothesis hyp8 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_17 x0 = intelements x0.
Hypothesis hyp9 : forall T170 : REFERENCES,
            singleton REFERENCES (f_tab this) T170 ->
            forall x0 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x0 ->
            intelements_17 T170 x0 = intelements T170 x0.
Hypothesis hyp10 : l_left34_1 < l_right34_2.
Hypothesis hyp11 : l_left34_2 < l_right34_2.
Hypothesis hyp12 : f_tab this <> null.
Hypothesis hyp13 : ((l_left34_1 <= l_right34_0 /\ l_right34_0 <= l_hi) /\
              (forall l_k56 : t_int,
               l_lo <= l_k56 /\ l_k56 < l_left34_1 ->
               intelements_17 (f_tab this) l_k56 <=
               intelements (f_tab this) l_hi)) /\
             (forall l_k57 : t_int,
              l_right34_0 < l_k57 /\ l_k57 <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_17 (f_tab this) l_k57).
Hypothesis hyp14 : ~
             intelements_17 (f_tab this) l_left34_1 <=
             intelements (f_tab this) l_hi.
Hypothesis hyp15 : (l_lo <= l_left34_1 /\ l_left34_1 <= l_right34_2) /\
             (forall l_k50 : t_int,
              l_lo <= l_k50 /\ l_k50 < l_left34_1 ->
              intelements_17 (f_tab this) l_k50 <=
              intelements (f_tab this) l_hi).
Hypothesis hyp16 : ((((l_lo <= l_left34_2 /\ l_left34_2 <= l_right34_2) /\
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
Hypothesis hyp17 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp18 : ~ ~ l_lo < l_hi.
Hypothesis hyp19 : instances this.
Hypothesis hyp20 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   false = true.
Proof with autoJ.
(* Write your proof here *)
startJack.
destruct hyp4...
split; j_omega.


Qed.
End JackProof.
