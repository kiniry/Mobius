Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_12 : REFERENCES -> t_int.
Variable shortelements_5 : REFERENCES -> t_short.
Variable byteelements_5 : REFERENCES -> t_byte.
Variable booleanelements_5 : REFERENCES -> bool.
Variable charelements_5 : REFERENCES -> t_char.
Variable refelements_5 : REFERENCES -> REFERENCES.
Variable newObject_14 : REFERENCES.
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
Hypothesis hyp1 : ~ instances newObject_14.
Hypothesis hyp2 : newObject_14 <> null.
Hypothesis hyp3 : f_tab this <> null.
Hypothesis hyp4 : ~ interval 0 (j_sub (arraylength (f_tab this)) 1) l_right34_1.
Hypothesis hyp5 : false <> true.
Hypothesis hyp6 : l_left34_1 < l_right34_1.
Hypothesis hyp7 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_18 x0 = intelements x0.
Hypothesis hyp8 : forall T184 : REFERENCES,
            singleton REFERENCES (f_tab this) T184 ->
            forall x0 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x0 ->
            intelements_18 T184 x0 = intelements T184 x0.
Hypothesis hyp9 : ~ l_left34_1 < l_right34_2.
Hypothesis hyp10 : l_left34_2 < l_right34_2.
Hypothesis hyp11 : f_tab this <> null.
Hypothesis hyp12 : ((l_left34_1 <= l_right34_1 /\ l_right34_1 <= l_hi) /\
              (forall l_k57 : t_int,
               l_lo <= l_k57 /\ l_k57 < l_left34_1 ->
               intelements_18 (f_tab this) l_k57 <=
               intelements (f_tab this) l_hi)) /\
             (forall l_k58 : t_int,
              l_right34_1 < l_k58 /\ l_k58 <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_18 (f_tab this) l_k58).
Hypothesis hyp13 : (l_lo <= l_left34_1 /\ l_left34_1 <= l_right34_2) /\
             (forall l_k51 : t_int,
              l_lo <= l_k51 /\ l_k51 < l_left34_1 ->
              intelements_18 (f_tab this) l_k51 <=
              intelements (f_tab this) l_hi).
Hypothesis hyp14 : (((((l_lo <= l_left34_2 /\ l_left34_2 <= l_right34_2) /\
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
Hypothesis hyp15 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp16 : ~ ~ l_lo < l_hi.
Hypothesis hyp17 : instances this.
Hypothesis hyp18 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   false = true.
Proof with autoJ.
(* Write your proof here *)
startJack.
destruct hyp4; split; j_omega.



Qed.
End JackProof.
