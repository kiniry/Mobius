Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable l_right40_1 : t_int.
Variable l_left40_1 : t_int.
Variable intelements_19 : REFERENCES -> t_int -> t_int.
Variable l_right40_2 : t_int.
Variable l_left40_2 : t_int.
Variable this : REFERENCES.
Variable l_lo : t_int.
Variable l_hi : t_int.
Hypothesis req1 : ((((f_tab this <> null /\ 0 <= l_lo) /\
               l_lo < arraylength (f_tab this)) /\ 
              0 <= l_hi) /\ l_hi < arraylength (f_tab this)) /\ 
            true = true.
Hypothesis hyp1 : f_tab this <> null.
Hypothesis hyp2 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_right40_1.
Hypothesis hyp3 : f_tab this <> null.
Hypothesis hyp4 : l_left40_1 < l_right40_1.
Hypothesis hyp5 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_left40_1.
Hypothesis hyp6 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_19 x0 = intelements x0.
Hypothesis hyp7 : forall T213 : REFERENCES,
            singleton REFERENCES (f_tab this) T213 ->
            forall x0 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x0 ->
            intelements_19 T213 x0 = intelements T213 x0.
Hypothesis hyp8 : l_left40_1 < l_right40_2.
Hypothesis hyp9 : l_left40_2 <= l_left40_1.
Hypothesis hyp10 : l_left40_2 < l_right40_2.
Hypothesis hyp11 : f_tab this <> null.
Hypothesis hyp12 : ~
             intelements (f_tab this) l_hi <=
             intelements_19 (f_tab this) l_right40_1.
Hypothesis hyp13 : ~
             intelements_19 (f_tab this) l_left40_1 <=
             intelements (f_tab this) l_hi.
Hypothesis hyp14 : (((l_left40_1 <= l_right40_1 /\ l_right40_1 <= l_right40_2) /\
               l_right40_1 <= l_hi) /\
              (forall l_k69 : t_int,
               l_lo <= l_k69 /\ l_k69 < l_left40_1 ->
               intelements_19 (f_tab this) l_k69 <=
               intelements (f_tab this) l_hi)) /\
             (forall l_k70 : t_int,
              l_right40_1 < l_k70 /\ l_k70 <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_19 (f_tab this) l_k70).
Hypothesis hyp15 : ((l_lo <= l_left40_1 /\ l_left40_2 <= l_left40_1) /\
              l_left40_1 <= l_right40_2) /\
             (forall l_k62 : t_int,
              l_lo <= l_k62 /\ l_k62 < l_left40_1 ->
              intelements_19 (f_tab this) l_k62 <=
              intelements (f_tab this) l_hi).
Hypothesis hyp16 : (((((l_lo <= l_left40_2 /\ l_left40_2 <= l_right40_2) /\
                 l_right40_2 <= l_hi) /\
                (forall l_m : t_int,
                 l_lo <= l_m /\ l_m < l_left40_2 ->
                 intelements_19 (f_tab this) l_m <=
                 intelements (f_tab this) l_hi)) /\
               (forall l_n : t_int,
                l_right40_2 < l_n /\ l_n <= l_hi ->
                intelements (f_tab this) l_hi <=
                intelements_19 (f_tab this) l_n)) /\
              intelements (f_tab this) l_hi <=
              intelements_19 (f_tab this) l_right40_2) /\
             (forall l_i51 : t_int,
              l_lo <= l_i51 /\ l_i51 <= l_hi - 1 ->
              exists l_j51 : t_int,
                (l_lo <= l_j51 /\ l_j51 <= l_hi) /\
                intelements (f_tab this) l_j51 =
                intelements_19 (f_tab this) l_i51).
Hypothesis hyp17 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp18 : ~ ~ l_lo < l_hi.
Hypothesis hyp19 : instances this.
Hypothesis hyp20 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   l_left40_1 < l_right40_1 -> l_right40_1 < l_right40_2.
Proof with autoJ.
(* Write your proof here *)
startJack.

assert (l_right40_1 <> l_right40_2); 
unfold not; intros; subst;
subst;j_omega.
destrJlt(l_right40_1 <= l_right40_2).
subst...









Qed.
End JackProof.
