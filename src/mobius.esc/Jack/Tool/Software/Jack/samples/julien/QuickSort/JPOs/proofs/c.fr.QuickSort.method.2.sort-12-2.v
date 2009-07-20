Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_6 : REFERENCES -> t_int -> t_int.
Variable intelements_7 : REFERENCES -> t_int -> t_int.
Variable intelements_8 : REFERENCES -> t_int -> t_int.
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
            intelements_6 x0 = intelements_7 x0.
Hypothesis hyp2 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_7 x0 = intelements_8 x0.
Hypothesis hyp3 : forall T121 : REFERENCES,
            singleton REFERENCES (f_tab this) T121 ->
            forall x1 : t_int,
            ~ singleton t_int l_hi x1 ->
            intelements_7 T121 x1 = intelements_8 T121 x1.
Hypothesis hyp4 : forall x2 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x2 ->
            intelements_8 x2 = intelements_20 x2.
Hypothesis hyp5 : forall x3 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x3 ->
            intelements_20 x3 = intelements x3.
Hypothesis hyp6 : forall T216 : REFERENCES,
            singleton REFERENCES (f_tab this) T216 ->
            forall x4 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x4 ->
            intelements_20 T216 x4 = intelements T216 x4.
Hypothesis hyp7 : 0 < l_left40_3.
Hypothesis hyp8 : forall T110 : REFERENCES,
            singleton REFERENCES (f_tab this) T110 ->
            forall x5 : t_int,
            ~ interval l_lo (j_sub l_left40_3 1) x5 ->
            intelements_6 T110 x5 = intelements_7 T110 x5.
Hypothesis hyp9 : (forall l_i0 : t_int,
             t_int ->
             forall l_j36 : t_int,
             l_lo <= l_i0 /\ l_i0 <= l_left40_3 - 1 ->
             l_lo <= l_j36 /\ l_j36 <= l_left40_3 - 1 ->
             l_i0 < l_j36 ->
             intelements_6 (f_tab this) l_i0 <=
             intelements_6 (f_tab this) l_j36) /\
            (forall l_i37 : t_int,
             l_lo <= l_i37 /\ l_i37 <= l_left40_3 - 1 ->
             exists l_j37 : t_int,
               (l_lo <= l_j37 /\ l_j37 <= l_left40_3 - 1) /\
               intelements_7 (f_tab this) l_j37 =
               intelements_6 (f_tab this) l_i37).
Hypothesis hyp10 : ((forall l_i0 : t_int,
               t_int ->
               t_int ->
               l_lo <= l_i0 /\ l_i0 < l_left40_3 ->
               intelements_7 (f_tab this) l_i0 <=
               intelements_7 (f_tab this) l_left40_3) /\
              (forall l_j93 : t_int,
               l_left40_3 < l_j93 /\ l_j93 <= l_hi ->
               intelements_7 (f_tab this) l_left40_3 <=
               intelements_7 (f_tab this) l_j93)) /\
             (forall l_i95 : t_int,
              l_lo <= l_i95 /\ l_i95 <= l_hi ->
              exists l_j95 : t_int,
                (l_lo <= l_j95 /\ l_j95 <= l_hi) /\
                intelements (f_tab this) l_j95 =
                intelements_7 (f_tab this) l_i95).
Hypothesis hyp11 : forall T122 : REFERENCES,
             singleton REFERENCES (f_tab this) T122 ->
             forall x6 : t_int,
             ~ singleton t_int l_left40_3 x6 ->
             intelements_8 T122 x6 = intelements_20 T122 x6.
Hypothesis hyp12 : intelements_7 (f_tab this) l_left40_3 =
             intelements_20 (f_tab this) l_hi /\
             intelements_7 (f_tab this) l_hi =
             intelements_20 (f_tab this) l_left40_3.
Hypothesis hyp13 : ~ l_left40_3 < l_right40_3.
Hypothesis hyp14 : f_tab this <> null.
Hypothesis hyp15 : ((forall l_i0 : t_int,
               t_int ->
               t_int ->
               l_lo <= l_i0 /\ l_i0 < l_left40_3 ->
               intelements_20 (f_tab this) l_i0 <=
               intelements (f_tab this) l_hi) /\
              (forall l_j85 : t_int,
               l_left40_3 < l_j85 /\ l_j85 <= l_hi ->
               intelements (f_tab this) l_hi <=
               intelements_20 (f_tab this) l_j85)) /\
             (forall l_i87 : t_int,
              l_lo <= l_i87 /\ l_i87 <= l_hi ->
              exists l_j87 : t_int,
                (l_lo <= l_j87 /\ l_j87 <= l_hi) /\
                intelements (f_tab this) l_j87 =
                intelements_20 (f_tab this) l_i87).
Hypothesis hyp16 : (((((l_lo <= l_left40_3 /\ l_left40_3 <= l_right40_3) /\
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
Hypothesis hyp17 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp18 : ~ ~ l_lo < l_hi.
Hypothesis hyp19 : instances this.
Hypothesis hyp20 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_i102 : t_int,
   l_lo <= l_i102 /\ l_i102 < l_left40_3 ->
   intelements_6 (f_tab this) l_i102 <= intelements_6 (f_tab this) l_left40_3.
Proof with autoJ.
(* Write your proof here *)
intros l_i90.
startJack.
subst...
destrJlt (l_i90 <=  l_right40_3); j_omega.
elim (H19 l_i90); j_omega.
intros; elimAnd.
rewrite <- H23.
rewrite hyp8; j_omega...

apply H15; j_omega...









Qed.
End JackProof.
