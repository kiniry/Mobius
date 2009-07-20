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
            intelements_7 x0 = intelements_8 x0.
Hypothesis hyp2 : forall T121 : REFERENCES,
            singleton REFERENCES (f_tab this) T121 ->
            forall x0 : t_int,
            ~ singleton t_int l_hi x0 ->
            intelements_7 T121 x0 = intelements_8 T121 x0.
Hypothesis hyp3 : forall x1 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x1 ->
            intelements_8 x1 = intelements_20 x1.
Hypothesis hyp4 : forall x2 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x2 ->
            intelements_20 x2 = intelements x2.
Hypothesis hyp5 : forall T216 : REFERENCES,
            singleton REFERENCES (f_tab this) T216 ->
            forall x3 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x3 ->
            intelements_20 T216 x3 = intelements T216 x3.
Hypothesis hyp6 : forall T122 : REFERENCES,
            singleton REFERENCES (f_tab this) T122 ->
            forall x4 : t_int,
            ~ singleton t_int l_left40_3 x4 ->
            intelements_8 T122 x4 = intelements_20 T122 x4.
Hypothesis hyp7 : intelements_7 (f_tab this) l_left40_3 =
            intelements_20 (f_tab this) l_hi /\
            intelements_7 (f_tab this) l_hi =
            intelements_20 (f_tab this) l_left40_3.
Hypothesis hyp8 : ~ l_left40_3 < l_right40_3.
Hypothesis hyp9 : f_tab this <> null.
Hypothesis hyp10 : ((forall l_i0 : t_int,
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
Hypothesis hyp11 : (((((l_lo <= l_left40_3 /\ l_left40_3 <= l_right40_3) /\
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
Hypothesis hyp12 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp13 : ~ ~ l_lo < l_hi.
Hypothesis hyp14 : instances this.
Hypothesis hyp15 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_i95 : t_int,
   l_lo <= l_i95 /\ l_i95 <= l_hi ->
   exists l_j95 : t_int,
     (l_lo <= l_j95 /\ l_j95 <= l_hi) /\
     intelements (f_tab this) l_j95 = intelements_7 (f_tab this) l_i95.
Proof with autoJ.
(* Write your proof here *)
intros l_i83.
startJack.
subst.

destruct (classic (l_hi = l_i83)).
subst.
rewrite H14.
elim (H11 l_right40_3); [intros x [[h1 h2] h3] | split; j_omega].
rewrite <- h3; exists x; auto.
destruct (classic (l_i83 = l_right40_3)).
subst.
rewrite H13.
elim (H11 l_hi); [intros x [[h1 h2] h3] | split; j_omega].
rewrite <- h3; exists x; auto.
rewrite hyp2; auto.
rewrite hyp6; auto.





Qed.
End JackProof.
