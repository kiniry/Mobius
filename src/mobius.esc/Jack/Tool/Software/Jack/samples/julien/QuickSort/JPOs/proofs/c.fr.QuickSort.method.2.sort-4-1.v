Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_4 : REFERENCES -> t_int -> t_int.
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
Hypothesis hyp1 : f_tab this <> null.
Hypothesis hyp2 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_4 x0 = intelements_7 x0.
Hypothesis hyp3 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_7 x0 = intelements_8 x0.
Hypothesis hyp4 : forall T121 : REFERENCES,
            singleton REFERENCES (f_tab this) T121 ->
            forall x1 : t_int,
            ~ singleton t_int l_hi x1 ->
            intelements_7 T121 x1 = intelements_8 T121 x1.
Hypothesis hyp5 : forall x2 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x2 ->
            intelements_8 x2 = intelements_20 x2.
Hypothesis hyp6 : forall x3 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x3 ->
            intelements_20 x3 = intelements x3.
Hypothesis hyp7 : forall T216 : REFERENCES,
            singleton REFERENCES (f_tab this) T216 ->
            forall x4 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x4 ->
            intelements_20 T216 x4 = intelements T216 x4.
Hypothesis hyp8 : l_left40_3 + 1 < arraylength (f_tab this).
Hypothesis hyp9 : ~ 0 < l_left40_3.
Hypothesis hyp10 : forall T90 : REFERENCES,
             singleton REFERENCES (f_tab this) T90 ->
             forall x5 : t_int,
             ~ interval (j_add l_left40_3 1) l_hi x5 ->
             intelements_4 T90 x5 = intelements_7 T90 x5.
Hypothesis hyp11 : (forall l_i0 : t_int,
              t_int ->
              forall l_j36 : t_int,
              l_left40_3 + 1 <= l_i0 /\ l_i0 <= l_hi ->
              l_left40_3 + 1 <= l_j36 /\ l_j36 <= l_hi ->
              l_i0 < l_j36 ->
              intelements_4 (f_tab this) l_i0 <=
              intelements_4 (f_tab this) l_j36) /\
             (forall l_i37 : t_int,
              l_left40_3 + 1 <= l_i37 /\ l_i37 <= l_hi ->
              exists l_j37 : t_int,
                (l_left40_3 + 1 <= l_j37 /\ l_j37 <= l_hi) /\
                intelements_7 (f_tab this) l_j37 =
                intelements_4 (f_tab this) l_i37).
Hypothesis hyp12 : (((forall l_i0 : t_int,
                t_int ->
                forall l_j101 : t_int,
                l_lo <= l_i0 /\ l_i0 < l_left40_3 ->
                l_lo <= l_j101 /\ l_j101 < l_left40_3 ->
                l_i0 < l_j101 ->
                intelements_7 (f_tab this) l_i0 <=
                intelements_7 (f_tab this) l_j101) /\
               (forall l_i102 : t_int,
                l_lo <= l_i102 /\ l_i102 < l_left40_3 ->
                intelements_7 (f_tab this) l_i102 <=
                intelements_7 (f_tab this) l_left40_3)) /\
              (forall l_j104 : t_int,
               l_left40_3 < l_j104 /\ l_j104 <= l_hi ->
               intelements_7 (f_tab this) l_left40_3 <=
               intelements_7 (f_tab this) l_j104)) /\
             (forall l_i106 : t_int,
              l_lo <= l_i106 /\ l_i106 <= l_hi ->
              exists l_j106 : t_int,
                (l_lo <= l_j106 /\ l_j106 <= l_hi) /\
                intelements (f_tab this) l_j106 =
                intelements_7 (f_tab this) l_i106).
Hypothesis hyp13 : ((forall l_i0 : t_int,
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
Hypothesis hyp14 : forall T122 : REFERENCES,
             singleton REFERENCES (f_tab this) T122 ->
             forall x6 : t_int,
             ~ singleton t_int l_left40_3 x6 ->
             intelements_8 T122 x6 = intelements_20 T122 x6.
Hypothesis hyp15 : intelements_7 (f_tab this) l_left40_3 =
             intelements_20 (f_tab this) l_hi /\
             intelements_7 (f_tab this) l_hi =
             intelements_20 (f_tab this) l_left40_3.
Hypothesis hyp16 : ~ l_left40_3 < l_right40_3.
Hypothesis hyp17 : f_tab this <> null.
Hypothesis hyp18 : ((forall l_i0 : t_int,
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
Hypothesis hyp19 : (((((l_lo <= l_left40_3 /\ l_left40_3 <= l_right40_3) /\
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
Hypothesis hyp20 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp21 : ~ ~ l_lo < l_hi.
Hypothesis hyp22 : instances this.
Hypothesis hyp23 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_i0 : t_int,
   t_int ->
   forall l_j111 : t_int,
   l_lo <= l_i0 /\ l_i0 <= l_hi ->
   l_lo <= l_j111 /\ l_j111 <= l_hi ->
   l_i0 < l_j111 ->
   intelements_4 (f_tab this) l_i0 <= intelements_4 (f_tab this) l_j111.
Proof with autoJ.
(* Write your proof here *)
intros l_i0 _ l_j.
startJack.
destruct (classic (l_left40_3 < l_i0)); destruct (classic (l_left40_3 < l_j)).
subst.
apply H25; auto; j_omega.
j_omega.
solveInc.
subst.

rewrite  hyp10; auto; [idtac | unfold not; intros; j_omega].
elim (H26 l_j); j_omega;
intros x [[h1 h1']  h2].
rewrite <- h2. 
simpl in h1.
eassert(h := (H20 x _ )); auto.
split; j_omega.
destrJlt(l_i0 <= l_right40_3).
eassert(h3 := (H18 l_i0 _ _ _)); auto.
j_omega.

subst; j_omega.
j_omega.











Qed.
End JackProof.
