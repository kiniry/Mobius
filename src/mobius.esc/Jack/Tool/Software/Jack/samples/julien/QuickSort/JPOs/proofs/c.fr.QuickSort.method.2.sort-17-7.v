Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_9 : REFERENCES -> t_int -> t_int.
Variable intelements_10 : REFERENCES -> t_int -> t_int.
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
Hypothesis hyp1 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_9 x0 = intelements_10 x0.
Hypothesis hyp2 : f_tab this <> null.
Hypothesis hyp3 : forall T131 : REFERENCES,
            singleton REFERENCES (f_tab this) T131 ->
            forall x0 : t_int,
            ~ singleton t_int l_right40_1 x0 ->
            intelements_9 T131 x0 = intelements_10 T131 x0.
Hypothesis hyp4 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_right40_1.
Hypothesis hyp5 : f_tab this <> null.
Hypothesis hyp6 : l_left40_1 < l_right40_1.
Hypothesis hyp7 : l_left40_1 < l_right40_1.
Hypothesis hyp8 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_left40_1.
Hypothesis hyp9 : forall x1 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x1 ->
            intelements_10 x1 = intelements_19 x1.
Hypothesis hyp10 : forall T132 : REFERENCES,
             singleton REFERENCES (f_tab this) T132 ->
             forall x2 : t_int,
             ~ singleton t_int l_left40_1 x2 ->
             intelements_10 T132 x2 = intelements_19 T132 x2.
Hypothesis hyp11 : intelements_9 (f_tab this) l_left40_1 =
             intelements_19 (f_tab this) l_right40_1 /\
             intelements_9 (f_tab this) l_right40_1 =
             intelements_19 (f_tab this) l_left40_1.
Hypothesis hyp12 : forall x3 : REFERENCES,
             ~ singleton REFERENCES (f_tab this) x3 ->
             intelements_19 x3 = intelements x3.
Hypothesis hyp13 : forall T213 : REFERENCES,
             singleton REFERENCES (f_tab this) T213 ->
             forall x4 : t_int,
             ~ interval l_lo (j_sub l_hi 1) x4 ->
             intelements_19 T213 x4 = intelements T213 x4.
Hypothesis hyp14 : l_left40_1 < l_right40_2.
Hypothesis hyp15 : l_left40_1 < l_right40_1 -> l_right40_1 < l_right40_2.
Hypothesis hyp16 : l_left40_2 <= l_left40_1.
Hypothesis hyp17 : l_left40_2 < l_right40_2.
Hypothesis hyp18 : f_tab this <> null.
Hypothesis hyp19 : ~
             intelements (f_tab this) l_hi <=
             intelements_19 (f_tab this) l_right40_1.
Hypothesis hyp20 : (forall l_k75 : t_int,
              l_lo <= l_k75 /\ l_k75 < l_left40_1 ->
              intelements_19 (f_tab this) l_k75 <=
              intelements (f_tab this) l_hi) /\
             (forall l_k76 : t_int,
              l_right40_1 < l_k76 /\ l_k76 <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_19 (f_tab this) l_k76).
Hypothesis hyp21 : ~
             intelements_19 (f_tab this) l_left40_1 <=
             intelements (f_tab this) l_hi.
Hypothesis hyp22 : (((l_left40_1 <= l_right40_1 /\ l_right40_1 <= l_right40_2) /\
               l_right40_1 <= l_hi) /\
              (forall l_k69 : t_int,
               l_lo <= l_k69 /\ l_k69 < l_left40_1 ->
               intelements_19 (f_tab this) l_k69 <=
               intelements (f_tab this) l_hi)) /\
             (forall l_k70 : t_int,
              l_right40_1 < l_k70 /\ l_k70 <= l_hi ->
              intelements (f_tab this) l_hi <=
              intelements_19 (f_tab this) l_k70).
Hypothesis hyp23 : ((l_lo <= l_left40_1 /\ l_left40_2 <= l_left40_1) /\
              l_left40_1 <= l_right40_2) /\
             (forall l_k62 : t_int,
              l_lo <= l_k62 /\ l_k62 < l_left40_1 ->
              intelements_19 (f_tab this) l_k62 <=
              intelements (f_tab this) l_hi).
Hypothesis hyp24 : (((((l_lo <= l_left40_2 /\ l_left40_2 <= l_right40_2) /\
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
Hypothesis hyp25 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp26 : ~ ~ l_lo < l_hi.
Hypothesis hyp27 : instances this.
Hypothesis hyp28 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_i51 : t_int,
   l_lo <= l_i51 /\ l_i51 <= l_hi - 1 ->
   exists l_j51 : t_int,
     (l_lo <= l_j51 /\ l_j51 <= l_hi) /\
     intelements (f_tab this) l_j51 = intelements_9 (f_tab this) l_i51.
Proof with autoJ.
(* Write your proof here *)
intros l_i45.
startJack.
destruct (classic (l_i45 = l_right40_1)).
subst.
rewrite H22.
elim (H4 l_left40_1); [intros x [[h1 h2] h3] | split; j_omega].
rewrite <- h3.
exists x; repeat split; j_omega.
destruct (classic (l_i45 = l_left40_1 )).
subst.
rewrite H21.
destrJlt ( l_right40_1 <=  l_hi ).
elim (H4 l_right40_1); [intros x [[h1 h2] h3] | split; j_omega].
rewrite <- h3.
exists x...
subst.
rewrite hyp13; trivial; [exists l_hi | unfold not; intros; subst; j_omega].
repeat split; j_omega; trivial.
rewrite hyp3...
rewrite hyp10...





Qed.
End JackProof.
