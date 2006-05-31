Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_5 : REFERENCES -> t_int -> t_int.
Variable intelements_6 : REFERENCES -> t_int -> t_int.
Variable intelements_7 : REFERENCES -> t_int -> t_int.
Variable intelements_19 : REFERENCES -> t_int -> t_int.
Variable l_right34_3 : t_int.
Variable l_left34_3 : t_int.
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
            intelements_5 x0 = intelements_6 x0.
Hypothesis hyp3 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_6 x0 = intelements_7 x0.
Hypothesis hyp4 : forall T109 : REFERENCES,
            singleton REFERENCES (f_tab this) T109 ->
            forall x1 : t_int,
            ~ singleton t_int l_hi x1 ->
            intelements_6 T109 x1 = intelements_7 T109 x1.
Hypothesis hyp5 : forall x2 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x2 ->
            intelements_7 x2 = intelements_19 x2.
Hypothesis hyp6 : forall x3 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x3 ->
            intelements_19 x3 = intelements x3.
Hypothesis hyp7 : forall T184 : REFERENCES,
            singleton REFERENCES (f_tab this) T184 ->
            forall x4 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x4 ->
            intelements_19 T184 x4 = intelements T184 x4.
Hypothesis hyp8 : ~ l_left34_3 + 1 < arraylength (f_tab this).
Hypothesis hyp9 : (((forall l_i0 : t_int,
               t_int ->
               forall l_j87 : t_int,
               l_lo <= l_i0 /\ l_i0 < l_left34_3 ->
               l_lo <= l_j87 /\ l_j87 < l_left34_3 ->
               l_i0 < l_j87 ->
               intelements_5 (f_tab this) l_i0 <=
               intelements_5 (f_tab this) l_j87) /\
              (forall l_i88 : t_int,
               l_lo <= l_i88 /\ l_i88 < l_left34_3 ->
               intelements_5 (f_tab this) l_i88 <=
               intelements_5 (f_tab this) l_left34_3)) /\
             (forall l_j90 : t_int,
              l_left34_3 < l_j90 /\ l_j90 <= l_hi ->
              intelements_5 (f_tab this) l_left34_3 <=
              intelements_5 (f_tab this) l_j90)) /\
            (forall l_i92 : t_int,
             l_lo <= l_i92 /\ l_i92 <= l_hi ->
             exists l_j92 : t_int,
               (l_lo <= l_j92 /\ l_j92 <= l_hi) /\
               intelements (f_tab this) l_j92 =
               intelements_5 (f_tab this) l_i92).
Hypothesis hyp10 : forall T100 : REFERENCES,
             singleton REFERENCES (f_tab this) T100 ->
             forall x5 : t_int,
             ~ interval l_lo (j_sub l_left34_3 1) x5 ->
             intelements_5 T100 x5 = intelements_6 T100 x5.
Hypothesis hyp11 : (forall l_i0 : t_int,
              t_int ->
              forall l_j30 : t_int,
              l_lo <= l_i0 /\ l_i0 <= l_left34_3 - 1 ->
              l_lo <= l_j30 /\ l_j30 <= l_left34_3 - 1 ->
              l_i0 < l_j30 ->
              intelements_5 (f_tab this) l_i0 <=
              intelements_5 (f_tab this) l_j30) /\
             (forall l_i31 : t_int,
              l_lo <= l_i31 /\ l_i31 <= l_left34_3 - 1 ->
              exists l_j31 : t_int,
                (l_lo <= l_j31 /\ l_j31 <= l_left34_3 - 1) /\
                intelements_6 (f_tab this) l_j31 =
                intelements_5 (f_tab this) l_i31).
Hypothesis hyp12 : ((forall l_i0 : t_int,
               t_int ->
               t_int ->
               l_lo <= l_i0 /\ l_i0 < l_left34_3 ->
               intelements_6 (f_tab this) l_i0 <=
               intelements_6 (f_tab this) l_left34_3) /\
              (forall l_j80 : t_int,
               l_left34_3 < l_j80 /\ l_j80 <= l_hi ->
               intelements_6 (f_tab this) l_left34_3 <=
               intelements_6 (f_tab this) l_j80)) /\
             (forall l_i82 : t_int,
              l_lo <= l_i82 /\ l_i82 <= l_hi ->
              exists l_j82 : t_int,
                (l_lo <= l_j82 /\ l_j82 <= l_hi) /\
                intelements (f_tab this) l_j82 =
                intelements_6 (f_tab this) l_i82).
Hypothesis hyp13 : forall T110 : REFERENCES,
             singleton REFERENCES (f_tab this) T110 ->
             forall x6 : t_int,
             ~ singleton t_int l_left34_3 x6 ->
             intelements_7 T110 x6 = intelements_19 T110 x6.
Hypothesis hyp14 : intelements_6 (f_tab this) l_left34_3 =
             intelements_19 (f_tab this) l_hi /\
             intelements_6 (f_tab this) l_hi =
             intelements_19 (f_tab this) l_left34_3.
Hypothesis hyp15 : ~ l_left34_3 < l_right34_3.
Hypothesis hyp16 : f_tab this <> null.
Hypothesis hyp17 : ((forall l_i0 : t_int,
               t_int ->
               t_int ->
               l_lo <= l_i0 /\ l_i0 < l_left34_3 ->
               intelements_19 (f_tab this) l_i0 <=
               intelements (f_tab this) l_hi) /\
              (forall l_j72 : t_int,
               l_left34_3 < l_j72 /\ l_j72 <= l_hi ->
               intelements (f_tab this) l_hi <=
               intelements_19 (f_tab this) l_j72)) /\
             (forall l_i74 : t_int,
              l_lo <= l_i74 /\ l_i74 <= l_hi ->
              exists l_j74 : t_int,
                (l_lo <= l_j74 /\ l_j74 <= l_hi) /\
                intelements (f_tab this) l_j74 =
                intelements_19 (f_tab this) l_i74).
Hypothesis hyp18 : ((((l_lo <= l_left34_3 /\ l_left34_3 <= l_right34_3) /\
                l_right34_3 <= l_hi) /\
               (forall l_m : t_int,
                l_lo <= l_m /\ l_m < l_left34_3 ->
                intelements_19 (f_tab this) l_m <=
                intelements (f_tab this) l_hi)) /\
              (forall l_n : t_int,
               l_right34_3 < l_n /\ l_n <= l_hi ->
               intelements (f_tab this) l_hi <=
               intelements_19 (f_tab this) l_n)) /\
             (forall l_i44 : t_int,
              l_lo <= l_i44 /\ l_i44 <= l_hi - 1 ->
              exists l_j44 : t_int,
                (l_lo <= l_j44 /\ l_j44 <= l_hi) /\
                intelements (f_tab this) l_j44 =
                intelements_19 (f_tab this) l_i44).
Hypothesis hyp19 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp20 : ~ ~ l_lo < l_hi.
Hypothesis hyp21 : instances this.
Hypothesis hyp22 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_i0 : t_int,
   t_int ->
   forall l_j97 : t_int,
   l_lo <= l_i0 /\ l_i0 <= l_hi ->
   l_lo <= l_j97 /\ l_j97 <= l_hi ->
   l_i0 < l_j97 ->
   intelements_5 (f_tab this) l_i0 <= intelements_5 (f_tab this) l_j97.
Proof with autoJ.
(* Write your proof here *)
startJack.
case (classic (l_left34_3 + 1 <= l_i0 /\ l_i0 <= l_hi));
case (classic (l_left34_3 + 1 <= l_j97 /\ l_j97 <= l_hi)).
intros; apply H23...
split; j_omega.
split; j_omega.
intros h1 h2.
destruct h1...
j_omega.
intros h1 h2.
assert(h3 := hyp10 _ (refl_equal (f_tab this)) _ h2).
rewrite h3.
clear h3.
assert(h4 : (intelements_4 (f_tab this) l_i0 <=
       intelements_4 (f_tab this) l_left34_3)).
destrJlt (l_i0 <= l_left34_3).
subst; j_omega.
assert(intelements_4 (f_tab this) l_left34_3 <=
        intelements_3 (f_tab this) l_j95).
assert(h5 := H25 _ h1).
elim h5.
intros.
destruct H.
rewrite <- H27.
apply H22...
destruct H; split; j_omega.
j_omega.
intros h1 h2.
assert(h3 := hyp8 _ (refl_equal (f_tab this)) _ h1).
assert(h4 := hyp8 _ (refl_equal (f_tab this)) _ h2).
rewrite h3.
rewrite h4.
destrJlt (l_j95 <= l_left34_3).
apply H20...
split; j_omega.
subst.
apply H23...





Qed.
End JackProof.
