Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_3 : REFERENCES -> t_int -> t_int.
Variable intelements_4 : REFERENCES -> t_int -> t_int.
Variable intelements_5 : REFERENCES -> t_int -> t_int.
Variable intelements_6 : REFERENCES -> t_int -> t_int.
Variable intelements_18 : REFERENCES -> t_int -> t_int.
Variable l_right34_3 : t_int.
Variable l_left34_3 : t_int.
Variable this : REFERENCES.
Variable l_lo : t_int.
Variable l_hi : t_int.
Hypothesis req1 : (((0 <= l_lo /\ l_lo < arraylength (f_tab this)) /\ 0 <= l_hi) /\
             l_hi < arraylength (f_tab this)) /\ true = true.
Hypothesis hyp1 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_3 x0 = intelements_4 x0.
Hypothesis hyp2 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_4 x0 = intelements_5 x0.
Hypothesis hyp3 : forall x1 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x1 ->
            intelements_5 x1 = intelements_6 x1.
Hypothesis hyp4 : forall T98 : REFERENCES,
            singleton REFERENCES (f_tab this) T98 ->
            forall x2 : t_int,
            ~ singleton t_int l_hi x2 ->
            intelements_5 T98 x2 = intelements_6 T98 x2.
Hypothesis hyp5 : forall x3 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x3 ->
            intelements_6 x3 = intelements_18 x3.
Hypothesis hyp6 : forall x4 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x4 ->
            intelements_18 x4 = intelements x4.
Hypothesis hyp7 : forall T173 : REFERENCES,
            singleton REFERENCES (f_tab this) T173 ->
            forall x5 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x5 ->
            intelements_18 T173 x5 = intelements T173 x5.
Hypothesis hyp8 : forall T80 : REFERENCES,
            singleton REFERENCES (f_tab this) T80 ->
            forall x6 : t_int,
            ~ interval (j_add l_left34_3 1) l_hi x6 ->
            intelements_3 T80 x6 = intelements_4 T80 x6.
Hypothesis hyp9 : (forall l_i0 : t_int,
             t_int ->
             forall l_j30 : t_int,
             l_left34_3 + 1 <= l_i0 /\ l_i0 <= l_hi ->
             l_left34_3 + 1 <= l_j30 /\ l_j30 <= l_hi ->
             l_i0 < l_j30 ->
             intelements_3 (f_tab this) l_i0 <=
             intelements_3 (f_tab this) l_j30) /\
            (forall l_i31 : t_int,
             l_left34_3 + 1 <= l_i31 /\ l_i31 <= l_hi ->
             exists l_j31 : t_int,
               (l_left34_3 + 1 <= l_j31 /\ l_j31 <= l_hi) /\
               intelements_4 (f_tab this) l_j31 =
               intelements_3 (f_tab this) l_i31).
Hypothesis hyp10 : (((forall l_i0 : t_int,
                t_int ->
                forall l_j87 : t_int,
                l_lo <= l_i0 /\ l_i0 < l_left34_3 ->
                l_lo <= l_j87 /\ l_j87 < l_left34_3 ->
                l_i0 < l_j87 ->
                intelements_4 (f_tab this) l_i0 <=
                intelements_4 (f_tab this) l_j87) /\
               (forall l_i88 : t_int,
                l_lo <= l_i88 /\ l_i88 < l_left34_3 ->
                intelements_4 (f_tab this) l_i88 <=
                intelements_4 (f_tab this) l_left34_3)) /\
              (forall l_j90 : t_int,
               l_left34_3 < l_j90 /\ l_j90 <= l_hi ->
               intelements_4 (f_tab this) l_left34_3 <=
               intelements_4 (f_tab this) l_j90)) /\
             (forall l_i92 : t_int,
              l_lo <= l_i92 /\ l_i92 <= l_hi ->
              exists l_j92 : t_int,
                (l_lo <= l_j92 /\ l_j92 <= l_hi) /\
                intelements (f_tab this) l_j92 =
                intelements_4 (f_tab this) l_i92).
Hypothesis hyp11 : forall T89 : REFERENCES,
             singleton REFERENCES (f_tab this) T89 ->
             forall x7 : t_int,
             ~ interval l_lo (j_sub l_left34_3 1) x7 ->
             intelements_4 T89 x7 = intelements_5 T89 x7.
Hypothesis hyp12 : (forall l_i0 : t_int,
              t_int ->
              forall l_j30 : t_int,
              l_lo <= l_i0 /\ l_i0 <= l_left34_3 - 1 ->
              l_lo <= l_j30 /\ l_j30 <= l_left34_3 - 1 ->
              l_i0 < l_j30 ->
              intelements_4 (f_tab this) l_i0 <=
              intelements_4 (f_tab this) l_j30) /\
             (forall l_i31 : t_int,
              l_lo <= l_i31 /\ l_i31 <= l_left34_3 - 1 ->
              exists l_j31 : t_int,
                (l_lo <= l_j31 /\ l_j31 <= l_left34_3 - 1) /\
                intelements_5 (f_tab this) l_j31 =
                intelements_4 (f_tab this) l_i31).
Hypothesis hyp13 : ((forall l_i0 : t_int,
               t_int ->
               t_int ->
               l_lo <= l_i0 /\ l_i0 < l_left34_3 ->
               intelements_5 (f_tab this) l_i0 <=
               intelements_5 (f_tab this) l_left34_3) /\
              (forall l_j80 : t_int,
               l_left34_3 < l_j80 /\ l_j80 <= l_hi ->
               intelements_5 (f_tab this) l_left34_3 <=
               intelements_5 (f_tab this) l_j80)) /\
             (forall l_i82 : t_int,
              l_lo <= l_i82 /\ l_i82 <= l_hi ->
              exists l_j82 : t_int,
                (l_lo <= l_j82 /\ l_j82 <= l_hi) /\
                intelements (f_tab this) l_j82 =
                intelements_5 (f_tab this) l_i82).
Hypothesis hyp14 : forall T99 : REFERENCES,
             singleton REFERENCES (f_tab this) T99 ->
             forall x8 : t_int,
             ~ singleton t_int l_left34_3 x8 ->
             intelements_6 T99 x8 = intelements_18 T99 x8.
Hypothesis hyp15 : intelements_5 (f_tab this) l_left34_3 =
             intelements_18 (f_tab this) l_hi /\
             intelements_5 (f_tab this) l_hi =
             intelements_18 (f_tab this) l_left34_3.
Hypothesis hyp16 : ~ l_left34_3 < l_right34_3.
Hypothesis hyp17 : f_tab this <> null.
Hypothesis hyp18 : ((forall l_i0 : t_int,
               t_int ->
               t_int ->
               l_lo <= l_i0 /\ l_i0 < l_left34_3 ->
               intelements_18 (f_tab this) l_i0 <=
               intelements (f_tab this) l_hi) /\
              (forall l_j72 : t_int,
               l_left34_3 < l_j72 /\ l_j72 <= l_hi ->
               intelements (f_tab this) l_hi <=
               intelements_18 (f_tab this) l_j72)) /\
             (forall l_i74 : t_int,
              l_lo <= l_i74 /\ l_i74 <= l_hi ->
              exists l_j74 : t_int,
                (l_lo <= l_j74 /\ l_j74 <= l_hi) /\
                intelements (f_tab this) l_j74 =
                intelements_18 (f_tab this) l_i74).
Hypothesis hyp19 : ((((l_lo <= l_left34_3 /\ l_left34_3 <= l_right34_3) /\
                l_right34_3 <= l_hi) /\
               (forall l_m : t_int,
                l_lo <= l_m /\ l_m < l_left34_3 ->
                intelements_18 (f_tab this) l_m <=
                intelements (f_tab this) l_hi)) /\
              (forall l_n : t_int,
               l_right34_3 < l_n /\ l_n <= l_hi ->
               intelements (f_tab this) l_hi <=
               intelements_18 (f_tab this) l_n)) /\
             (forall l_i44 : t_int,
              l_left34_3 <= l_i44 /\ l_i44 <= l_right34_3 - 1 ->
              exists l_j44 : t_int,
                (l_lo <= l_j44 /\ l_j44 <= l_hi) /\
                intelements (f_tab this) l_j44 =
                intelements_18 (f_tab this) l_i44).
Hypothesis hyp20 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp21 : ~ ~ l_lo < l_hi.
Hypothesis hyp22 : instances this.
Hypothesis hyp23 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_i97 : t_int,
   l_lo <= l_i97 /\ l_i97 <= l_hi ->
   exists l_j97 : t_int,
     (l_lo <= l_j97 /\ l_j97 <= l_hi) /\
     intelements (f_tab this) l_j97 = intelements_3 (f_tab this) l_i97.
Proof with autoJ.
(* Write your proof here *)
intros.
assert(h :forall l_i31 : t_int,
        l_lo <= l_i31 /\ l_i31 <= l_hi ->
        exists l_j31 : t_int,
          (l_lo <= l_j31 /\ l_j31 <= l_hi) /\
          intelements_4 (f_tab this) l_j31 = intelements_3 (f_tab this) l_i31).
intros.

case (classic (l_left34_3 + 1 <= l_i31 )).
intros. 
destruct hyp9.
assert (h: exists l_j31 : t_int,
         (l_left34_3 + 1 <= l_j31 /\ l_j31 <= l_hi) /\
         intelements_4 (f_tab this) l_j31 = intelements_3 (f_tab this) l_i31).
apply H3; split; j_omega.
elim h.
intros.
exists x.
elimAnd...
solveInc.
j_omega.
(* case not (l_left34_3 + 1 <= l_i31 )*)
intros.
solveInc.
startJack.
assert(h := hyp8 _ (refl_equal (f_tab this)) l_i31).
exists l_i31.
split...
rewrite h...
unfold not; intros; j_omega.


assert(h1 := h _ H).
elim h1.
intros.

destruct H0.


rewrite <- H1.

destruct hyp10.
apply H3...


Qed.
End JackProof.
