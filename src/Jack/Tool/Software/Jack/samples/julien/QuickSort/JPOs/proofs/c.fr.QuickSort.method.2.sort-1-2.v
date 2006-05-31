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
Hypothesis hyp2 : (forall l_i0 : t_int,
             t_int ->
             forall l_j98 : t_int,
             l_lo <= l_i0 /\ l_i0 <= l_hi ->
             l_lo <= l_j98 /\ l_j98 <= l_hi ->
             l_i0 < l_j98 ->
             intelements_6 (f_tab this) l_i0 <=
             intelements_6 (f_tab this) l_j98) /\
            (forall l_i99 : t_int,
             l_lo <= l_i99 /\ l_i99 <= l_hi ->
             exists l_j99 : t_int,
               (l_lo <= l_j99 /\ l_j99 <= l_hi) /\
               intelements (f_tab this) l_j99 =
               intelements_6 (f_tab this) l_i99).
Hypothesis hyp3 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_6 x0 = intelements_7 x0.
Hypothesis hyp4 : forall T112 : REFERENCES,
            singleton REFERENCES (f_tab this) T112 ->
            forall x0 : t_int,
            ~ singleton t_int l_hi x0 ->
            intelements_6 T112 x0 = intelements_7 T112 x0.
Hypothesis hyp5 : forall x1 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x1 ->
            intelements_7 x1 = intelements_19 x1.
Hypothesis hyp6 : forall x2 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x2 ->
            intelements_19 x2 = intelements x2.
Hypothesis hyp7 : forall T187 : REFERENCES,
            singleton REFERENCES (f_tab this) T187 ->
            forall x3 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x3 ->
            intelements_19 T187 x3 = intelements T187 x3.
Hypothesis hyp8 : ~ l_left34_3 + 1 < arraylength (f_tab this).
Hypothesis hyp9 : ~ 0 < l_left34_3.
Hypothesis hyp10 : (((forall l_i0 : t_int,
                t_int ->
                forall l_j88 : t_int,
                l_lo <= l_i0 /\ l_i0 < l_left34_3 ->
                l_lo <= l_j88 /\ l_j88 < l_left34_3 ->
                l_i0 < l_j88 ->
                intelements_6 (f_tab this) l_i0 <=
                intelements_6 (f_tab this) l_j88) /\
               (forall l_i89 : t_int,
                l_lo <= l_i89 /\ l_i89 < l_left34_3 ->
                intelements_6 (f_tab this) l_i89 <=
                intelements_6 (f_tab this) l_left34_3)) /\
              (forall l_j91 : t_int,
               l_left34_3 < l_j91 /\ l_j91 <= l_hi ->
               intelements_6 (f_tab this) l_left34_3 <=
               intelements_6 (f_tab this) l_j91)) /\
             (forall l_i93 : t_int,
              l_lo <= l_i93 /\ l_i93 <= l_hi ->
              exists l_j93 : t_int,
                (l_lo <= l_j93 /\ l_j93 <= l_hi) /\
                intelements (f_tab this) l_j93 =
                intelements_6 (f_tab this) l_i93).
Hypothesis hyp11 : ((forall l_i0 : t_int,
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
Hypothesis hyp12 : forall T113 : REFERENCES,
             singleton REFERENCES (f_tab this) T113 ->
             forall x4 : t_int,
             ~ singleton t_int l_left34_3 x4 ->
             intelements_7 T113 x4 = intelements_19 T113 x4.
Hypothesis hyp13 : intelements_6 (f_tab this) l_left34_3 =
             intelements_19 (f_tab this) l_hi /\
             intelements_6 (f_tab this) l_hi =
             intelements_19 (f_tab this) l_left34_3.
Hypothesis hyp14 : ~ l_left34_3 < l_right34_3.
Hypothesis hyp15 : f_tab this <> null.
Hypothesis hyp16 : ((forall l_i0 : t_int,
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
Hypothesis hyp17 : ((((l_lo <= l_left34_3 /\ l_left34_3 <= l_right34_3) /\
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
Hypothesis hyp18 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp19 : ~ ~ l_lo < l_hi.
Hypothesis hyp20 : instances this.
Hypothesis hyp21 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_i31 : t_int,
   l_lo <= l_i31 /\ l_i31 <= l_hi ->
   exists l_j31 : t_int,
     (l_lo <= l_j31 /\ l_j31 <= l_hi) /\
     intelements (f_tab this) l_j31 = intelements_6 (f_tab this) l_i31.
Proof with autoJ.
(* Write your proof here *)
startJack.
apply H23...


Qed.
End JackProof.
