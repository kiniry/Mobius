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
Variable l_right39_3 : t_int.
Variable l_left39_3 : t_int.
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
             forall l_j110 : t_int,
             l_lo <= l_i0 /\ l_i0 <= l_hi ->
             l_lo <= l_j110 /\ l_j110 <= l_hi ->
             l_i0 < l_j110 ->
             intelements_6 (f_tab this) l_i0 <=
             intelements_6 (f_tab this) l_j110) /\
            (forall l_i111 : t_int,
             l_lo <= l_i111 /\ l_i111 <= l_hi ->
             exists l_j111 : t_int,
               (l_lo <= l_j111 /\ l_j111 <= l_hi) /\
               intelements (f_tab this) l_j111 =
               intelements_6 (f_tab this) l_i111).
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
Hypothesis hyp7 : forall T207 : REFERENCES,
            singleton REFERENCES (f_tab this) T207 ->
            forall x3 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x3 ->
            intelements_19 T207 x3 = intelements T207 x3.
Hypothesis hyp8 : ~ l_left39_3 + 1 < arraylength (f_tab this).
Hypothesis hyp9 : ~ 0 < l_left39_3.
Hypothesis hyp10 : (((forall l_i0 : t_int,
                t_int ->
                forall l_j100 : t_int,
                l_lo <= l_i0 /\ l_i0 < l_left39_3 ->
                l_lo <= l_j100 /\ l_j100 < l_left39_3 ->
                l_i0 < l_j100 ->
                intelements_6 (f_tab this) l_i0 <=
                intelements_6 (f_tab this) l_j100) /\
               (forall l_i101 : t_int,
                l_lo <= l_i101 /\ l_i101 < l_left39_3 ->
                intelements_6 (f_tab this) l_i101 <=
                intelements_6 (f_tab this) l_left39_3)) /\
              (forall l_j103 : t_int,
               l_left39_3 < l_j103 /\ l_j103 <= l_hi ->
               intelements_6 (f_tab this) l_left39_3 <=
               intelements_6 (f_tab this) l_j103)) /\
             (forall l_i105 : t_int,
              l_lo <= l_i105 /\ l_i105 <= l_hi ->
              exists l_j105 : t_int,
                (l_lo <= l_j105 /\ l_j105 <= l_hi) /\
                intelements (f_tab this) l_j105 =
                intelements_6 (f_tab this) l_i105).
Hypothesis hyp11 : ((forall l_i0 : t_int,
               t_int ->
               t_int ->
               l_lo <= l_i0 /\ l_i0 < l_left39_3 ->
               intelements_6 (f_tab this) l_i0 <=
               intelements_6 (f_tab this) l_left39_3) /\
              (forall l_j92 : t_int,
               l_left39_3 < l_j92 /\ l_j92 <= l_hi ->
               intelements_6 (f_tab this) l_left39_3 <=
               intelements_6 (f_tab this) l_j92)) /\
             (forall l_i94 : t_int,
              l_lo <= l_i94 /\ l_i94 <= l_hi ->
              exists l_j94 : t_int,
                (l_lo <= l_j94 /\ l_j94 <= l_hi) /\
                intelements (f_tab this) l_j94 =
                intelements_6 (f_tab this) l_i94).
Hypothesis hyp12 : forall T113 : REFERENCES,
             singleton REFERENCES (f_tab this) T113 ->
             forall x4 : t_int,
             ~ singleton t_int l_left39_3 x4 ->
             intelements_7 T113 x4 = intelements_19 T113 x4.
Hypothesis hyp13 : intelements_6 (f_tab this) l_left39_3 =
             intelements_19 (f_tab this) l_hi /\
             intelements_6 (f_tab this) l_hi =
             intelements_19 (f_tab this) l_left39_3.
Hypothesis hyp14 : ~ l_left39_3 < l_right39_3.
Hypothesis hyp15 : f_tab this <> null.
Hypothesis hyp16 : ((forall l_i0 : t_int,
               t_int ->
               t_int ->
               l_lo <= l_i0 /\ l_i0 < l_left39_3 ->
               intelements_19 (f_tab this) l_i0 <=
               intelements (f_tab this) l_hi) /\
              (forall l_j84 : t_int,
               l_left39_3 < l_j84 /\ l_j84 <= l_hi ->
               intelements (f_tab this) l_hi <=
               intelements_19 (f_tab this) l_j84)) /\
             (forall l_i86 : t_int,
              l_lo <= l_i86 /\ l_i86 <= l_hi ->
              exists l_j86 : t_int,
                (l_lo <= l_j86 /\ l_j86 <= l_hi) /\
                intelements (f_tab this) l_j86 =
                intelements_19 (f_tab this) l_i86).
Hypothesis hyp17 : (((((l_lo <= l_left39_3 /\ l_left39_3 <= l_right39_3) /\
                 l_right39_3 <= l_hi) /\
                (forall l_m : t_int,
                 l_lo <= l_m /\ l_m < l_left39_3 ->
                 intelements_19 (f_tab this) l_m <=
                 intelements (f_tab this) l_hi)) /\
               (forall l_n : t_int,
                l_right39_3 < l_n /\ l_n <= l_hi ->
                intelements (f_tab this) l_hi <=
                intelements_19 (f_tab this) l_n)) /\
              intelements (f_tab this) l_hi <=
              intelements_19 (f_tab this) l_right39_3) /\
             (forall l_i50 : t_int,
              l_lo <= l_i50 /\ l_i50 <= l_hi - 1 ->
              exists l_j50 : t_int,
                (l_lo <= l_j50 /\ l_j50 <= l_hi) /\
                intelements (f_tab this) l_j50 =
                intelements_19 (f_tab this) l_i50).
Hypothesis hyp18 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp19 : ~ ~ l_lo < l_hi.
Hypothesis hyp20 : instances this.
Hypothesis hyp21 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall l_i0 : t_int,
   t_int ->
   forall l_j35 : t_int,
   l_lo <= l_i0 /\ l_i0 <= l_hi ->
   l_lo <= l_j35 /\ l_j35 <= l_hi ->
   l_i0 < l_j35 ->
   intelements_6 (f_tab this) l_i0 <= intelements_6 (f_tab this) l_j35.
Proof with autoJ.
(* Write your proof here *)
startJack.
apply H22...
split...
j_omega.
split; j_omega.




Qed.
End JackProof.
