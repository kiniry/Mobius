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
Hypothesis hyp1 : f_tab this <> null.
Hypothesis hyp2 : (forall l_i0 : t_int,
             t_int ->
             forall l_j111 : t_int,
             l_lo <= l_i0 /\ l_i0 <= l_hi ->
             l_lo <= l_j111 /\ l_j111 <= l_hi ->
             l_i0 < l_j111 ->
             intelements_7 (f_tab this) l_i0 <=
             intelements_7 (f_tab this) l_j111) /\
            (forall l_i112 : t_int,
             l_lo <= l_i112 /\ l_i112 <= l_hi ->
             exists l_j112 : t_int,
               (l_lo <= l_j112 /\ l_j112 <= l_hi) /\
               intelements (f_tab this) l_j112 =
               intelements_7 (f_tab this) l_i112).
Hypothesis hyp3 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_7 x0 = intelements_8 x0.
Hypothesis hyp4 : forall T121 : REFERENCES,
            singleton REFERENCES (f_tab this) T121 ->
            forall x0 : t_int,
            ~ singleton t_int l_hi x0 ->
            intelements_7 T121 x0 = intelements_8 T121 x0.
Hypothesis hyp5 : forall x1 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x1 ->
            intelements_8 x1 = intelements_20 x1.
Hypothesis hyp6 : forall x2 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x2 ->
            intelements_20 x2 = intelements x2.
Hypothesis hyp7 : forall T216 : REFERENCES,
            singleton REFERENCES (f_tab this) T216 ->
            forall x3 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x3 ->
            intelements_20 T216 x3 = intelements T216 x3.
Hypothesis hyp8 : ~ l_left40_3 + 1 < arraylength (f_tab this).
Hypothesis hyp9 : ~ 0 < l_left40_3.
Hypothesis hyp10 : (((forall l_i0 : t_int,
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
Hypothesis hyp11 : ((forall l_i0 : t_int,
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
Hypothesis hyp12 : forall T122 : REFERENCES,
             singleton REFERENCES (f_tab this) T122 ->
             forall x4 : t_int,
             ~ singleton t_int l_left40_3 x4 ->
             intelements_8 T122 x4 = intelements_20 T122 x4.
Hypothesis hyp13 : intelements_7 (f_tab this) l_left40_3 =
             intelements_20 (f_tab this) l_hi /\
             intelements_7 (f_tab this) l_hi =
             intelements_20 (f_tab this) l_left40_3.
Hypothesis hyp14 : ~ l_left40_3 < l_right40_3.
Hypothesis hyp15 : f_tab this <> null.
Hypothesis hyp16 : ((forall l_i0 : t_int,
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
Hypothesis hyp17 : (((((l_lo <= l_left40_3 /\ l_left40_3 <= l_right40_3) /\
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
Hypothesis hyp18 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp19 : ~ ~ l_lo < l_hi.
Hypothesis hyp20 : instances this.
Hypothesis hyp21 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall x25 : REFERENCES,
   ~ singleton REFERENCES (f_tab this) x25 ->
   forall x26 : t_int,
   instances x25 -> intelements_7 x25 x26 = intelements x25 x26.
Proof with autoJ.
(* Write your proof here *)
startJack.
rewrite hyp3...
rewrite hyp5...
rewrite hyp6...









Qed.
End JackProof.
