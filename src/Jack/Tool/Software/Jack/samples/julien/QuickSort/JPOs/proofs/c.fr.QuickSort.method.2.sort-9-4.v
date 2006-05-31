Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_4 : REFERENCES -> t_int -> t_int.
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
Hypothesis hyp1 : (forall l_i0 : t_int,
             t_int ->
             forall l_j111 : t_int,
             l_lo <= l_i0 /\ l_i0 <= l_hi ->
             l_lo <= l_j111 /\ l_j111 <= l_hi ->
             l_i0 < l_j111 ->
             intelements_4 (f_tab this) l_i0 <=
             intelements_4 (f_tab this) l_j111) /\
            (forall l_i112 : t_int,
             l_lo <= l_i112 /\ l_i112 <= l_hi ->
             exists l_j112 : t_int,
               (l_lo <= l_j112 /\ l_j112 <= l_hi) /\
               intelements (f_tab this) l_j112 =
               intelements_4 (f_tab this) l_i112).
Hypothesis hyp2 : f_tab this <> null.
Hypothesis hyp3 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_4 x0 = intelements_6 x0.
Hypothesis hyp4 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_6 x0 = intelements_7 x0.
Hypothesis hyp5 : forall x1 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x1 ->
            intelements_7 x1 = intelements_8 x1.
Hypothesis hyp6 : forall T121 : REFERENCES,
            singleton REFERENCES (f_tab this) T121 ->
            forall x2 : t_int,
            ~ singleton t_int l_hi x2 ->
            intelements_7 T121 x2 = intelements_8 T121 x2.
Hypothesis hyp7 : forall x3 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x3 ->
            intelements_8 x3 = intelements_20 x3.
Hypothesis hyp8 : forall x4 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x4 ->
            intelements_20 x4 = intelements x4.
Hypothesis hyp9 : forall T216 : REFERENCES,
            singleton REFERENCES (f_tab this) T216 ->
            forall x5 : t_int,
            ~ interval l_lo (j_sub l_hi 1) x5 ->
            intelements_20 T216 x5 = intelements T216 x5.
Hypothesis hyp10 : l_left40_3 + 1 < arraylength (f_tab this).
Hypothesis hyp11 : forall T90 : REFERENCES,
             singleton REFERENCES (f_tab this) T90 ->
             forall x6 : t_int,
             ~ interval (j_add l_left40_3 1) l_hi x6 ->
             intelements_4 T90 x6 = intelements_6 T90 x6.
Hypothesis hyp12 : (forall l_i0 : t_int,
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
                intelements_6 (f_tab this) l_j37 =
                intelements_4 (f_tab this) l_i37).
Hypothesis hyp13 : (((forall l_i0 : t_int,
                t_int ->
                forall l_j101 : t_int,
                l_lo <= l_i0 /\ l_i0 < l_left40_3 ->
                l_lo <= l_j101 /\ l_j101 < l_left40_3 ->
                l_i0 < l_j101 ->
                intelements_6 (f_tab this) l_i0 <=
                intelements_6 (f_tab this) l_j101) /\
               (forall l_i102 : t_int,
                l_lo <= l_i102 /\ l_i102 < l_left40_3 ->
                intelements_6 (f_tab this) l_i102 <=
                intelements_6 (f_tab this) l_left40_3)) /\
              (forall l_j104 : t_int,
               l_left40_3 < l_j104 /\ l_j104 <= l_hi ->
               intelements_6 (f_tab this) l_left40_3 <=
               intelements_6 (f_tab this) l_j104)) /\
             (forall l_i106 : t_int,
              l_lo <= l_i106 /\ l_i106 <= l_hi ->
              exists l_j106 : t_int,
                (l_lo <= l_j106 /\ l_j106 <= l_hi) /\
                intelements (f_tab this) l_j106 =
                intelements_6 (f_tab this) l_i106).
Hypothesis hyp14 : 0 < l_left40_3.
Hypothesis hyp15 : forall T110 : REFERENCES,
             singleton REFERENCES (f_tab this) T110 ->
             forall x7 : t_int,
             ~ interval l_lo (j_sub l_left40_3 1) x7 ->
             intelements_6 T110 x7 = intelements_7 T110 x7.
Hypothesis hyp16 : (forall l_i0 : t_int,
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
Hypothesis hyp17 : ((forall l_i0 : t_int,
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
Hypothesis hyp18 : forall T122 : REFERENCES,
             singleton REFERENCES (f_tab this) T122 ->
             forall x8 : t_int,
             ~ singleton t_int l_left40_3 x8 ->
             intelements_8 T122 x8 = intelements_20 T122 x8.
Hypothesis hyp19 : intelements_7 (f_tab this) l_left40_3 =
             intelements_20 (f_tab this) l_hi /\
             intelements_7 (f_tab this) l_hi =
             intelements_20 (f_tab this) l_left40_3.
Hypothesis hyp20 : ~ l_left40_3 < l_right40_3.
Hypothesis hyp21 : f_tab this <> null.
Hypothesis hyp22 : ((forall l_i0 : t_int,
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
Hypothesis hyp23 : (((((l_lo <= l_left40_3 /\ l_left40_3 <= l_right40_3) /\
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
Hypothesis hyp24 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp25 : ~ ~ l_lo < l_hi.
Hypothesis hyp26 : instances this.
Hypothesis hyp27 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall T12 : REFERENCES,
   instances T12 ->
   (fun x : REFERENCES => instances x /\ typeof x = array (class c_int) 1)
     T12 ->
   forall x24 : t_int,
   ~
   (let x23 :=
      (fun x22 : t_int =>
       interval l_lo l_hi x22 \/ singleton REFERENCES (f_tab this) T12)
      :t_int -> Prop in
    x23 x24) -> intelements_4 T12 x24 = intelements T12 x24.
Proof with autoJ.
(* Write your proof here *)
startJack.
rewrite hyp3...
rewrite hyp4...
rewrite hyp5...
rewrite hyp7...
rewrite hyp8...







Qed.
End JackProof.
