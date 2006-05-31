Require Import Bool.
Require Import ZArith.
Require Import Classical.
Add LoadPath "/home/jcharles/sources/runtime-workspace/QuickSort/JPOs".
Require Import "fr_QuickSort_classes".
Load "user_extensions.v".
Require Import "fr_QuickSort".
Import JackLogic.
Open Scope Z_scope.
Open Scope J_Scope.

Section JackProof.

Variable intelements_7 : Reference -> t_int -> t_int.
Variable intelements_8 : Reference -> t_int -> t_int.
Variable intelements_20 : Reference -> t_int -> t_int.
Variable l_right_3 : t_int.
Variable l_left_3 : t_int.
Variable this : Reference.
Variable l_lo : t_int.
Variable l_hi : t_int.
Hypothesis req1 : f_tab this <> null.
Hypothesis req2 : 0 <= l_lo.
Hypothesis req3 : l_lo < arraylength (f_tab this).
Hypothesis req4 : 0 <= l_hi.
Hypothesis req5 : l_hi < arraylength (f_tab this).
Hypothesis hyp1 : f_tab this <> null.
Hypothesis hyp2 : forall l_i : t_int,
            t_int ->
            forall l_j4 : t_int,
            l_lo <= l_i /\ l_i <= l_hi ->
            l_lo <= l_j4 /\ l_j4 <= l_hi ->
            l_i < l_j4 ->
            intelements_7 (f_tab this) l_i <= intelements_7 (f_tab this) l_j4.
Hypothesis hyp3 : forall l_i2 : t_int,
            l_lo <= l_i2 /\ l_i2 <= l_hi ->
            exists l_j4 : t_int,
              (l_lo <= l_j4 /\ l_j4 <= l_hi) /\
              intelements (f_tab this) l_j4 = intelements_7 (f_tab this) l_i2.
Hypothesis hyp4 : forall l_i3 : t_int,
            l_lo <= l_i3 /\ l_i3 <= l_hi ->
            exists l_j5 : t_int,
              (l_lo <= l_j5 /\ l_j5 <= l_hi) /\
              intelements (f_tab this) l_j5 = intelements_7 (f_tab this) l_i3.
Hypothesis hyp5 : forall l_i4 : t_int,
            l_lo <= l_i4 /\ l_i4 <= l_hi ->
            exists l_j6 : t_int,
              (l_lo <= l_j6 /\ l_j6 <= l_hi) /\
              intelements (f_tab this) l_j6 = intelements_7 (f_tab this) l_i4.
Hypothesis hyp6 : forall x0 : Reference,
            ~ singleton Reference (f_tab this) x0 ->
            intelements_7 x0 = intelements_8 x0.
Hypothesis hyp7 : forall T121 : Reference,
            singleton Reference (f_tab this) T121 ->
            forall x0 : t_int,
            ~ singleton t_int l_hi x0 ->
            intelements_7 T121 x0 = intelements_8 T121 x0.
Hypothesis hyp8 : forall x1 : Reference,
            ~ singleton Reference (f_tab this) x1 ->
            intelements_8 x1 = intelements_20 x1.
Hypothesis hyp9 : forall l_i5 : t_int,
            l_lo <= l_i5 /\ l_i5 <= l_hi ->
            exists l_j7 : t_int,
              (l_lo <= l_j7 /\ l_j7 <= l_hi) /\
              intelements (f_tab this) l_j7 =
              intelements_20 (f_tab this) l_i5.
Hypothesis hyp10 : forall l_i6 : t_int,
             l_lo <= l_i6 /\ l_i6 <= l_hi - 1 ->
             exists l_j8 : t_int,
               (l_lo <= l_j8 /\ l_j8 <= l_hi) /\
               intelements (f_tab this) l_j8 =
               intelements_20 (f_tab this) l_i6.
Hypothesis hyp11 : forall x2 : Reference,
             ~ singleton Reference (f_tab this) x2 ->
             intelements_20 x2 = intelements x2.
Hypothesis hyp12 : forall T216 : Reference,
             singleton Reference (f_tab this) T216 ->
             forall x3 : t_int,
             ~ interval l_lo (j_sub l_hi 1) x3 ->
             intelements_20 T216 x3 = intelements T216 x3.
Hypothesis hyp13 : l_right_3 <= l_hi.
Hypothesis hyp14 : ~ l_left_3 + 1 < arraylength (f_tab this).
Hypothesis hyp15 : ~ 0 < l_left_3.
Hypothesis hyp16 : forall l_i : t_int,
             t_int ->
             forall l_j10 : t_int,
             l_lo <= l_i /\ l_i < l_left_3 ->
             l_lo <= l_j10 /\ l_j10 < l_left_3 ->
             l_i < l_j10 ->
             intelements_7 (f_tab this) l_i <=
             intelements_7 (f_tab this) l_j10.
Hypothesis hyp17 : forall l_i7 : t_int,
             l_lo <= l_i7 /\ l_i7 < l_left_3 ->
             intelements_7 (f_tab this) l_i7 <=
             intelements_7 (f_tab this) l_left_3.
Hypothesis hyp18 : forall l_j10 : t_int,
             l_left_3 < l_j10 /\ l_j10 <= l_hi ->
             intelements_7 (f_tab this) l_left_3 <=
             intelements_7 (f_tab this) l_j10.
Hypothesis hyp19 : forall l_i : t_int,
             t_int ->
             t_int ->
             l_lo <= l_i /\ l_i < l_left_3 ->
             intelements_7 (f_tab this) l_i <=
             intelements_7 (f_tab this) l_left_3.
Hypothesis hyp20 : forall l_j12 : t_int,
             l_left_3 < l_j12 /\ l_j12 <= l_hi ->
             intelements_7 (f_tab this) l_left_3 <=
             intelements_7 (f_tab this) l_j12.
Hypothesis hyp21 : l_lo <= l_left_3.
Hypothesis hyp22 : forall T122 : Reference,
             singleton Reference (f_tab this) T122 ->
             forall x4 : t_int,
             ~ singleton t_int l_left_3 x4 ->
             intelements_8 T122 x4 = intelements_20 T122 x4.
Hypothesis hyp23 : intelements_7 (f_tab this) l_left_3 =
             intelements_20 (f_tab this) l_hi.
Hypothesis hyp24 : intelements_7 (f_tab this) l_hi =
             intelements_20 (f_tab this) l_left_3.
Hypothesis hyp25 : ~ l_left_3 < l_right_3.
Hypothesis hyp26 : l_left_3 <= l_right_3.
Hypothesis hyp27 : f_tab this <> null.
Hypothesis hyp28 : forall l_n : t_int,
             l_right_3 < l_n /\ l_n <= l_hi ->
             intelements (f_tab this) l_hi <= intelements_20 (f_tab this) l_n.
Hypothesis hyp29 : intelements (f_tab this) l_hi <=
             intelements_20 (f_tab this) l_right_3.
Hypothesis hyp30 : forall l_i : t_int,
             t_int ->
             t_int ->
             l_lo <= l_i /\ l_i < l_left_3 ->
             intelements_20 (f_tab this) l_i <= intelements (f_tab this) l_hi.
Hypothesis hyp31 : forall l_j14 : t_int,
             l_left_3 < l_j14 /\ l_j14 <= l_hi ->
             intelements (f_tab this) l_hi <=
             intelements_20 (f_tab this) l_j14.
Hypothesis hyp32 : forall l_m : t_int,
             l_lo <= l_m /\ l_m < l_left_3 ->
             intelements_20 (f_tab this) l_m <= intelements (f_tab this) l_hi.
Hypothesis hyp33 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp34 : ~ ~ l_lo < l_hi.
Hypothesis hyp35 : instances this.
Hypothesis hyp36 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.
Ltac purify := simpl_pure.

Lemma l: 
   forall T12 : Reference,
   instances T12 ->
   (fun x : Reference => instances x /\ typeof x = array (class c_int) 1) T12 ->
   forall x10 : t_int,
   ~
   (let x9 :=
      (fun x8 : t_int =>
       interval l_lo l_hi x8 \/ singleton Reference (f_tab this) T12)
      :t_int -> Prop in
    x9 x10) -> intelements_7 T12 x10 = intelements T12 x10.
Proof with autoJ.
(* Write your proof here *)
startJack.
rewrite hyp3...
rewrite hyp5...
rewrite hyp6...











Qed.
End JackProof.
