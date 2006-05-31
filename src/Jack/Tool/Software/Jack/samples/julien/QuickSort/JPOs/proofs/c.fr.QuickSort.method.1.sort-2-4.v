Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_1 : REFERENCES -> t_int -> t_int.
Variable this : REFERENCES.
Hypothesis req1 : f_tab this <> null /\ true = true.
Hypothesis hyp1 : f_tab this <> null.
Hypothesis hyp2 : forall x0 : REFERENCES,
            ~ singleton REFERENCES (f_tab this) x0 ->
            intelements_1 x0 = intelements x0.
Hypothesis hyp3 : forall T66 : REFERENCES,
            singleton REFERENCES (f_tab this) T66 ->
            forall x0 : t_int,
            ~ interval 0 (j_sub (arraylength (f_tab this)) 1) x0 ->
            intelements_1 T66 x0 = intelements T66 x0.
Hypothesis hyp4 : (forall l_i0 : t_int,
             t_int ->
             forall l_j36 : t_int,
             0 <= l_i0 /\ l_i0 <= arraylength (f_tab this) - 1 ->
             0 <= l_j36 /\ l_j36 <= arraylength (f_tab this) - 1 ->
             l_i0 < l_j36 ->
             intelements_1 (f_tab this) l_i0 <=
             intelements_1 (f_tab this) l_j36) /\
            (forall l_i37 : t_int,
             0 <= l_i37 /\ l_i37 <= arraylength (f_tab this) - 1 ->
             exists l_j37 : t_int,
               (0 <= l_j37 /\ l_j37 <= arraylength (f_tab this) - 1) /\
               intelements (f_tab this) l_j37 =
               intelements_1 (f_tab this) l_i37).
Hypothesis hyp5 : 0 < arraylength (f_tab this).
Hypothesis hyp6 : f_tab this <> null.
Hypothesis hyp7 : instances this.
Hypothesis hyp8 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall T0 : REFERENCES,
   instances T0 ->
   (fun x : REFERENCES => instances x /\ typeof x = array (class c_int) 1) T0 ->
   forall x8 : t_int,
   ~
   (let x7 :=
      (fun x6 : t_int =>
       interval 0 (j_sub (arraylength (f_tab this)) 1) x6 \/
       singleton REFERENCES (f_tab this) T0)
      :t_int -> Prop in
    x7 x8) -> intelements_1 T0 x8 = intelements T0 x8.
Proof with autoJ.
(* Write your proof here *)
startJack.
rewrite hyp2...
Qed.
End JackProof.
