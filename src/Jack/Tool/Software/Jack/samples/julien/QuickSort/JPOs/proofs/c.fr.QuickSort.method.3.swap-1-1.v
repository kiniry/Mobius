Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable this : REFERENCES.
Variable l_i0 : t_int.
Variable l_j0 : t_int.
Hypothesis req1 : ((((f_tab this <> null /\ 0 <= l_i0) /\
               l_i0 < arraylength (f_tab this)) /\ 
              0 <= l_j0) /\ l_j0 < arraylength (f_tab this)) /\ 
            true = true.
Hypothesis hyp1 : f_tab this <> null.
Hypothesis hyp2 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_j0.
Hypothesis hyp3 : f_tab this <> null.
Hypothesis hyp4 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_j0.
Hypothesis hyp5 : f_tab this <> null.
Hypothesis hyp6 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_i0.
Hypothesis hyp7 : f_tab this <> null.
Hypothesis hyp8 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_i0.
Hypothesis hyp9 : instances this.
Hypothesis hyp10 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac unfold_pure H := unfold Def_greater_or_equal_10, Def_greater_or_equal_32, Def_greater_or_equal_61, Def_greater_or_equal_83 in H.
Ltac unfold_pure_all := unfold Def_greater_or_equal_10, Def_greater_or_equal_32, Def_greater_or_equal_61, Def_greater_or_equal_83 in *.
Ltac autoJ := unfold_pure_all; autoJack; arrtac.

Lemma l: 
   overridingCoupleZ t_int
     (overridingCoupleZ t_int (intelements (f_tab this)) l_i0
        (intelements (f_tab this) l_j0)) l_j0 (intelements (f_tab this) l_i0)
     l_i0 = intelements (f_tab this) l_j0.
Proof with autoJ.
(* Write your proof here *)
startJack.

Qed.
End JackProof.
