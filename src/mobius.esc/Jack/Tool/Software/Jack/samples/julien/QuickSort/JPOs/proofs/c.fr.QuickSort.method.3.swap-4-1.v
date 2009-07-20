Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_24 : REFERENCES -> t_int.
Variable shortelements_16 : REFERENCES -> t_short.
Variable byteelements_16 : REFERENCES -> t_byte.
Variable booleanelements_16 : REFERENCES -> bool.
Variable charelements_16 : REFERENCES -> t_char.
Variable refelements_16 : REFERENCES -> REFERENCES.
Variable newObject_34 : REFERENCES.
Variable this : REFERENCES.
Variable l_i0 : t_int.
Variable l_j0 : t_int.
Hypothesis req1 : ((((f_tab this <> null /\ 0 <= l_i0) /\
               l_i0 < arraylength (f_tab this)) /\ 
              0 <= l_j0) /\ l_j0 < arraylength (f_tab this)) /\ 
            true = true.
Hypothesis hyp1 : ~ instances newObject_34.
Hypothesis hyp2 : newObject_34 <> null.
Hypothesis hyp3 : f_tab this <> null.
Hypothesis hyp4 : ~ interval 0 (j_sub (arraylength (f_tab this)) 1) l_i0.
Hypothesis hyp5 : f_tab this <> null.
Hypothesis hyp6 : interval 0 (j_sub (arraylength (f_tab this)) 1) l_i0.
Hypothesis hyp7 : instances this.
Hypothesis hyp8 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   false = true.
Proof with autoJ.
(* Write your proof here *)
startJack.
destruct hyp4; split; j_omega.
Qed.
End JackProof.
