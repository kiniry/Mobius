Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_21 : REFERENCES -> t_int.
Variable shortelements_12 : REFERENCES -> t_short.
Variable byteelements_12 : REFERENCES -> t_byte.
Variable booleanelements_12 : REFERENCES -> bool.
Variable charelements_12 : REFERENCES -> t_char.
Variable refelements_12 : REFERENCES -> REFERENCES.
Variable newObject_28 : REFERENCES.
Variable this : REFERENCES.
Variable l_lo : t_int.
Variable l_hi : t_int.
Hypothesis req1 : ((((f_tab this <> null /\ 0 <= l_lo) /\
               l_lo < arraylength (f_tab this)) /\ 
              0 <= l_hi) /\ l_hi < arraylength (f_tab this)) /\ 
            true = true.
Hypothesis hyp1 : ~ instances newObject_28.
Hypothesis hyp2 : newObject_28 <> null.
Hypothesis hyp3 : f_tab this <> null.
Hypothesis hyp4 : ~ interval 0 (j_sub (arraylength (f_tab this)) 1) l_hi.
Hypothesis hyp5 : ~ ~ l_lo < l_hi.
Hypothesis hyp6 : instances this.
Hypothesis hyp7 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   false = true.
Proof with autoJ.
(* Write your proof here *)
startJack.
destruct hyp4...
j_omega.


Qed.
End JackProof.
