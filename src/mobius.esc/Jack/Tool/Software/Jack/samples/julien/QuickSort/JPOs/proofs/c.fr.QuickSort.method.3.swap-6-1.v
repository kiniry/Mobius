Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_27 : REFERENCES -> t_int.
Variable shortelements_19 : REFERENCES -> t_short.
Variable byteelements_19 : REFERENCES -> t_byte.
Variable booleanelements_19 : REFERENCES -> bool.
Variable charelements_19 : REFERENCES -> t_char.
Variable refelements_19 : REFERENCES -> REFERENCES.
Variable newObject_40 : REFERENCES.
Variable this : REFERENCES.
Variable l_i0 : t_int.
Variable l_j0 : t_int.
Hypothesis req1 : ((((f_tab this <> null /\ 0 <= l_i0) /\
               l_i0 < arraylength (f_tab this)) /\ 
              0 <= l_j0) /\ l_j0 < arraylength (f_tab this)) /\ 
            true = true.
Hypothesis hyp1 : ~ instances newObject_40.
Hypothesis hyp2 : newObject_40 <> null.
Hypothesis hyp3 : f_tab this = null.
Hypothesis hyp4 : instances this.
Hypothesis hyp5 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   false = true.
Proof with autoJ.
(* Write your proof here *)
startJack.
destruct H...
Qed.
End JackProof.
