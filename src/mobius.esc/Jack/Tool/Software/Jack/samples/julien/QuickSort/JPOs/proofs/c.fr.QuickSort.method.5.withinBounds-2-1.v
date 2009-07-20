Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_28 : REFERENCES -> t_int.
Variable shortelements_20 : REFERENCES -> t_short.
Variable byteelements_20 : REFERENCES -> t_byte.
Variable booleanelements_20 : REFERENCES -> bool.
Variable charelements_20 : REFERENCES -> t_char.
Variable refelements_20 : REFERENCES -> REFERENCES.
Variable newObject_43 : REFERENCES.
Variable this : REFERENCES.
Variable l_i0 : t_int.
Hypothesis req1 : true = true /\ true = true.
Hypothesis hyp1 : ~ instances newObject_43.
Hypothesis hyp2 : newObject_43 <> null.
Hypothesis hyp3 : f_tab this = null.
Hypothesis hyp4 : 0 <= l_i0.
Hypothesis hyp5 : f_tab this <> null.
Hypothesis hyp6 : instances this.
Hypothesis hyp7 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   false = true.
Proof with autoJ.
(* Write your proof here *)
startJack.
intuition.
Qed.
End JackProof.
