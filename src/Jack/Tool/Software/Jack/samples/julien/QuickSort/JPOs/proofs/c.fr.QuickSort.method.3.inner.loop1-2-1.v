Require Import Bool.
Require Import ZArith.
Require Import Classical.
Require Import "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/fr_QuickSort".

Load "/user/jcharles/home/runtime-workspace/QuickSort/JPOs/userTactics.v".

Open Scope Z_scope.
Open Scope J_Scope.
Section JackProof.
Variable intelements_18 : REFERENCES -> t_int.
Variable shortelements_10 : REFERENCES -> t_short.
Variable byteelements_10 : REFERENCES -> t_byte.
Variable booleanelements_10 : REFERENCES -> bool.
Variable charelements_10 : REFERENCES -> t_char.
Variable refelements_10 : REFERENCES -> REFERENCES.
Variable newObject_23 : REFERENCES.
Variable l_i0_1 : t_int.
Variable this : REFERENCES.
Variable l_i0 : t_int.
Variable l_hi : t_int.
Variable l_pivot0 : t_int.
Hypothesis req1 : (((f_tab this <> null /\ 0 <= l_i0) /\
              l_i0 < arraylength (f_tab this)) /\
             (f_tab this <> null /\ 0 <= l_hi) /\
             l_hi < arraylength (f_tab this)) /\ true = true.
Hypothesis hyp1 : ~ instances newObject_23.
Hypothesis hyp2 : newObject_23 <> null.
Hypothesis hyp3 : f_tab this <> null.
Hypothesis hyp4 : ~ interval 0 (j_sub (arraylength (f_tab this)) 1) l_i0_1.
Hypothesis hyp5 : l_i0_1 < l_hi.
Hypothesis hyp6 : forall l_k71 : t_int,
            l_i0 <= l_k71 /\ l_k71 < l_i0_1 ->
            intelements (f_tab this) l_k71 <= l_pivot0.
Hypothesis hyp7 : instances this.
Hypothesis hyp8 : subtypes (typeof this) (class c_fr_QuickSort).

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   false = true.
Proof with autoJ.
(* Write your proof here *)
startJack.



Qed.
End JackProof.
