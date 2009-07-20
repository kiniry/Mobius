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

Ltac autoJ := autoJack; arrtac.

Lemma l: 
   forall T17 : REFERENCES,
   instances T17 ->
   (fun x : REFERENCES =>
    instances x /\
    elemtypeDomDef (typeof x) /\
    typeof x <> array (class c_int) 1 /\
    typeof x <> array (class c_short) 1 /\
    typeof x <> array (class c_byte) 1 /\ typeof x <> array (class c_char) 1)
     T17 ->
   functionEquals t_int REFERENCES (refelements T17) (refelements T17).
Proof with autoJ.
(* Write your proof here *)
startJack.
auto.
Qed.
End JackProof.
