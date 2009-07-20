Require Import Bool.
Require Import ZArith.
Require Import Classical.
Add LoadPath "/home/jcharles/sources/runtime-workspace/QuickSort/JPOs".
Require Import "Loop_classes".
Load "user_extensions.v".
Require Import "Loop".
Import JackLogic.
Open Scope Z_scope.
Open Scope J_Scope.

Section JackProof.

Variable local_0: Reference.

Variable local_1: t_int.

Variable local_2: Reference.

Hypothesis req1 : (not ((local_0 = null))).

Hypothesis req2 : (subtypes (typeof local_0) (class c_fr_Loop)).

Hypothesis hyp1 : (not ((arrayReference_15 = null))).

Hypothesis hyp2 : (j_lt local_1_16 3).

Hypothesis hyp3 : (j_le 0 local_1_16).

Hypothesis hyp4 : (j_lt local_1_16 3).

Hypothesis hyp5 : (not ((arrayReference_15 = null))).

Hypothesis hyp6 : (((((j_le 0 local_1_16)) /\ ((j_le local_1_16 3)))) /\ ((forall (var_0z: t_int), (((((j_le 0 var_0z)) /\ ((j_lt var_0z local_1_16)))) ->
(((intelements arrayReference_15) var_0z) = 0))))).

Hypothesis hyp7 : (j_le 0 (j_sub 3 local_1_16)).

Hypothesis hyp8 : (* 0 = 0 *)True.

Hypothesis hyp9 : (* 0 = 0 *)True.

Hypothesis hyp10 : ((arraylength arrayReference_15) = 3).

Hypothesis hyp11 : (null <> arrayReference_15).


Ltac autoJ := autoJack; arrtac.
Ltac purify := simpl_pure.


Lemma l:
(j_le 0 (j_add local_1_16 1)).
Proof with autoJ.
(* Write your proof here *)
startJack.
j_omega.

Qed.
End JackProof.
