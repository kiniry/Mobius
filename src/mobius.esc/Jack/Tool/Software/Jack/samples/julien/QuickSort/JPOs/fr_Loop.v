Add LoadPath "/home/jcharles/sources/runtime-workspace/QuickSort/JPOs".

Require Import ZArith.
Require Import "jack_arith".
Require Import "jack_references".
Require Import "fr_Loop_classes".

Require Import "fr_Loop_subtypes".

Module JackLogic.
Module JackClasses := JackReferences fr_LoopClasses.

(* Importing Jack arithmetic and classes *)
Import JackArith.
Import JackClasses.
Import fr_LoopClasses.
Import fr_LoopSubtypes.

Export JackArith.
Export JackClasses.
Export fr_LoopClasses.
Export fr_LoopSubtypes.

(* Some more array things *)
Lemma j_le_lt_or_eq: forall n m:Z, n <= m -> n < m \/ n = m.
Proof.
unfold j_le, j_lt. intros; omega.
Qed.

Axiom ArrayTypeAx :
forall arr c n,  (subtypes (typeof arr) (array (class c) n)) -> 
     forall pos, subtypes (typeof (refelements arr pos)) (class c).

Axiom arraylenAx : forall a c n, instances a -> subtypes (typeof a) (array c n) -> j_le 0 (arraylength a).


(* Fields definitions *)


Load "/home/jcharles/sources/runtime-workspace/QuickSort/JPOs/jack_tactics.v".
End JackLogic.

