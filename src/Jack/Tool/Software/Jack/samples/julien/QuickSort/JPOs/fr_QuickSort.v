Add LoadPath "/home/jcharles/sources/runtime-workspace/QuickSort/JPOs".

Require Import ZArith.
Require Import "jack_arith".
Require Import "jack_references".
Require Import "fr_QuickSort_classes".

Require Import "fr_QuickSort_subtypes".

Module JackLogic.
Module JackClasses := JackReferences fr_QuickSortClasses.

(* Importing Jack arithmetic and classes *)
Import JackArith.
Import JackClasses.
Import fr_QuickSortClasses.
Import fr_QuickSortSubtypes.

Export JackArith.
Export JackClasses.
Export fr_QuickSortClasses.
Export fr_QuickSortSubtypes.

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
Definition f_fr_QuickSort_tab_type := Reference -> Reference.
Variable f_tab : f_fr_QuickSort_tab_type.

Axiom f_tabDom : forall (n: Reference), (subtypes (typeof (f_tab n))(array (class c_int) 1)) <-> subtypes (typeof n) (class c_fr_QuickSort).
Axiom f_tabRan : forall (n: Reference), n <> null -> subtypes (typeof n) (class c_fr_QuickSort) -> ((instances (f_tab n)) \/ ((f_tab n) = null)).


Load "/home/jcharles/sources/runtime-workspace/QuickSort/JPOs/jack_tactics.v".
End JackLogic.

