Add LoadPath "/home/jcharles/sources/runtime-workspace/QuickSort/JPOs".

(* I am the fourth and final little helper. *)
Require Import "jack_arith".
Require Import "jack_references".

(** * The User Extensions Library *)

Module UserExtensions (Arg: JackClasses).
Module JackRefs := JackReferences Arg.
Import JackRefs.
Open Scope J_Scope.
Ltac myassert t := 
  match type of t with
  | ?A -> ?B =>
     let H1 := fresh "H" in 
     let H' := fresh "H" in
     (assert (H1 : A);
      [trivial;idtac | myassert (t H1)])
  | _ => let H1 := fresh "H" in assert (H1 := t)
  end.

End UserExtensions.
