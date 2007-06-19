Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef.
Require Import Coq.Init.Datatypes.

Export ZArith.
Export Bool.
Export BoolEq.
Export List.
Export BasicDef.



Inductive stmt  : Type :=
 | Affect : var -> expr -> stmt
 | If     :  expr -> stmt -> stmt -> stmt
 | While  : expr -> stmt -> stmt
 | Sseq   : stmt -> stmt -> stmt 
 | Skip : stmt
 | Call :  methodNames   -> stmt.



Parameter meth_dec: forall x y : methodNames, {x = y} + {x <> y}.
Definition eq_methNames : methodNames -> methodNames -> bool := (fun x y => if (meth_dec x y) then true else false).

(*Specification notions*)
(*assertion is a function of states, ghost states and traces to propositions *)
Definition assertion := state -> state -> Prop.


Definition assertion1 := state -> Prop.


(* a function which maps method names to method postconditions *)
Definition methPost := methodNames -> assertion.

(* a function which maps method names to method postconditions *)
Definition methPre := methodNames -> assertion1.


Definition body := methodNames -> stmt.
 

Definition program :=   list  methodNames  .












