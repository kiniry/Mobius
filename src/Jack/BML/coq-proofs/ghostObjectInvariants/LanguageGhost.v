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





Inductive gStmt  : Type :=
 | GAffect  : var      -> expr -> gStmt
 | GIf         : expr    -> gStmt -> gStmt -> gStmt
 | GWhile  : expr    -> gStmt -> gStmt
 | GSseq   : gStmt  -> gStmt -> gStmt
 | GSkip    : gStmt 	
 | GCall     : methodNames  -> gStmt
 | Pack : gStmt
 | Unpack : gStmt.



Parameter meth_dec: forall x y : methodNames, {x = y} + {x <> y}.
Definition eq_methNames : methodNames -> methodNames -> bool := (fun x y => if (meth_dec x y) then true else false).

(*Specification notions*)
(*assertion is a function of states, ghost states and traces to propositions *)
Definition gAssertion := state -> bool -> state -> bool -> Prop.
Definition gAssertion1 := state -> bool  -> Prop.

Definition Invariant := state   -> Prop.


(* a function which maps method names to method postconditions *)
Definition gMethPost := methodNames -> gAssertion.

(* a function which maps method names to method postconditions *)
Definition gMethPre := methodNames -> gAssertion1.


Definition gBody := methodNames -> gStmt.
 














