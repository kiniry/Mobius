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
 | Call :  methodNames  -> stmt
 | Signal :  event -> stmt.


Parameter meth_dec: forall x y : methodNames, {x = y} + {x <> y}.
Definition eq_methNames : methodNames -> methodNames -> bool := (fun x y => if (meth_dec x y) then true else false).

(*Specification notions*)
(*assertion is a function of states, ghost states and traces to propositions *)
Definition assertion := state -> list event -> state -> Prop.

(* a function which maps method names to method postconditions *)
Definition methPost := methodNames -> assertion.
(* a function which maps method names to method strong invariants*)
Definition methInv := methodNames ->   assertion.

Definition body := methodNames -> stmt.
 
Definition program :=   list  methodNames  .


(**************************************************************************************************************)
(* 

Definition stateA := Z -> state.

Definition invA := state -> stateA -> Prop.

Inductive instrA  : Type :=
 | AffectA : var -> expr -> instrA
 | IfA     : expr -> stmtA -> stmtA -> instrA
 | WhileA  : expr -> invA  -> stmtA -> instrA
 | SetA    : Z -> instrA
 
with stmtA : Type :=
 | SnilA   : stmtA
 | SseqA   : instrA -> stmtA -> stmtA.

Scheme instrA_ind_mut := Induction for instrA Sort Prop
with stmtA_ind_mut  := Induction for stmtA Sort Prop.


Inductive progA : Type :=
 | ProgA : preProg -> stmtA -> postProg -> progA.

*)


(*
(* Programe stmtG *)

Inductive instrG (n:nat) : Type :=
 | AffectG  : var -> expr -> instrG n
 | IfG      : expr -> stmtG n -> stmtG n -> instrG n
 | WhileG   : expr -> assertionIndex (S n)  -> stmtG n -> instrG n
 | DeclareG : nat  -> instrG n  
 
with stmtG (n:nat) : Type :=
 | SnilG   : stmtG n
 | SseqG   : instrG n -> stmtG n -> stmtG n.

Scheme instrG_ind_mut := Induction for instrG Sort Prop
with stmtG_ind_mut  := Induction for stmtG Sort Prop.

Inductive progG (n:nat) : Type :=
 | ProgG : preProg -> stmtG n -> postProg -> progG n.
*)








(* (* Definition language for wp without propagation *)

Fixpoint assertionIndex (n:nat) : Type := 
 match n with 
 | O => Prop
 | S n => state -> assertionIndex n
 end.

Inductive instrIndex : nat -> Type :=
 | AffectIndex  : forall n, var -> expr -> instrIndex n
 | IfIndex      : forall n, expr -> stmtIndex n -> stmtIndex n -> instrIndex n
 | WhileIndex   : forall n, 
     expr -> (state -> assertionIndex n)  -> stmtIndex n -> instrIndex n
 | DeclareIndex : forall n, stmtIndex (S n) -> instrIndex n  
 
with stmtIndex : nat -> Type :=
 | SnilIndex   : forall n, stmtIndex n
 | SseqIndex   : forall n, instrIndex n -> stmtIndex n -> stmtIndex n.

Scheme instrIndex_ind_mut := Induction for instrIndex Sort Prop
with stmtIndex_ind_mut  := Induction for stmtIndex Sort Prop.
*)
