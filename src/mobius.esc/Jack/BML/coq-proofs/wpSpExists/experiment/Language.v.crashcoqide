Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef.
Require Import Logic_n.

Inductive inv : Type := 
  | Inv : assertion -> list var -> inv.



Inductive stmt  : Type :=
 | Affect : Z -> var ->  expr -> stmt
 | If     : Z -> expr ->   stmt -> stmt -> stmt
 | While  : Z -> expr -> inv  -> stmt -> stmt
 | Snil   : Z -> stmt
 | Sseq   : Z -> stmt -> stmt -> stmt.

(* Scheme instr_ind_mut := Induction for instr Sort Prop
with stmt_ind_mut  := Induction for stmt Sort Prop.
*)
Inductive prog : Type :=
 | Prog : preProg -> stmt -> postProg -> prog.

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
