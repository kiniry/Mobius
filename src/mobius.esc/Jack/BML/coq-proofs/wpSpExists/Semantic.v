Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import BasicDef.
Require Import Language.


Inductive exec_stmt : state -> stmt -> state -> Prop := 

 | ExecAffect      : forall s x e, 
     exec_stmt s (Affect x e) (update s x (eval_expr s e))

 | ExecIf_true     : forall s1 s2 e stmtT stmtF,
     eval_expr s1 e <> 0 -> 
     exec_stmt s1 stmtT s2 ->
     exec_stmt s1 (If e stmtT stmtF) s2

 | ExecIf_false    : forall s1 s2 e stmtT stmtF,
     eval_expr s1 e = 0 -> 
     exec_stmt s1 stmtF s2 ->
     exec_stmt s1 (If e stmtT stmtF) s2

 | ExecWhile_true  : forall s1 s2 s3 e inv stmt,
     eval_expr s1 e <> 0 ->
     exec_stmt s1 stmt s2 ->
     exec_stmt s2 (While e inv stmt) s3 ->
     exec_stmt s1 (While e inv stmt) s3

 | ExecWhile_false  : forall s1 e inv stmt,
     eval_expr s1 e = 0 ->
     exec_stmt s1 (While e inv stmt) s1
 
 | ExecSnil : forall s, exec_stmt s Snil s

 | ExecSseq   : forall s1 s2 s3 i stmt,
      exec_stmt s1 i s2 -> 
      exec_stmt s2 stmt s3 -> 
      exec_stmt s1 (Sseq i stmt) s3.

(* Scheme exec_stmt_ind_mut := Induction for exec_stmt Sort Prop
with exec_stmt_ind_mut  := Induction for exec_stmt Sort Prop.
*)





(*
Definition updateA (aux : stateA) n s p := if Zeq_bool n p then s else aux p.
 
Inductive exec_instrA : state -> stateA -> instrA -> state -> stateA -> Prop:= 

 | ExecAffectA      : forall s aux x e, 
     exec_instrA s aux (AffectA x e) (update s x (eval_expr s e)) aux

 | ExecIfA_true     : forall s1 aux1 s2 aux2 e stmtT stmtF,
     eval_expr s1 e <> 0 -> 
     exec_stmtA s1 aux1 stmtT s2 aux2 ->
     exec_instrA s1 aux1 (IfA e stmtT stmtF) s2 aux2 

 | ExecIfA_false    : forall s1 aux1 s2 aux2 e stmtT stmtF,
     eval_expr s1 e = 0 -> 
     exec_stmtA s1 aux1 stmtF s2 aux2 ->
     exec_instrA s1 aux1 (IfA e stmtT stmtF) s2 aux2 

 | ExecWhileA_true  : forall s1 aux1 s2 aux2 s3 aux3 e inv stmt,
     eval_expr s1 e <> 0 ->
     exec_stmtA s1 aux1 stmt s2 aux2 ->
     exec_instrA s2 aux2 (WhileA e inv stmt) s3 aux3 ->
     exec_instrA s1 aux1 (WhileA e inv stmt) s3 aux3 

 | ExecWhileA_false  : forall s aux e inv stmt,
     eval_expr s e = 0 ->
     exec_instrA s aux (WhileA e inv stmt) s aux

 | ExecSetA          : forall n s aux,
     exec_instrA s aux (SetA n) s (updateA aux n s)

with exec_stmtA : state -> stateA -> stmtA -> state -> stateA -> Prop :=

 | ExecSnilA : forall s aux , exec_stmtA s aux SnilA s aux

 | ExecSseqA : forall s1 aux1 s2 aux2 s3 aux3 i stmt,
      exec_instrA s1 aux1 i s2 aux2 -> 
      exec_stmtA s2 aux2 stmt s3 aux3 -> 
      exec_stmtA s1 aux1 (SseqA i stmt) s3 aux3.

Scheme exec_instrA_ind_mut := Induction for exec_instrA Sort Prop
with exec_stmtA_ind_mut  := Induction for exec_stmtA Sort Prop.

*)


































(*
Inductive exec_instrG (n:nat) : state -> instrG n -> state -> Prop := 

 | ExecAffectG      : forall s x e, 
     exec_instrG n s (AffectG n x e) (update s x (eval_expr s e))

 | ExecIfG_true     : forall s1 s2 e stmtT stmtF,
     eval_expr s1 e <> 0 -> 
     exec_stmtG n s1 stmtT s2 ->
     exec_instrG n s1 (IfG n e stmtT stmtF) s2

 | ExecIfG_false    : forall s1 s2 e stmtT stmtF,
     eval_expr s1 e = 0 -> 
     exec_stmtG n s1 stmtF s2 ->
     exec_instrG n s1 (IfG n e stmtT stmtF) s2

 | ExecWhileG_true  : forall s1 s2 s3 e inv stmt,
     eval_expr s1 e <> 0 ->
     exec_stmtG n s1 stmt s2 ->
     exec_instrG n s2 (WhileG n e inv stmt) s3 ->
     exec_instrG n s1 (WhileG n e inv stmt) s3

 | ExecWhileG_false  : forall s1 e inv stmt,
     eval_expr s1 e = 0 ->
     exec_instrG n s1 (WhileG n e inv stmt) s1

 | ExecDeclareG      : forall p s,
     exec_instrG n s (DeclareG n p) s
 
with exec_stmtG (n:nat) : state -> stmtG n -> state -> Prop :=

 | ExecSnilG : forall s, exec_stmtG n s (SnilG n) s

 | ExecSseqG   : forall s1 s2 s3 i stmt,
      exec_instrG n s1 i s2 -> 
      exec_stmtG n s2 stmt s3 -> 
      exec_stmtG n s1 (SseqG n i stmt) s3.

Scheme exec_instrG_ind_mut := Induction for exec_instrG Sort Prop
with exec_stmtG_ind_mut  := Induction for exec_stmtG Sort Prop.

*)




























(*Inductive exec_instrIndex : 
         forall n, state -> instrIndex n -> state -> Prop := 

 | ExecAffectIndex      : forall n s x e, 
     exec_instrIndex n s (AffectIndex n x e) (update s x (eval_expr s e))

 | ExecIfIndex_true     : forall n s1 s2 e stmtT stmtF,
     eval_expr s1 e <> 0 -> 
     exec_stmtIndex n s1 stmtT s2 ->
     exec_instrIndex n s1 (IfIndex n e stmtT stmtF) s2

 | ExecIfIndex_false    : forall n s1 s2 e stmtT stmtF,
     eval_expr s1 e = 0 -> 
     exec_stmtIndex n s1 stmtF s2 ->
     exec_instrIndex n s1 (IfIndex n e stmtT stmtF) s2

 | ExecWhileIndex_true  : forall n s1 s2 s3 e inv stmt,
     eval_expr s1 e <> 0 ->
     exec_stmtIndex n s1 stmt s2 ->
     exec_instrIndex n s2 (WhileIndex n e inv stmt) s3 ->
     exec_instrIndex n s1 (WhileIndex n e inv stmt) s3

 | ExecWhileIndex_false  : forall n s1 e inv stmt,
     eval_expr s1 e = 0 ->
     exec_instrIndex n s1 (WhileIndex n e inv stmt) s1

 | ExecDeclareIndex      : forall n s1 s2 stmt,
     exec_stmtIndex (S n) s1 stmt s2 ->
     exec_instrIndex n s1 (DeclareIndex n stmt) s2
 
with exec_stmtIndex : forall n, state -> stmtIndex n -> state -> Prop :=

 | ExecSnilIndex : forall n s, exec_stmtIndex n s (SnilIndex n) s

 | ExecSseqIndex   : forall n s1 s2 s3 i stmt,
      exec_instrIndex n s1 i s2 -> 
      exec_stmtIndex n s2 stmt s3 -> 
      exec_stmtIndex n s1 (SseqIndex n i stmt) s3.

Scheme exec_instrIndex_ind_mut := Induction for exec_instrIndex Sort Prop
with exec_stmtIndex_ind_mut  := Induction for exec_stmtIndex Sort Prop.


*)
