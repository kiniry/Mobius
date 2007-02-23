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

 | ExecWhile_true  : forall s1 s2 s3 e  stmt,
     eval_expr s1 e <> 0 ->
     exec_stmt s1 stmt s2 ->
     exec_stmt s2 (While e stmt) s3 ->
     exec_stmt s1 (While e stmt) s3

 | ExecWhile_false  : forall s1 e  stmt,
     eval_expr s1 e = 0 ->
     exec_stmt s1 (While e  stmt) s1
 
 
 | ExecSseq   : forall s1 s2 s3 i stmt,
      exec_stmt s1 i s2 -> 
      exec_stmt s2 stmt s3 -> 
      exec_stmt s1 (Sseq i stmt) s3

 | ExecSkip : forall s, exec_stmt s Skip s
 
 | ExecCall : forall s1 s2 stmt mName, 
       exec_stmt s1 stmt s2 -> 
       exec_stmt s1 (Call mName  stmt) s2.


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
