Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import BasicDef.
(*Require Import Coq.Lists.List.*)
Require Export List.
Require Import Language.

(* Variable  event :  Set.
 Inductive event : Set := 
 | Noevent : event
 | Event :  forall (e : eventName) , event  . *)

(*BIG STEP OPERATIONAL SEMANTICS WHICH DESCRIBE TERMINATING EXECUTIONS. 
   THE DEFINITION IS PARAMETRIZED WITH A PROGRAM (WHICH IS DEFINED AS A SET OF METHODS) 
   AND A FUNCTION B (OF TYPE body) WHICH MAPS METHOD NAMES TO METHOD BODIES (THOSE ARE STATEMENTS).
   THE SEMANTICS MANIPULATES INITIAL AND TERMINAL STATE BUT ALSO A TRACE OF EVENTS 
   WHICH ARE EMITTED DURING THE EXECUTION OF THE STATEMENT
*)
Inductive t_exec (P : program)(B: body) :  state -> stmt -> list event -> state -> Prop := 

 | ExecAffect      : forall s x e, 
     t_exec  P B s (Affect x e) nil (update s x (eval_expr s e))

 | ExecIf_true     : forall s1 s2 e stmtT stmtF eventsT,
     eval_expr s1 e <> 0 -> 
     t_exec P B s1 stmtT eventsT s2 ->
     t_exec P B s1 (If e stmtT stmtF) eventsT s2

 | ExecIf_false    : forall s1 s2 e stmtT stmtF eventsF,
     eval_expr s1 e = 0 -> 
     t_exec P B s1 stmtF eventsF s2 ->
     t_exec P B s1 (If e stmtT stmtF) eventsF s2

 | ExecWhile_true  : forall s1 s2 s3 e  stmt eventsI eventsC  ,
     eval_expr s1 e <> 0 ->
     t_exec P B s1 stmt eventsI s2 ->
     t_exec P B s2 (While e stmt) eventsC s3 ->
     t_exec P B s1 (While e stmt) (app eventsI  eventsC)  s3

 | ExecWhile_false  : forall s1 e  stmt ,
     eval_expr  s1 e = 0 ->
     t_exec P  B s1 (While e  stmt) nil  s1
 
 
 | ExecSseq   : forall s1 s2 s3 stmt1 stmt2 events1 events2,
      t_exec P  B s1 stmt1 events1 s2 -> 
      t_exec P  B s2 stmt2 events2 s3 -> 
      t_exec P  B s1 (Sseq stmt1 stmt2) (app events1  events2) s3

 | ExecSkip : forall s, t_exec P B s Skip nil s
 
 | ExecCall : forall s1 s2 ( mName  : methodNames) eventsB, 
       (In mName P) ->  	
       t_exec P  B s1 (B mName) eventsB s2 -> 
       t_exec P  B s1 (Call mName  ) eventsB  s2

 | ExecSignal : forall s event, t_exec P B s ( Signal  event ) (  event :: nil ) s .


(* RELATION WHICH DESCRIBED THE REACHABLE STATES IN THE EXECUTION OF A STATEMENT. 
    IT ALSO CONTAINS THE TRACE OF EVENTS EMITTED FROM IN THE EXECUTION STARTING 
    FROM THE INITIAL STATE UPTO THE CURRENT STATE
*)
Inductive reach (P : program)(B: body): state -> stmt -> list event ->  state -> Prop := 

 | ReachAffect      : forall s x e, 
     reach P B s (Affect x e)  nil (update s x (eval_expr s e))

 | ReachIf_true     : forall s1 s2 e stmtT stmtF eventsT ,
     eval_expr s1 e <> 0 -> 
     reach P B s1 stmtT eventsT  s2 ->
     reach P B s1  (If e stmtT stmtF) eventsT s2

 | ReachIf_false    : forall s1 s2 e stmtT stmtF eventsF,
     eval_expr s1 e = 0 -> 
     reach P B s1 stmtF eventsF   s2 ->
     reach P B s1 (If e stmtT stmtF) eventsF  s2

(*WHILE*)
(*this constructor describes as a reachable state the final state of a loop execution *)
 | ReachWhile_false  : forall s1 e  stmt,
     eval_expr s1 e = 0 ->
     reach P B s1 (While e  stmt) nil s1

(* every state reachable in the execution of the loop body is reachable in the execution of the whole loop *)
 | ReachWhile_true1  : forall s1 s2  e  stmt eventsB,
     eval_expr s1 e <> 0 ->
     reach P B s1 stmt eventsB s2 ->
     reach P B s1 (While e stmt) eventsB s2

(* every state occurring in a loop execution after one terminated iteration is reachable in the loop *)
 | ReachWhile_true2  : forall s1 s2 s3 e  stmt eventsB eventsW,
     eval_expr s1 e <> 0 ->
     t_exec P B s1 stmt eventsB s2 ->
     reach   P B s2 (While e stmt) eventsW  s3 ->
     reach   P B s1 (While e stmt) (app eventsB eventsW) s3
(*SEQUENCE*)
(*every state reachable in the first statement is reachable by the sequence statement*)
 | ReachSseq1   : forall s1 s2 stmt1 stmt2 events1,
      reach P B s1 stmt1 events1 s2 -> 
      reach P B s1 (Sseq stmt1 stmt2) events1 s2
(*every state reachable in the second statement is reachable by the sequence statement on the condition that the first statement has terminated*)
 | ReachSseq2   : forall s1 s2 s3 stmt1 stmt2 events1 events2,
      t_exec P B s1 stmt1 events1 s2 -> 
      reach  P  B s2  stmt2 events2 s3 -> 
      reach  P  B s1 (Sseq stmt1 stmt2 )  (app events1 events2) s3

 | ReachSkip : forall s, reach P B s Skip nil s

 | ReachCall : forall s1 s2 ( mName  : methodNames) eventsB, 
       (In mName P) -> 
       reach P B s1 (B mName) eventsB s2 -> 
       reach P B s1 (Call mName  ) eventsB  s2

 | ReachSignal : forall s event, reach P B s (Signal event ) ( event :: nil) s  .


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
