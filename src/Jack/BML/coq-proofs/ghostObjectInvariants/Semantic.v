Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import BasicDef.
(*Require Import Coq.Lists.List.*)
Require Export List.
Require Import Language.



(*BIG STEP OPERATIONAL SEMANTICS WHICH DESCRIBE TERMINATING EXECUTIONS. 
   THE DEFINITION IS PARAMETRIZED WITH A PROGRAM (WHICH IS DEFINED AS A SET OF METHODS) 
   AND A FUNCTION B (OF TYPE body) WHICH MAPS METHOD NAMES TO METHOD BODIES (THOSE ARE STATEMENTS).
   THE SEMANTICS MANIPULATES INITIAL AND TERMINAL STATE BUT ALSO A TRACE OF EVENTS 
   WHICH ARE EMITTED DURING THE EXECUTION OF THE STATEMENT
*)
Inductive t_exec (P : program)(B: body) :  state -> stmt -> state  -> Prop := 

 | ExecAffect      : forall s x e, 
   t_exec  P B s  (Affect x e)  (update s x (eval_expr s  e)) 

 | ExecIf_true     : forall s1 s2  e stmtT stmtF ,
     eval_expr s1 e <>  0 -> 
     t_exec P B s1  stmtT s2  ->
     t_exec P B s1 (If e stmtT stmtF)  s2 

 | ExecIf_false    : forall s1 s2  e stmtT stmtF ,
     eval_expr s1 e =  0 -> 
     t_exec P B s1  stmtF s2  ->
     t_exec P B s1 (If e stmtT stmtF)  s2 

 | ExecWhile_true  : forall s1 s2 s3  e  stmt   ,
     eval_expr s1   e <>  0 ->
     t_exec P B s1 stmt s2  ->
     t_exec P B s2  (While e stmt)  s3   ->
     t_exec P B s1  (While e stmt) s3

 | ExecWhile_false  : forall s  e  stmt ,
     eval_expr  s  e = 0 ->
     t_exec P  B s  (While e  stmt) s
 
 | ExecSseq   : forall s1 s2 s3 stmt1 stmt2 ,
      t_exec P  B s1 stmt1  s2   -> 
      t_exec P  B s2 stmt2  s3  -> 
      t_exec P  B s1 (Sseq stmt1 stmt2)  s3 

 | ExecSkip : forall s , t_exec P B s Skip s

 | ExecCall : forall s1  s2  ( mName  : methodNames)   , 
       (In mName P) ->  	
       t_exec P  B  s1 (B mName) s2 -> 
       t_exec P  B s1  (Call mName  ) s2.
(*

 | ExecPack : forall s  , t_exec P B s   Pack   s

 | ExecUnpack : forall s, t_exec P B s Unpack s. 
*)
