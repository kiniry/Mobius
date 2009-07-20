(*Require Import ZArith.*)
Require Import Bool.
Require Import BoolEq.
Require Import BasicDef.
Require Import Language.

(*Require Import  Coq.Init.Peano. *)
Inductive exec_stmtN : nat -> state -> stmt -> state -> Prop := 

 | ExecAffectN      : forall (n : nat) s x e, 
     exec_stmtN (n +1) s (Affect x e) (update s x (eval_expr s e))

 | ExecIf_trueN     : forall n s1 s2 e stmtT stmtF,
     
     eval_expr s1 e <> 0  -> 
     exec_stmtN (n+1) s1 stmtT s2 ->
     exec_stmtN (n +1) s1 (If e stmtT stmtF) s2

 | ExecIf_falseN    : forall n s1 s2 e stmtT stmtF,
     
     eval_expr s1 e = 0 -> 
     exec_stmtN (n +1) s1 stmtF s2 ->
     exec_stmtN (n +1) s1 (If e stmtT stmtF) s2

 | ExecWhile_trueN  : forall n s1 s2 s3 e  stmt,
     
     eval_expr s1 e <> 0 ->
     exec_stmtN (n + 1) s1 stmt s2 ->
     exec_stmtN (n + 1) s2 (While e stmt) s3 ->
     exec_stmtN (n + 2) s1 (While e stmt) s3

 | ExecWhile_falseN  : forall n s1 e  stmt,
     
     eval_expr s1 e = 0 ->
     exec_stmtN (n +1) s1 (While e  stmt) s1
 
 | ExecSseqN   : forall n s1 s2 s3 i stmt,
      
      exec_stmtN (n + 1)  s1 i s2 -> 
      exec_stmtN (n+1) s2 stmt s3 -> 
      exec_stmtN (n+1) s1 (Sseq i stmt) s3

 | ExecSkipN : forall n s,  exec_stmtN (n +1) s Skip s
 
 | ExecCallN : forall n s1 s2 stmt mName,  
       
       exec_stmtN (n+1) s1 stmt s2 -> 
       exec_stmtN ( n + 2) s1 (Call mName  stmt) s2.


(*Require Import  Coq.Init.Peano. *)
Inductive exec_stmt :  state -> stmt -> state -> Prop := 

 | ExecAffect     : forall s x e, 
     exec_stmt s (Affect x e) (update s x (eval_expr s e))

 | ExecIf_true    : forall  s1 s2 e stmtT stmtF,
     
     eval_expr s1 e <> 0  -> 
     exec_stmt  s1 stmtT s2 ->
     exec_stmt s1 (If e stmtT stmtF) s2

 | ExecIf_false    : forall  s1 s2 e stmtT stmtF,
     
     eval_expr s1 e = 0 -> 
     exec_stmt  s1 stmtF s2 ->
     exec_stmt  s1 (If e stmtT stmtF) s2

 | ExecWhile_true  : forall s1 s2 s3 e  stmt,
     
     eval_expr s1 e <> 0 ->
     exec_stmt s1 stmt s2 ->
     exec_stmt s2 (While e stmt) s3 ->
     exec_stmt s1 (While e stmt) s3

 | ExecWhile_false  : forall  s1 e  stmt,
     
     eval_expr s1 e = 0 ->
     exec_stmt  s1 (While e  stmt) s1
 
 | ExecSseq   : forall s1 s2 s3 i stmt,
      
      exec_stmt  s1 i s2 -> 
      exec_stmt  s2 stmt s3 -> 
      exec_stmt  s1 (Sseq i stmt) s3

 | ExecSkip : forall  s,  exec_stmt  s Skip s
 
 | ExecCall: forall  s1 s2 stmt mName,  
       
       exec_stmt s1 stmt s2 -> 
       exec_stmt s1 (Call mName  stmt) s2.


(*TO BE CONTINUED *)
(*
Lemma execNimpliesExec : forall s1 s2 stmt ,  
( exists n , exec_stmtN  n s1 stmt s2) ->  exec_stmt s1 stmt s2.

Proof. intros s1 s2 stmt. induction stmt.
intros.
elim H.
intros.
inversion H0.
simpl; subst;auto.
apply (ExecAffect ).

intros.
elim H.
intros.
inversion H0.
simpl;subst;auto.
apply ExecIf_true .
assumption.
apply IHstmt1.

exists (n + 1)%nat.
assumption.
simpl;subst;auto.
apply ExecIf_false.
assumption.
apply IHstmt2.

exists (n + 1)%nat.
assumption.


intros.

Qed. *)
 
Lemma levelgt0: forall  st s1 s2 , exec_stmtN 0 s1 st s2  -> False. 
Proof.
intros  st s1 s2 exec. induction st; inversion exec; simpl; subst; auto; omega. 
Qed.


Lemma forSmallerAlso : forall  n1 n2 st post,
      (n1  < n2)%nat ->    
     ( forall m s1 s2, ( m <= n2 )%nat -> exec_stmtN m s1 st s2 ->   post s1 s2 ) ->
     ( forall m s1 s2, ( m <= n1 )%nat -> exec_stmtN m s1 st s2 ->   post s1 s2 ).
Proof.
intros.
apply (X m s1 s2).
assert (H100 := le_lt_trans  m n1 n2 H0 H ). 

apply ( lt_le_weak m n2). 
assumption.
assumption.
Qed.

Lemma monot:  forall m st s1 s2  ,  exec_stmtN m s1 st s2 -> forall n ,  ( m <= n )%nat ->
    exec_stmtN n s1 st s2.
Proof.
intros m st  s1 s2 execN. 
induction execN. 
(* ASSIGN *)
intros.
assert (C := ExecAffectN   (n0 - 1)  s x e). 
 
assert (  (n0 - 1 + 1)%nat = n0).
omega.
rewrite  H0 in C.
clear H0.
assumption.

(*IF then*)
intros.
assert ( C := ExecIf_trueN    (n0 - 1)  s1 s2 e stmtT stmtF).
assert ( (n0 - 1 + 1)%nat = n0).
omega.
rewrite  H1 in C.
apply C.
assumption.
apply IHexecN.
assumption.
(*IF else*)
intros.
assert ( C := ExecIf_falseN    (n0 - 1)  s1 s2 e stmtT stmtF).
assert ( (n0 - 1 + 1)%nat = n0).
omega.
rewrite  H1 in C.
apply C.
assumption.
apply IHexecN.
assumption.


(*WHILE iteration*)
intros.
assert(C := ExecWhile_trueN  ( n0 -2  )   s1 s2 s3 e  stmt ).
assert ( (n0 - 2 + 2)%nat = n0).
omega.
rewrite  H1 in C.
clear H1.
assert ( (n0 - 2 + 1)%nat = (n0 - 1)%nat).
omega.
rewrite  H1 in C.
clear H1.
apply C.

assumption.

apply IHexecN1 .
omega.
apply IHexecN2.
omega.

(* WHILE termination *)
intros.
assert ( C := ExecWhile_falseN   (n0 -1) s1 e  stmt).
assert ( (n0 - 1 + 1)%nat = n0).
omega.
rewrite  H1 in C.
apply C.
assumption.

(* CONSEQUENCE *)
intros.
assert ( C := ExecSseqN  (n0 -1) s1 s2 s3 i stmt ).
assert ( (n0 - 1 + 1)%nat = n0).
omega.
rewrite  H0 in C.
apply C.
apply IHexecN1.
assumption.
apply IHexecN2.
assumption.

(* SKIP *)
intros.
assert ( C := ExecSkipN  (n0 - 1) s ).
assert ( (n0 - 1 + 1)%nat = n0).
omega.
rewrite  H0 in C.
assumption.

(* CALL *)
intros.
assert (  C := ExecCallN ( n0 - 2) s1 s2 stmt mName). 
 assert ( (n0 - 2 + 2)%nat = n0).
omega.
rewrite  H0 in C.
clear H0.
assert ( (n0 - 2 + 1)%nat = (n0 - 1)%nat).
omega.
rewrite  H0 in C.
clear H0.
apply C.
apply IHexecN.
omega.
Qed.

Lemma forSmallerAlso1 : forall  n1 n2 st post,
      (n1  < n2)%nat ->    
     ( forall s1 s2, exec_stmtN n2 s1 st s2 ->   post s1 s2 ) ->
     ( forall s1 s2, exec_stmtN n1 s1 st s2 ->   post s1 s2 ).
Proof.
intros.
apply (X  s1 s2).
apply (monot n1 st s1 s2 H0).
omega.
Qed.

(*

(*INDUCTION ON N *)
Lemma auxCall : 
forall (n: nat) (s1 s2: state) (post : assertion) (st : Language.stmt)  (mName : methodNames) , 
((forall (t1 t2 : state),
      (forall m, ( m <= n )%nat ->    exec_stmtN m t1 (Call mName st) t2 -> post t1 t2)) -> 
                              ( forall m , ( m <= n )%nat -> exec_stmtN m s1 st s2 ->   post s1 s2 ) )  ->  
(forall m , ( m <= n)%nat  ->exec_stmtN m s1  (Call mName st)   s2 -> post s1 s2). 
Proof.

intros n. induction n.  intros. 
(*n = 0*)
assert ( ( 0 = m) %nat).
apply (  le_n_O_eq  m H0).
rewrite <- H2 in H1. 
assert ( c := levelgt0  (Call mName st) s1 s2 H1). 
elim c.

(*inductive case*)
intros.
assert (H100 := forSmallerAlso n (S n) )
assert ( H11 := IHn s1 s2 post st mName).

assert(((forall (t1 t2 : state) (m : nat),
        (m <= n)%nat -> exec_stmtN n t1 (Call mName st) t2 -> post t1 t2) ->
       forall m : nat, (m <= n)%nat -> exec_stmtN n s1 st s2 -> post s1 s2) ).
intros.
eapply H.
intros.
apply (H2 t1 t2 m1 ).

assert ( ((forall (t1 t2 : state) (mName : methodNames) (m : nat),
        (m < n)%nat -> exec_stmtN n t1 (Call mName st) t2 -> post t1 t2) ->
       post s1 s2)   ).

intros.
apply H.
intros.
apply ( H2 t1 t2 mName m0).
omega.
Qed.


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
