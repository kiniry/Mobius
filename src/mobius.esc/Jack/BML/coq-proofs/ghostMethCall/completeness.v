Require Import Main. 
Require Import Coq.Logic.Classical_Prop.

(* COMPLETENESS OF THE LOGIC FOR NORMAL ASSERTIONS *)
Lemma completeness: forall (st : stmt) (post : assertion),  
( forall (s1 s2 : state ),  exec_stmt   s1  st s2  -> post s1 s2) -> RULE st post.
Proof.
intros st. 
induction st. simpl;auto. intros.

(* ASSIGN *)
apply (  AffectRule  v e).
intros.
apply ( H s1 s2).
rewrite H0.
apply  (ExecAffect s1 v e).


(* IF *)
intros.
apply (   IfRule   e st1 st2  (  fun s1 s2 => exec_stmt s1 st1 s2  )  
                                             (  fun s1 s2 => exec_stmt s1 st2 s2  )  
                                             post
                ).
intros.
apply (H s1 s2 ).
destruct H0.
 assert (exclM :=  classic  (eval_expr s1 e = 0) ).
elim exclM.
intros.
apply (  ExecIf_false s1 s2 e st1  st2 H2 (H1 H2)  ).
intros.
apply (  ExecIf_true s1 s2 e st1  st2 H2 (H0 H2)  ).
apply (  IHst1  (fun s1 s2 : state => exec_stmt s1 st1 s2)).
intros.
assumption.
apply (  IHst2  (fun s1 s2 : state => exec_stmt s1 st2 s2)).
intros.
assumption.


(* WHILE *)
intros.
apply (  WhileRule    st  post   
                                          (fun s1 s2 : state => exec_stmt s1 (While e st) s2)  
                                          
                                          e 
                                          (fun s1 s2 : state => exec_stmt s1 st s2) ).

intros.
destruct H0.
apply (H s1 s2).
assumption.
intros.
apply ( ExecWhile_true  s p   t  e  st  H0 H1 H2).
intros. 
apply ( ExecWhile_false  s   e  st  H0 ).
apply (IHst (fun s1 s2 : state => exec_stmt s1 st s2) ).
intros.
assumption.

(* SEQ *)
intros.
apply (SeqRule st1 st2  (fun s1 s2 : state => exec_stmt s1 st1 s2) 
                                         (fun s1 s2 : state => exec_stmt s1 st2 s2) 
                                         post).

intros.
elim H0.
intros.
destruct H1.
apply (H s1 s2).
apply ( ExecSseq   s1 x s2  st1  st2 H1 H2).
apply (IHst1 (fun s1 s2 : state => exec_stmt s1 st1 s2)).
trivial.
apply (IHst2 (fun s1 s2 : state => exec_stmt s1 st2 s2)).
trivial.

(* SKIP *)
intros.
apply ( SkipRule  post). 
intros.
rewrite H0.
apply  (  H s2 s2 ). 
apply (ExecSkip s2).

(* PROCEDURE CALL *)
intros.
apply ( CallRule  st m  post (fun s1 s2 : state => exec_stmt s1 (Call m st) s2  )  ).
assumption.

apply (IHst  (fun s1 s2 : state => exec_stmt s1 (Call m st) s2) ).
Qed.




