Require Import Language.
Require Import Semantic.
Require Import LogicPartial.

Export Language.
Export Semantic.


Open Scope Z_scope.



(*RULES FOR REASONING OVER PROGRAMS AND ASSERTIONS (INVARIANTS) WHICH
   MUST HOLD IN EVERY REACHABLE STATE IN THE EXECUTION OF  A METHOD.
   METHODS ARE PROVIDED WITH SUCH INVARIANTS VIA THE MAPPING MS WHICH IS 
   A GLOBAL PARAMETER OF THE INDUCTIVE DEFINITION BELOW. 
   THE CONSEQUENCE RULE IS IMPLICITE AS IT IS INLINED IN EVERY RULE*)
Inductive RULER (MS : methPost) (MI : methInv ) :  stmt -> assertion -> Prop :=
 
 | AffectRuleR : forall   x e (post : assertion) , 
     (forall  (s1 s2: state) ,  s2 = update s1 x (eval_expr s1 e)   -> post s1 nil s2)  ->
    (forall  (s1 s2: state) ,   s2 = s1  -> post s1 nil s2)  ->
     RULER MS  MI (Affect x e) post
 
 | IfRuleR : forall   e (stmtT stmtF: stmt ) ( post1  post2 post : assertion) , 
    ( forall ( s1 s2: state) event,  
                                          ( (not (eval_expr s1 e = 0)) -> post1 s1  event s2) /\ 
                                          (eval_expr s1 e = 0 ->  post2 s1 event s2)   -> post s1 event s2) -> 
    (forall  (s1 s2: state) ,   s2 = s1  -> post s1 nil s2)  ->                                      
    RULER MS MI stmtT   post1   ->
    RULER MS MI stmtF   post2   ->
	
    RULER MS MI (If e stmtT stmtF) post 

 | WhileRuleR : forall   (st : stmt ) ( post post1   : assertion) e ( inv : assertion)   ,
     (forall s1 s2 event,  post1 s1 event s2   ->  post s1 event s2 ) ->
     (forall  (s1 s2: state) ,   s2 = s1  -> post1 s1 nil s2)  ->
     (forall s , eval_expr s e = 0  -> post1 s nil s   ) ->  
     RULER MS MI st post1     -> 
     RULET MS st  inv  ->
     (forall  s1 s2 s3 e1 e2,  ( inv s1 e1 s2 -> eval_expr s1 e <>  0 -> post1 s2  e2 s3 -> post1 s1 (app e1 e2) s3) )->
     RULER MS  MI  (While e st) post  

 |  SeqRuleR : forall  (stmt1 stmt2: stmt ) (post  post1 postT  postRst2 : assertion), 
    (forall s1 s2 e , ( post1 s1 e s2 -> post s1 e s2)) -> 
   (forall s1 s2 s3 e1 e2 ,  postT s1 e1 s2 -> postRst2 s2 e2 s3 ->  post1 s1 (app e1 e2 ) s3) -> 
   RULER MS MI stmt1  post1 ->
   RULET MS stmt1   postT -> 
   RULER MS MI stmt2 postRst2   ->
   (forall  (s1 s2: state) ,   s2 = s1  -> post s1 nil s2)  ->
   RULER MS MI (Sseq stmt1 stmt2) post

 | SkipRuleR :   forall  (post: assertion),
   ( forall (s1 s2: state )  ,  s1 = s2 -> post s1 nil s2) ->
   RULER MS MI Skip  post

 | CallRuleR : forall   ( mName : methodNames ) ( post   : assertion ) , 
   (forall (s1 s2 : state ) event,  ( MI mName ) s1 event s2 -> post s1  event s2 ) ->
   (forall  (s1 s2: state) ,   s2 = s1  -> post s1 nil s2)  ->
   RULER MS  MI (Call mName )  post

 | SignalRuleR : forall   ( post   : assertion ) event, 
    ( forall (s1 s2: state )  ,  s1 = s2 -> post s1 (event :: nil) s2) ->   
    ( forall (s1 s2: state )  ,  s1 = s2 -> post s1 nil s2) ->   
    RULER MS MI (Signal event)  post. 
 

(* CONSEQUENCE RULE IS DERIVABLE *)
Lemma  conseqRuleReach : forall MS MI (st : stmt )(post1 post2 : assertion) , 
(forall s1 s2 event, (post1 s1 event s2)  ->  (post2 s1 event s2) ) -> 
 RULER MS MI st post1 -> RULER MS MI st post2.
Proof.
intros MS MI st. induction st; 
intros post1 post2  conseq rule;
inversion rule;simpl;subst;auto.

(* ASSIGN *)
apply ( AffectRuleR  MS MI v e post2 )  .      
intros.
apply conseq.
apply H1.
assumption.
intros.
apply conseq.
apply H3.
assumption.
(* IF *)
apply ( IfRuleR MS MI  e st1 st2 post0 post3 post2 ) .  
intros.
apply conseq.
apply H2.
assumption.
intros.
apply conseq.
apply H3.
assumption.
assumption.
assumption.

(* WHILE *)
eapply ( WhileRuleR MS MI st post2 post0  e inv  ).
intros;simpl;auto.
assumption.
(* intros.
   apply conseq.
   apply H2. *)
assumption.
assumption.
assumption.
assumption.


(* CONSEQ *)
apply ( SeqRuleR MS MI st1 st2   post2 post0 postT postRst2) .  
intros.
apply conseq.
apply H1.
assumption.
assumption.

assumption.
assumption.
assumption.
intros.
apply conseq. 
apply H7.
assumption.


(* SKIP *)
apply (SkipRuleR MS MI post2).
intros; simpl;auto.

(* CALL *)
apply (CallRuleR MS MI  m post2).
intros; simpl;auto.
intros.
apply conseq.
simpl;auto.
(* SIGNAL *)
apply (SignalRuleR MS MI post2).
intros; simpl;auto.
intros.
apply conseq.
apply H1.
assumption.
Qed.
 
(*This lemma just shows that we can prove the soundness using the right hand side of the following implication*)
(* Lemma aux: forall MS MI (st: stmt) (B : body) ( P : program)  ,  
(forall ( post : assertion),   RULER MS MI st post   -> 
forall (s1 s2 : state )  event,  (  t_exec  P B s1 st event s2) -> post s1 event s2) -> 
forall (s1 s2 : state )  event,  (  t_exec  P B s1 st event s2) ->(forall ( post : assertion),   RULER MS MI st post   ->post s1 event s2).
Proof.
intros.
apply H.
assumption.
assumption.
Qed.
*)




(*PROOF OF SOUNDNESS OF THE ABOVE RULE W.R.T. THE
  SEMANTICS OF THE RELATION OF REACHABLE STATES GIVEN IN   Semantic.v. 
  THE REACHABILITY RELATION IS DESCRIBED BY THE INDUCTIVE TYPE reach IN 
  Semantic.v.
  THE PROOF IS BY INDUCTION OVER THE RELATION OF REACHABLE STATES*)
Lemma correctAuxReach: forall MS MI stmt   (B : body) ( P : program) , 
 (forall st (N : methodNames) (spec : assertion),  (In N P) -> spec = (MS N) -> st = B N -> RULET MS st spec )  -> 
 (forall st (N : methodNames) (spec : assertion),  (In N P) -> spec = (MI N) -> st = B N -> RULER MS MI st spec )  -> 
forall (s1 s2 : state )   events,  (  reach  P B s1 stmt  events s2) ->  forall Post , ( RULER MS  MI stmt Post )  ->
Post s1 events s2.

Proof. 
intros MS MI  stmt body Prog    MethVerified MethInvVerified  s1 s2 events exec; induction exec;
intros Post rule ; inversion rule; simpl; subst; auto.

(* intros post rule; *)


(*assign automatically eliminated*)
(*IF *)

apply  ( H3 s1 s2).

split.
intros.

apply ( IHexec post1).
assumption.
intros.
elim H.
assumption.


apply  ( H3 s1 s2).
split.
intros.

intros.
elim H0.
assumption.
intros.
apply ( IHexec post2).
assumption.

(*WHILE*)
(*iteration case, condition holds*)

apply (H2 s1  s2  (eventsB) ). 
apply (IHexec post1).
assumption.

apply (H3 s1  s3  (eventsB ++ eventsW ) ). 
apply (H9 s1 s2 s3).
apply ( correctAux MS stmt  body Prog MethVerified ). 
assumption.
assumption.
assumption.
apply (IHexec post1 ) .
apply ( WhileRuleR MS MI  stmt  post1 post1 e inv) .
intros;simpl;auto.
intros.
apply H4.
assumption.
assumption.
assumption.
assumption.
assumption.

(*SEQUENCe*)
apply (IHexec  Post) .
apply (conseqRuleReach MS MI stmt1 post1 Post).
assumption.
assumption.

apply H2.
apply ( H3 s1 s2 s3 events1 events2).
apply ( correctAux MS stmt1 body  Prog).
assumption. 
assumption.
assumption.

apply ( IHexec postRst2).
assumption.



(*CALL *)

apply H1.
apply (IHexec (MI mName)).
apply (MethInvVerified (body mName) mName ).
assumption.
trivial.
trivial.

Qed. 
 

(* Main theorem which states that if all methods in a program are proven correct in the logic RULER 
    w.r.t. to their specifications for invariants (have a proof tree) 
then the specified invariant holds w.r.t.  every reachable state in a method execution and the initial state of the execution   *)
Lemma correctReach :  forall MS MI M    (B : body) ( P : program) , 
 (forall st (N : methodNames) (spec : assertion),  (In N P) ->  spec = (MS N) -> st = B N -> RULET MS st spec )   ->     
 (forall st (N : methodNames) (spec : assertion),  (In N P) ->  spec = (MI N) -> st = B N -> RULER MS MI st spec )  -> 
    (In M P) -> 
forall (s1 s2 : state )   events,  (  reach  P B s1 (B M)  events s2) ->  ( MI M) s1 events s2.

Proof. 
intros.
 
apply (correctAuxReach MS MI  (B M) B P).
assumption.
assumption.
assumption.
apply (H0 (B M)  M (MI M)   ).
assumption.
trivial.
trivial.
Qed.


