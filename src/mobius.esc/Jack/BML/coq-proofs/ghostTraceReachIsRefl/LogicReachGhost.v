Require Import LanguageGhost.
Require Import LogicPartial.
Require Import LogicPartialGhost.
Export LanguageGhost.


(*LOGIC IN A SP STYLE WITH EXPLICITE CONSEQUENCE RULE *)
Open Scope Z_scope.



(*RULES FOR REASONING OVER PROGRAMS AND ASSERTIONS.  
THE CONSEQUENCE RULE IS IMPLICITE AS IT IS INLINED IN EVERY RULE*)
Inductive RULERG (MS : GmethPost) (MI : GmethInv ) :  Gstmt -> Gassertion -> Prop :=
 
 | AffectRuleRG : forall   x e (post : Gassertion) , 
     (forall  (s1 s2: state) (g1 g2 : gState ),s2 = update s1 x (eval_expr s1 e)  -> g2 = g1 -> post s1 g1  nil s2 g2)  ->
     (forall  (s1 s2: state) (g1 g2 : gState),   s2 = s1 -> g2 = g1  -> post s1 g1 nil s2 g2)  ->
     RULERG MS  MI (GAffect x e) post
 
 | IfRuleRG : forall   (e : expr) (stmtT stmtF: Gstmt ) ( post1  post2 post : Gassertion) , 
    ( forall ( s1 s2: state) (g1 g2 : gState ) event,  ( (not (eval_expr s1 e = 0)) -> post1 s1  g1 event s2 g2 ) /\ 
                                          (eval_expr s1 e = 0 ->  post2 s1 g1 event s2 g2 )  -> post s1 g1 event s2 g2 ) -> 
    (forall  (s1 s2: state) (g1 g2 : gState ),   s2 = s1  -> g2 = g1 -> post s1 g1 nil s2 g2)  ->  
    RULERG MS MI stmtT   post1   ->
    RULERG MS MI stmtF   post2   ->
	
    RULERG MS MI (GIf e stmtT stmtF) post 

 | WhileRuleRG : forall   (st : Gstmt ) ( post post1   : Gassertion) e ( inv : Gassertion)   ,
     (forall s1 s2 g1 g2 event, post1 s1 g1 event s2 g2   ->  post s1 g1  event s2 g2) ->
      (forall  (s1 s2: state) (g1 g2 : gState ),   s2 = s1 -> g2 = g1 -> post1 s1 g1 nil s2 g2)  ->
     (* ( forall s p t  event1 event2,   eval_expr s e <>  0 -> inv s event1 p -> post1 p event2 t -> post1 s (app event1 event2) t ) ->   *)
     (forall s g, eval_expr s e = 0  -> post1 s g nil s g   ) ->  
     
     RULERG MS MI st post1     -> 
     RULETG MS st  inv  ->
     (forall  s1 s2 s3 g1 g2 g3 e1 e2,  ( inv s1 g1 e1 s2 g2  -> eval_expr s1 e <>  0 -> post1 s2 g2  e2 s3 g3 -> post1 s1 g1 (app e1 e2) s3 g3) )->
     RULERG MS  MI  (GWhile e st) post  


 |  SeqRuleRG : forall  (stmt1 stmt2: Gstmt ) (post  post1 postT  postRst2 : Gassertion), 
  ( forall s1 s2  e g1 g2 , ( post1 s1 g1 e s2 g2 -> post s1 g1  e s2 g2 )) -> 
   (forall s1 s2 s3 e1 e2 g1 g2 g3,  postT s1 g1 e1 s2 g2 -> postRst2 s2 g2 e2 s3 g3 ->  post1 s1 g1 (app e1 e2 ) s3 g3 ) -> 
   RULERG MS MI stmt1  post1 ->
   RULETG  MS stmt1   postT -> 
   RULERG MS MI stmt2 postRst2   ->
  (forall  (s1 s2: state) (g1 g2 : gState ),   s2 = s1 -> g2 = g1 -> post s1 g1  nil s2 g2)  ->
   RULERG MS MI (GSseq stmt1 stmt2) post

 | SkipRuleRG :   forall  (post: Gassertion),
   ( forall (s1 s2: state ) g1 g2  ,  s1 = s2 -> g2 = g1 -> post s1 g1 nil s2 g2 ) ->
   RULERG MS MI GSkip  post

 | SetRuleG :  forall   x e (post : Gassertion) , 
     (forall  (s1 s2: state) (g1 g2 : gState ),   g2 = gUpdate g1 x (gEval_expr  s1 g1 e) -> s1 = s2  -> post s1 g1  nil s2 g2)  ->
     (forall  (s1 s2: state) (g1 g2 : gState ),   s2 = s1 -> g2 = g1 -> post s1 g1 nil s2 g2)  ->
     RULERG MS  MI (GSet x e) post


 | CallRuleRG : forall   ( mName : methodNames ) ( post   : Gassertion ) , 
   (forall (s1 s2 : state ) event g1 g2,  ( MI mName ) s1 g1 event s2 g2  -> post s1 g1  event s2 g2 ) ->
   (forall  (s1 s2: state) (g1 g2 : gState ),   s2 = s1 -> g2 = g1 -> post s1 g1 nil s2 g2)  ->
   RULERG MS  MI (GCall mName )  post

 | SignalRuleRG : forall   ( post   : Gassertion ) event, 
    ( forall (s1 s2: state ) g1 g2 ,  s1 = s2 -> g1 = g2 -> post s1 g1 (event :: nil) s2 g2 ) ->   
    ( forall (s1 s2: state ) g1 g2 ,  s1 = s2 -> g2 = g1 -> post s1 g1 nil s2 g2 ) -> 	
    RULERG MS MI (GSignal event)  post. 
 
(* 
(* CONSEQUENCE RULE IS DERIVABLE *)
Lemma  conseqRule : forall MS MI (st : stmt )(post1 post2 : assertion) , 
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
apply H2.
assumption.

(* IF *)
apply ( IfRuleR MS MI  e st1 st2 post0 post3 post2 ) .  
intros.
apply conseq.
apply H2.
assumption.
assumption.
assumption.

(* WHILE *)
eapply ( WhileRuleR MS MI st post2 post0  e inv  ).
intros;simpl;auto.
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

(* SKIP *)
apply (SkipRuleR MS MI post2).
intros; simpl;auto.

(* CALL *)
apply (CallRuleR MS MI  m post2).
intros; simpl;auto.

(* SIGNAL *)
apply (SignalRuleR MS MI post2).
intros; simpl;auto.

Qed.
 
(*This lemma just shows that we can prove the soundness using the right hand side of the following implication*)
Lemma aux: forall MS MI (st: stmt) (B : body) ( P : program)  ,  
(forall ( post : assertion),   RULER MS MI st post   -> 
forall (s1 s2 : state )  event,  (  t_exec  P B s1 st event s2) -> post s1 event s2) -> 
forall (s1 s2 : state )  event,  (  t_exec  P B s1 st event s2) ->(forall ( post : assertion),   RULER MS MI st post   ->post s1 event s2).
Proof.
intros.
apply H.
assumption.
assumption.
Qed.

Variable A : assertion.


(*PROOF OF SOUNDNESS OF THE ABOVE RULE W.R.T. THE
 OPERATIONAL SEMANTICS GIVEN IN   Semantic.v. THE PROOF IS BY INDUCTION
 OVER THE OPERATIONAL SEMANTICS*)
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
apply (H8 s1 s2 s3).
apply ( correctAux MS stmt  body Prog MethVerified ). 
assumption.
assumption.
assumption.
apply (IHexec post1 ) .
apply ( WhileRuleR MS MI  stmt  post1 post1 e inv) .
intros;simpl;auto.
assumption.
assumption.
assumption.
assumption.

(*SEQUENCe*)
apply (IHexec  Post) .
apply (conseqRule MS MI stmt1 post1 Post).
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
 

(* general lemma which states that if all methods in a program are proven correct w.r.t. to their specifications 
then they are valid w.r.t. their specifications  *)
Lemma correctReach :  forall MS MI M    (B : body) ( P : program) , 
 (forall st (N : methodNames) (spec : assertion),  (In N P) -> spec = (MS N) -> st = B N -> RULET MS st spec )   ->     
 (forall st (N : methodNames) (spec : assertion),  (In N P) -> spec = (MI N) -> st = B N -> RULER MS MI st spec )  -> 
    (In M P) -> 
forall (s1 s2 : state )   events,  (  reach  P B s1 (B M)  events s2) ->   ( RULER MS MI (B M) ( MI M) )  -> ( MI M) s1 events s2.

Proof. 
intros.
 
apply (correctAuxReach MS MI  (B M) B P).
assumption.
assumption.
assumption.
assumption.
Qed. *)