Require Import Language.
Require Import Semantic.

Export Language.
Export Semantic.

(*LOGIC IN A SP STYLE WITH EXPLICITE CONSEQUENCE RULE *)
Open Scope Z_scope.



(*RULES FOR REASONING OVER PROGRAMS AND ASSERTIONS. THIS ASSERTIONS MUST HOLD IN 
  THE TERMINAL STATE  OF THE STATEMENT EXECUTION. THUS, THIS LOGIC RULES EXPRESS PARTIAL 
  CORRECTNESS. METHODS ARE PROVIDED WITH SPECIFICATIONS WHICH STATE
   WHAT MUST HOLD IN THE TERMINAL STATE OF A METHOD. THE SPECIFICATIONS ARE GIVEN 
   BY THE MAPPING FROM METHOD NAMES TO ASSERTIONS. 
  THE CONSEQUENCE RULE IS IMPLICITE AS IT IS INLINED IN EVERY RULE*)
Inductive RULET (MS : methPost) :  stmt -> assertion -> Prop :=
 
 | AffectRule : forall   x e (post : assertion) , 
     (forall  (s1 s2: state) ,   s2 = update s1 x (eval_expr s1 e)   -> post s1 nil s2)  ->
     RULET MS  (Affect x e) post
 
 | IfRule : forall   e (stmtT stmtF: stmt ) ( post1  post2 post : assertion) , 
    ( forall ( s1 s2: state) event,  ( (not (eval_expr s1 e = 0)) -> post1 s1  event s2) /\ 
                                          (eval_expr s1 e = 0 ->  post2 s1 event s2)  -> post s1 event s2) ->
    RULET MS stmtT   post1   ->
    RULET MS stmtF   post2   ->
    RULET MS (If e stmtT stmtF) post 

 | WhileRule : forall   (st : stmt ) ( post post1  : assertion) e   ,
     (forall s1 s2 event, post1 s1 event s2  /\   eval_expr s2 e = 0-> post s1 event s2 ) ->
     ( forall s p t  event1 event2,   eval_expr s e <>  0 -> post1 s event1 p -> post1 p event2 t -> post1 s (app event1 event2) t ) -> 
     (forall s , eval_expr s e = 0  -> post1 s nil s   ) ->
     RULET MS st  post1  ->
     RULET MS  (While e st) post  

 |  SeqRule: forall  (stmt1 stmt2: stmt ) ( post1  post2  post: assertion), 
   ( forall s1 s2 event1 event2,  (exists p , post1   s1 event1 p /\   post2  p event2 s2) -> post s1 (app event1 event2) s2    ) -> 
   RULET MS stmt1  post1 ->
   RULET MS stmt2 post2   ->
   RULET MS (Sseq stmt1 stmt2) post

 | SkipRule:   forall  (post: assertion),
   ( forall (s1 s2: state )  ,  s1 = s2 -> post s1 nil s2) ->
   RULET MS Skip  post

 | CallRule : forall   ( mName : methodNames ) ( post   : assertion ) , 
   (forall (s1 s2 : state ) event,  ( MS mName ) s1 event s2 -> post s1  event s2 ) ->
   RULET MS  (Call mName )  post

 | SignalRule : forall   ( post   : assertion ) event, 
    ( forall (s1 s2: state )  ,  s1 = s2 -> post s1 (event :: nil) s2) ->   
    RULET MS (Signal event)  post. 
 

(* CONSEQUENCE RULE IS DERIVABLE *)
Lemma  conseqRule : forall MS (st : stmt )(post1 post2 : assertion) , 
(forall s1 s2 event, (post1 s1 event s2)  ->  (post2 s1 event s2) ) -> 
 RULET MS st post1 -> RULET MS st post2.
Proof.
intros MS st. induction st; 
intros post1 post2  conseq rule;
inversion rule;simpl;subst;auto.

(* ASSIGN *)
apply ( AffectRule  MS v e post2 )  .      
intros.
apply conseq.
apply H2.
assumption.

(* IF *)
apply ( IfRule MS e st1 st2 post0 post3 post2 ) .  
intros.
apply conseq.
apply H2.
assumption.
assumption.
assumption.

(* WHILE *)
assert (H1_1 :   forall ( s1 s2 : state) event, post0 s1 event s2 /\ eval_expr s2 e = 0 -> post2 s1 event s2 ).
intros.
apply conseq.
apply H1.
assumption.
apply ( WhileRule MS st post2 post0 e ).  
assumption.
assumption.
assumption.
assumption.

(* CONSEQ *)
apply ( SeqRule MS st1 st2 post0 post3 post2) .  
intros.
apply conseq.
apply H1.
assumption.
assumption.
assumption.


(* SKIP *)
apply (SkipRule MS post2).
intros; simpl;auto.

(* CALL *)
apply (CallRule MS  m post2).
intros; simpl;auto.

(* SIGNAL *)
apply (SignalRule MS post2).
intros; simpl;auto.

Qed.
 (*
(*This lemma just shows that we can prove the soundness using the right hand side of the following implication*)
Lemma aux: forall MS (st: stmt) (B : body) ( P : program)  ,  
(forall ( post : assertion),   RULET MS st post   -> forall (s1 s2 : state )  event,  (  t_exec  P B s1 st event s2) -> post s1 event s2) -> 
forall (s1 s2 : state )  event,  (  t_exec  P B s1 st event s2) ->(forall ( post : assertion),   RULET MS st post   ->post s1 event s2).
Proof.
intros.
apply H.
assumption.
assumption.
Qed.*)



(*PROOF OF SOUNDNESS OF THE ABOVE RULE W.R.T. THE
 OPERATIONAL SEMANTICS GIVEN IN   Semantic.v. THE PROOF IS BY INDUCTION
 OVER THE OPERATIONAL SEMANTICS GIVEN BY THE INDUCTIVE DEFINITION t_exec *)
 Lemma correctAux: forall MS stmt   (B : body) ( P : program) , 
 (forall st (N : methodNames) (spec : assertion),  (In N P) -> spec = (MS N) -> st = B N -> RULET MS st spec )  -> 
forall (s1 s2 : state )   events,  (  t_exec  P B s1 stmt  events s2) ->  forall Post , ( RULET MS stmt Post )  ->
Post s1 events s2. 
Proof. 
intros MS  stmt body Prog    MethVerified s1 s2 events exec; induction exec;
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

apply (H2 s1  s3  (eventsI ++ eventsC) ). 
assert (H100 := IHexec2 (fun s1 events s2 => post1 s1 events s2 /\ eval_expr s2 e = 0 ) ).
assert ( RULET MS (While e stmt) (fun s1 events s2 => post1 s1 events s2 /\ eval_expr s2 e = 0 ) ).
apply ( WhileRule MS stmt  (fun s1  events s2 => post1 s1  events s2 /\ eval_expr s2 e = 0 )  post1 e  ).


intros.
assumption.
assumption.
assumption.
assumption.
assert (H102 := H100 H0).
simpl in *.
destruct H102.

split.
apply ( H3 s1 s2 s3).
assumption.
apply (IHexec1 post1 H6).
assumption.
assumption.

(* false case, inferred automatically (*false case, condition is false*)
apply (H2 s1 s1).
split.
apply (H4 s1).
assumption.
assumption.
*)

(*SEQUENCE*)
apply (H1 s1 s3).
exists s2.
split.
apply (IHexec1 post1 H2).
apply (IHexec2 post2 H4).


(*CALL *)

apply H1.
apply (IHexec (MS mName)).
apply (MethVerified (body mName) mName ).
assumption.
trivial.
trivial.
Qed. 
 

(* MAIN SOUNDNESS THEOREM WHICH STATES THAT IF ALL METHOD BODIES HAVE A PROOF TREE W.R.T. THE
 METHOD SPECIFICATION, THEN FOR EVERY TERMINATING EXECUTION OF EVERY METHOD THE RESPECTIVE 
  METHOD  SPECIFICATION HOLDS W.R.T. THE INITIAL AND FINAL STATE OF THE TERMINATING EXECUTION *)
Lemma correct :  forall MS  M    (B : body) ( P : program) , 
 (forall st (N : methodNames) (spec : assertion),    (In N P) -> spec = (MS N) -> st = B N -> RULET MS st spec )   ->     
    (In M P) -> 
forall (s1 s2 : state )   events,  (  t_exec  P B s1 (B M)  events s2 ) -> ( MS M) s1 events s2.

Proof. 
intros.
 
apply (correctAux MS (B M) B P).
assumption.
assumption.
apply (H (B M ) M (MS M )  ).
assumption.
trivial.
trivial.
Qed.