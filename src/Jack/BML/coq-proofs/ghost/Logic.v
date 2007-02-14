(*Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef. *)
Require Import Language.
Require Import Semantic.

Export Language.
Export Semantic.

(*LOGIC IN A SP STYLE WITH EXPLICITE CONSEQUENCE RULE *)
Open Scope Z_scope.

Definition assertion := state -> state -> Prop.
(*RULES FOR REASONING OVER PROGRAMS AND ASSERTIONS.  
THE CONSEQUENCE RULE IS IMPLICITE AS IT IS INLINED IN EVERY RULE*)
Inductive RULE: stmt -> assertion -> Prop :=
 
 | AffectRule : forall  x e (post : assertion) , 
     (forall  (s1 s2: state),   s2 = update s1 x (eval_expr s1 e)   -> post s1 s2)  ->
     RULE  (Affect x e) post
 
 | IfRule : forall  e (stmtT stmtF: stmt ) ( post1  post2 post : assertion) , 
    ( forall ( s1 s2: state),  ( (not (eval_expr s1 e = 0)) -> post1 s1 s2) /\ 
                                          (eval_expr s1 e = 0 ->  post2 s1 s2)  -> post s1 s2) ->
    RULE stmtT   post1   ->
    RULE stmtF   post2   ->
    RULE (If e stmtT stmtF) post 

 | WhileRule : forall   (st : stmt ) ( post post1  : assertion) e ( inv : assertion) ,
     (forall s1 s2, post1 s1 s2  /\   eval_expr s2 e = 0-> post s1 s2 ) ->
     ( forall s p t ,   eval_expr s e <>  0 -> inv s p -> post1 p t -> post1 s t ) -> 
     (forall s , eval_expr s e = 0  -> post1 s s   ) ->
     RULE st  inv  ->
     RULE (While e st) post  

 |  SeqRule: forall (stmt1 stmt2: stmt ) ( post1  post2  post: assertion), 
   ( forall s1 s2,  (exists p , post1   s1 p /\   post2  p s2) -> post s1 s2    ) -> 
   RULE stmt1  post1 ->
   RULE stmt2 post2   ->
   RULE (Sseq stmt1 stmt2) post

 | SkipRule:   forall (post: assertion),
   ( forall (s1 s2: state ) ,  s1 = s2 -> post s1 s2) ->
   RULE Skip  post.




(*PROOF OF SOUNDNESS OF THE ABOVE RULE W.R.T. THE
 OPERATIONAL SEMANTICS GIVEN IN   Semantic.v. THE PROOF IS BY INDUCTION
 OVER THE OPERATIONAL SEMANTICS*)
Lemma correct: forall (s: stmt)  (s1 s2 : state ), (  exec_stmt  s1 s s2)  ->
forall ( post : assertion),   RULE s post   -> post s1 s2.

Proof. 
intros st   s1 s2 exec . induction exec; simpl;auto; intros post rule.
(*ASSIGN*)
inversion rule.
apply (H2 s (update s x (eval_expr s e))).
trivial.

(*IF *)
inversion rule.
apply  ( H3 s1 s2).
split.
intros.
apply ( IHexec post1).
simpl.
apply H5.
intros.
elim H.
assumption.

inversion rule.
apply  ( H3 s1 s2).
split.
intros.
elim H7.
assumption.
intros.
apply ( IHexec post2).
simpl.
apply H6.

(*WHILE*)
(*iteration case, condition holds*)
inversion rule.
apply (H2 s1 s3).
assert (H100 := IHexec2 (fun s1 s2 => post1 s1 s2 /\ eval_expr s2 e = 0 ) ).
assert ( RULE (While e stmt) (fun s1 s2 => post1 s1 s2 /\ eval_expr s2 e = 0 ) ).
apply ( WhileRule  stmt  (fun s1 s2 => post1 s1 s2 /\ eval_expr s2 e = 0 )  post1 e inv ).


intros.
assumption.
assumption.
assumption.
assumption.
assert (H102 := H100 H7).
simpl in *.
destruct H102.

split.
apply ( H3 s1 s2 s3).
assumption.
apply (IHexec1 inv H6).
assumption.
assumption.

(*false case, condition is false*)
inversion rule.
apply (H2 s1 s1).
split.
apply (H4 s1).
assumption.
assumption.

(*SEQUENCE*)
inversion rule.
apply (H1 s1 s3).
exists s2.
split.
apply (IHexec1 post1 H2).
apply (IHexec2 post2 H4).

(*SKIP *)
inversion rule.
apply (H s s).
trivial.
Qed. 
 