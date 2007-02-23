(*Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef. *)

Require Import LanguageGhost.
Require Import Semantic.

Export LanguageGhost.
Open Scope Z_scope.

Definition Gassertion := state -> gState -> state -> gState -> Prop.

Inductive GRULE: Gstmt -> Gassertion -> Prop :=
 | GAffectRule : forall  x e (post : Gassertion)  , 
    ( forall (s1 s2 : state ) (g1 g2: gState), 
      g1 = g2 /\  s2 = update s1 x (eval_expr s1 e) -> post s1  g1 s2 g2 	  ) ->
     GRULE (GAffect x e)  post
 
 | GIfRule : forall  e (stmtT stmtF: Gstmt ) (post1 post2 post  : Gassertion),
    ( forall (s1 s2 : state ) (g1 g2: gState),     (not (eval_expr s1 e = 0) -> post1 s1 g1 s2 g2) /\ (eval_expr s1 e = 0 ->  post2 s1 g1 s2 g2)  -> post s1 g1 s2 g2) ->	 
    GRULE stmtT  post1  ->
    GRULE stmtF  post2  ->
    GRULE (GIf e stmtT stmtF)  post
              

 | GWhileRule : forall   (stmt : Gstmt ) ( post1 post : Gassertion) e ( inv : Gassertion) , 
     ( forall (s1 s2 : state ) (g1 g2: gState),   post1 s1 g1 s2 g2 /\   eval_expr s2 e = 0   -> post s1 g1 s2 g2) ->
     ( forall s p t  gs gp gt,   eval_expr s e <>  0 -> inv s gs p gp -> post1 p gp t gt -> post1 s gs t gt ) -> 
     (forall s gs, eval_expr s e = 0  -> post1 s gs s gs  ) ->
     GRULE stmt  inv  ->
     GRULE (GWhile e stmt) post 

 | GSeqRule: forall (stmt1 stmt2: Gstmt ) ( post1  post2 post : Gassertion), 
   ( forall (s1 s2 : state ) (g1 g2: gState),   (exists p, exists  gp, post1   s1 g1 p  gp /\  post2 p  gp s2 g2)   ->
   post  s1 g1 s2 g2 ) ->  
   GRULE stmt1  post1 ->
   GRULE stmt2 post2   ->
   GRULE (GSseq stmt1 stmt2)  post 
   
 | GSkipRule:  forall (post : Gassertion),	
   (forall (s1 s2 : state ) (g1 g2: gState),  g1 = g2 /\ s1 = s2 ->  post  s1 g1 s2 g2 ) ->
   GRULE GSkip post

 | GSetRule : forall x (e : gExpr) (post : Gassertion) ,
    (forall (s1 s2 : state ) (g1 g2: gState),    	g2 = gUpdate g1 x (gEval_expr s1 g1 e)  /\ s1 = s2 ->   post  s1 g1 s2 g2 ) ->
    GRULE (GSet x e)  post .

Axiom ext: forall ( A : Gassertion), (fun s1 s2 => A s1 s2) = A.

(*Lemma correct: forall (s: stmt) (s1 s2 : state ),
 (  exec_stmt  s1 s s2) -> forall ( post : assertion),  RULE s post -> post s1 s2.

Proof.
intros st  s1 s2 execRel.
induction execRel;intros.

(*case assign*)
inversion H.
trivial.

(*case if *)
intros.
inversion H0.
split.
intros. apply IHexecRel.
simpl in *.
assert ( H10 := ext post1).
rewrite H10.
assumption.
intros.
elim H. assumption.

inversion H0.
split.
intros. elim  H7.
assumption.
intros.
apply IHexecRel.
assert ( H10 := ext post2).
rewrite H10.
assumption.


(*while case*)
intros.
inversion H0.


assert ( IH1 := 
              IHexecRel1  
              inv
              H6).

simpl in *.

assert ( IH2 := IHexecRel2 post  H0).
rewrite <- H5 in  IH2.
destruct IH2.

split.
apply ( H3 s1 s2 s3).
assumption.
assumption.
assumption.
assumption.

inversion H0.
split.
apply (H4  s1).
assumption.
assumption.


(*sequence*)
intros.
inversion H.


assert ( H7 := IHexecRel1    post1  H2).
assert ( H9:=  IHexecRel2  post2  H4).
exists s2.
split.
assumption.
assumption.

Qed.
*)

