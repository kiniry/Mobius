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



