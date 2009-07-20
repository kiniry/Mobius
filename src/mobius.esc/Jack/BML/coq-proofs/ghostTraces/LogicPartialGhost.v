(*Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef. *)

Require Import LanguageGhost.


Export LanguageGhost.

Open Scope Z_scope.



Inductive RULETG (GMS : GmethPost)  :  Gstmt -> Gassertion -> Prop :=
 | GAffectRule : forall  x e (post : Gassertion)  , 
    ( forall (s1 s2 : state ) (g1 g2: gState) , 
      g1 = g2 /\  s2 = update s1 x (eval_expr s1 e) -> post s1  g1  nil  s2 g2 	  ) ->
     RULETG GMS    (GAffect x e)  post
 
 | GIfRule : forall   e (stmtT stmtF: Gstmt ) (post1 post2 post  : Gassertion),
    ( forall (s1 s2 : state ) (g1 g2: gState) events,     (not (eval_expr s1 e = 0) -> post1 s1 g1 events s2 g2) /\ (eval_expr s1 e = 0 ->  post2 s1 g1 events s2 g2)  -> post s1 g1 events s2 g2) ->	 
    RULETG GMS stmtT  post1  ->
    RULETG GMS stmtF  post2  ->
    RULETG GMS  (GIf e stmtT stmtF)  post             

 | GWhileRule : forall  (stmt : Gstmt ) ( post1 post : Gassertion) e , 
     ( forall (s1 s2 : state ) (g1 g2: gState) events,   post1 s1 g1 events s2 g2 /\   eval_expr s2 e = 0   -> post s1 g1 events s2 g2) ->
     ( forall s p t  gs gp gt e1 e2,   eval_expr s e <>  0 -> post1 s gs e1 p gp -> post1 p gp e2 t gt -> post1 s gs (e1 ++ e2) t gt ) -> 
     (forall s gs , eval_expr s e = 0  -> post1 s gs  nil s gs  ) ->
     RULETG  GMS stmt  post1  ->
     RULETG GMS (GWhile e stmt) post 

 | GSeqRule: forall  (stmt1 stmt2: Gstmt ) ( post1  post2 post : Gassertion), 
   ( forall (s1 s2 : state ) (g1 g2: gState) e1 e2 ,   (exists p, exists  gp, post1   s1 g1  e1 p  gp /\  post2 p  gp e2  s2 g2)   ->
   post  s1 g1 ( e1 ++ e2 ) s2 g2 ) ->  
   RULETG  GMS stmt1  post1 ->
   RULETG  GMS stmt2 post2   ->
   RULETG  GMS (GSseq stmt1 stmt2)  post  
   
 | GSkipRule:  forall  (post : Gassertion),	
   (forall (s1 s2 : state ) (g1 g2: gState) e,  g1 = g2 /\ s1 = s2 ->  post  s1 g1 e s2 g2 ) ->
   RULETG GMS GSkip post

 | GSetRule : forall  x (e : gExpr) (post : Gassertion) ,
    (forall (s1 s2 : state ) (g1 g2: gState) events,    	g2 = gUpdate g1 x (gEval_expr s1 g1 e)  /\ s1 = s2 ->   post  s1 g1 events s2 g2 ) ->
    RULETG GMS (GSet x e)  post 

  | GCallRule : forall   ( mName : methodNames ) ( post   : Gassertion ) , 
   (forall (s1 s2 : state )  (g1 g2: gState)  event,  ( GMS mName ) s1 g1 event s2 g2  -> post s1 g1  event s2 g2 ) ->
    RULETG GMS  (GCall  mName )  post

 | GSignalRule : forall   ( post   : Gassertion ) event, 
    ( forall (s1 s2: state )  (g1 g2: gState) ,  s1 = s2 -> g1 = g2  -> post s1 g1(event :: nil) s2 g2) ->   
    RULETG GMS (GSignal event)  post. 
 


