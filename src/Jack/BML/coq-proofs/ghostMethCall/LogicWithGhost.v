(*Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef. *)

Require Import LanguageGhost.


Export LanguageGhost.

Open Scope Z_scope.

Definition Gassertion := state -> gState -> state -> gState -> Prop.

Inductive methSpec  : methodNames -> Gassertion -> Type := 
   | spec : forall  (name :  methodNames ) (ass : Gassertion ),  methSpec name ass. 


Inductive GCTX: Type :=
    | Gnil : GCTX
    | Gcons :   methodNames -> Gstmt -> Gassertion ->  GCTX -> GCTX.
  
Fixpoint  ginList (ctx: GCTX ) ( name2 :  methodNames  ) (body2 : Gstmt)( ass2 : Gassertion ){struct ctx } : Prop  :=
   match ctx with 
   | Gnil =>  False
   | Gcons name1 body1 ass1    l =>         
       ( name1 = name2 /\ body1 = body2 /\  ass1 = ass2 ) \/    ( ginList l name2 body2 ass2) 
 
end. 

Inductive GRULE:  GCTX -> Gstmt -> Gassertion -> Prop :=
 | GAffectRule : forall gctx  x e (post : Gassertion)  , 
    ( forall (s1 s2 : state ) (g1 g2: gState), 
      g1 = g2 /\  s2 = update s1 x (eval_expr s1 e) -> post s1  g1 s2 g2 	  ) ->
     GRULE gctx   (GAffect x e)  post
 
 | GIfRule : forall  gctx  e (stmtT stmtF: Gstmt ) (post1 post2 post  : Gassertion),
    ( forall (s1 s2 : state ) (g1 g2: gState),     (not (eval_expr s1 e = 0) -> post1 s1 g1 s2 g2) /\ (eval_expr s1 e = 0 ->  post2 s1 g1 s2 g2)  -> post s1 g1 s2 g2) ->	 
    GRULE gctx stmtT  post1  ->
    GRULE gctx stmtF  post2  ->
    GRULE gctx  (GIf e stmtT stmtF)  post
              

 | GWhileRule : forall  gctx  (stmt : Gstmt ) ( post1 post : Gassertion) e , 
     ( forall (s1 s2 : state ) (g1 g2: gState),   post1 s1 g1 s2 g2 /\   eval_expr s2 e = 0   -> post s1 g1 s2 g2) ->
     ( forall s p t  gs gp gt,   eval_expr s e <>  0 -> post1 s gs p gp -> post1 p gp t gt -> post1 s gs t gt ) -> 
     (forall s gs, eval_expr s e = 0  -> post1 s gs s gs  ) ->
     GRULE gctx stmt  post1  ->
     GRULE gctx (GWhile e stmt) post 

 | GSeqRule: forall gctx (stmt1 stmt2: Gstmt ) ( post1  post2 post : Gassertion), 
   ( forall (s1 s2 : state ) (g1 g2: gState),   (exists p, exists  gp, post1   s1 g1 p  gp /\  post2 p  gp s2 g2)   ->
   post  s1 g1 s2 g2 ) ->  
   GRULE gctx stmt1  post1 ->
   GRULE gctx stmt2 post2   ->
   GRULE gctx (GSseq stmt1 stmt2)  post 
   
 | GSkipRule:  forall gctx (post : Gassertion),	
   (forall (s1 s2 : state ) (g1 g2: gState),  g1 = g2 /\ s1 = s2 ->  post  s1 g1 s2 g2 ) ->
   GRULE gctx GSkip post

 | GSetRule : forall gctx x (e : gExpr) (post : Gassertion) ,
    (forall (s1 s2 : state ) (g1 g2: gState),    	g2 = gUpdate g1 x (gEval_expr s1 g1 e)  /\ s1 = s2 ->   post  s1 g1 s2 g2 ) ->
    GRULE gctx (GSet x e)  post 

 
 | GCallRule : forall  gctx (body : Gstmt )  ( mName : methodNames ) ( post  post1 : Gassertion ) , 
   (forall (s1 s2 : state )(g1 g2: gState), post1 s1 g1 s2 g2 -> post s1 g1 s2 g2 ) ->
   GRULE  (Gcons mName body post1    gctx   ) body  post1 ->
   GRULE gctx (GCall mName body)  post
 
 | GCallRuleCtx : forall gctx  (body : Gstmt ) ( mName : methodNames ) ( post  post1 : Gassertion ) , 
      (forall (s1 s2 : state )  (g1 g2: gState) ,  post1 s1 g1 s2 g2 -> post s1 g1 s2 g2 ) ->
      ( ginList gctx   mName body post1 ) ->
      GRULE gctx  (GCall mName body)  post.

