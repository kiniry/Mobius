(*Require Import ZArith.
Require Import Bool.
Require Import BoolEq.
Require Import List.
Require Import BasicDef. *)

Require Import LanguageGhost.
Require Import BasicDef.
Require Import Semantic.
Require Import ZArith.
Export LanguageGhost.
Open Scope Z_scope.

Definition Gassertion := state -> gState -> state -> gState -> Prop.

Inductive GRULE: Gstmt -> Gassertion -> Prop :=
 | GAffectRule : forall  x e (post : Gassertion)  , 
   (forall (s1 s2 : state ) (g1 g2: gState), 
   g1 = g2 ->  s2 = update s1 x (eval_expr s1 e) -> post s1  g1 s2 g2) ->
   GRULE (GAffect x e)  post
 
 | GIfRule : forall  e (stmtT stmtF: Gstmt ) (post1 post2 post  : Gassertion),
   (forall (s1 s2 : state ) (g1 g2: gState),     
   (not (eval_expr s1 e = 0) -> post1 s1 g1 s2 g2) /\ 
   (eval_expr s1 e = 0 ->  post2 s1 g1 s2 g2)  -> post s1 g1 s2 g2) ->	 
   GRULE stmtT  post1  ->
   GRULE stmtF  post2  ->
   GRULE (GIf e stmtT stmtF)  post           

 | GWhileRule : forall   (stmt : Gstmt ) ( post1 post : Gassertion) e ( inv : Gassertion) , 
   (forall (s1 s2 : state ) (g1 g2: gState),   post1 s1 g1 s2 g2 /\ eval_expr s2 e = 0  -> post s1 g1 s2 g2) ->
   (forall s p t  gs gp gt,   eval_expr s e <>  0 -> inv s gs p gp -> post1 p gp t gt -> post1 s gs t gt ) -> 
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


Lemma derivStandardRule: 
forall  ( inv post : Gassertion) exp stmt,  
(forall s1 s2 g1 g2,  (forall p pg, inv p pg s1 g1 -> ( inv p pg s2 g2 /\ eval_expr s2 exp = 0 ) ) -> post s1 g1 s2 g2 ) ->
( GRULE  stmt  (fun s1 g1 s2 g2 => forall p pg, eval_expr s1 exp <>  0 -> inv p pg s1 g1 -> inv p pg s2 g2 ) ) ->
let invv :=  (fun s1 g1 s2 g2  =>  forall p pg, eval_expr s1 exp <>  0 -> inv p pg s1 g1 -> inv p pg s2 g2 ) in
let postt := (fun s1 g1 s2 g2 => forall p pg, inv p pg s1 g1 -> inv p pg s2 g2  ) in 
(forall s p t sg pg tg,   eval_expr s exp <>  0 -> invv s sg  p pg -> postt p pg t tg -> postt s sg  t tg )  /\
(forall s sg, eval_expr s exp = 0  -> postt s sg  s sg ) /\
GRULE  stmt  invv .
Proof.
simpl;subst;auto;intros.
Qed.


Lemma example: forall (x y: var ) (z : gVar),
GRULE (GWhile (EbinOp Oge (Evar x) (Econst 0)) (GSseq (GSseq (GAffect x  (EbinOp Osub  (Evar x ) (Econst  1)))
            ( GAffect  y  (EbinOp Oadd  (Evar y)  (Econst 2))))( GSet  z ( gEbinOp Oadd (gvar z) (gEconst 1)) ))  )
( fun s1 g1  s2 g2 => (Z_of_nat 2) * (eval_expr s1  (Evar x )) =  (eval_expr s2  (Evar y) ) ).
Proof.
intros.
assert (INV_PRES : GRULE (GSseq (GAffect x  (EbinOp Osub  (Evar x ) (Econst  1)))
           (GSseq ( GAffect  y  (EbinOp Oadd  (Evar y)  (Econst 2)))( GSet  z ( gEbinOp Oadd (gvar z) (gEconst 1)) ))) 
         
         (fun s1 g1 s2 g2 => forall p pg, ( eval_expr s1 (EbinOp Oge (Evar x) (Econst 0))) <>0  -> 
          (Z_of_nat 2) * ( (gEval_expr p pg  (gvar z )  ) - (gEval_expr s1 g1  (gvar z ) )) =     ( (eval_expr p (Evar y )  ) - (eval_expr s1  (Evar y ) ))  /\ 
           (gEval_expr p pg  (gvar z )  ) +   (eval_expr p (Evar x ) )    = (gEval_expr s1 g1  (gvar z )  ) +   (eval_expr s1 (Evar x ) )  -> 
          (Z_of_nat 2) * ( (gEval_expr p pg  (gvar z )  ) - (gEval_expr s2 g2  (gvar z ) )) =     ( (eval_expr p (Evar y )  ) - (eval_expr s2  (Evar y ) ))  /\ 
           (gEval_expr p pg  (gvar z )  ) +   (eval_expr p (Evar x ) )    = (gEval_expr s2 g2  (gvar z )  ) +   (eval_expr s2 (Evar x ) )
 )).
apply ( GSeqRule (GAffect x  (EbinOp Osub  (Evar x ) (Econst  1))) 
             (GSseq ( GAffect  y  (EbinOp Oadd  (Evar y)  (Econst 2)))( GSet  z ( gEbinOp Oadd (gvar z) (gEconst 1)) ))
             (fun s1 g1 s2 g2 =>   (eval_expr s1  (Evar y ) ) + (Z_of_nat 2) =  (eval_expr s2   (Evar y ) )  /\  (eval_expr s1  (Evar x ) ) - (Z_of_nat 1) =  (eval_expr s2   (Evar x ) ) /\
                 (gEval_expr s1 g1  (gvar z ) ) = (gEval_expr s2 g2  (gvar z ) ) )
             ( fun s1 g1 s2 g2 => (gEval_expr s1 g1  (gvar z ) ) + (Z_of_nat 1) =  (gEval_expr s2 g2  (gvar z ) ) /\  
                (eval_expr s1  (Evar y ) )  = (eval_expr s2  (Evar y ) )  /\   (eval_expr s1  (Evar x ) )  = (eval_expr s2  (Evar x ) ) )
             (fun s1 g1 s2 g2 => forall p pg, ( eval_expr s1 (EbinOp Oge (Evar x) (Econst 0))) <>0  -> 
               (Z_of_nat 2) * ( (gEval_expr p pg  (gvar z )  ) - (gEval_expr s1 g1  (gvar z ) )) =     ( (eval_expr p (Evar y )  ) - (eval_expr s1  (Evar y ) ))  /\ 
               (gEval_expr p pg  (gvar z )  ) +   (eval_expr p (Evar x ) )    = (gEval_expr s1 g1  (gvar z )  ) +   (eval_expr s1 (Evar x ) )  -> 
               (Z_of_nat 2) * ( (gEval_expr p pg  (gvar z )  ) - (gEval_expr s2 g2  (gvar z ) )) =     ( (eval_expr p (Evar y )  ) - (eval_expr s2  (Evar y ) ) ) /\ 
           (gEval_expr p pg  (gvar z )  ) +   (eval_expr p (Evar x) )    = (gEval_expr s2 g2  (gvar z )  ) +   (eval_expr s2 (Evar x ) )
 )).

intros.
elim H.
intros.
elim H2.
clear H2 H.
intros.
destruct H as ( (HH1, HH2) ,HH3).
destruct HH3 as ( HHH1, ( HHH2,HHH3)).

rewrite HHH2 in HH1.
clear HHH2.
rewrite HHH3 in HH2.
clear HHH3.
destruct H1.
rewrite <- HH1.
destruct HH2 as (HH21, HH22).
rewrite <- HH22  in HHH1.
clear HH22.
rewrite <- HHH1.
clear HHH1.
split.
assert ( B :=   Zmult_minus_distr_l  
     (gEval_expr p pg (gvar z))  
    ( (gEval_expr s1 g1 (gvar z)) + (Z_of_nat 1)) (Z_of_nat 2)).
rewrite B.
clear B.
assert ( B := Zmult_plus_distr_r  (Z_of_nat 2)  
            (gEval_expr s1 g1 (gvar z) )
            (Z_of_nat 1 )).
rewrite B.
clear B.
assert ( B:= inj_mult 2 1).
rewrite <- B.
clear B.
assert (B:= mult_1_r 2).
rewrite B.
clear B.

assert (B:= Zopp_plus_distr  
           (( Z_of_nat 2 )*( gEval_expr s1 g1 (gvar z)))
           ( Z_of_nat 2)).




eapply ( GWhileRule 
            (GSseq (GAffect x  (EbinOp Osub  (Evar x ) (Econst  1)))
           (GSseq ( GAffect  y  (EbinOp Oadd  (Evar y)  (Econst 2)))( GSet  z ( gEbinOp Oadd (gvar z) (gEconst 1)) )))
           ( fun s1 g1  s2 g2 => (Z_of_nat 2) * (eval_expr s1  (Evar x )) =  (eval_expr s2  (Evar y) ) )
           ( fun s1 g1  s2 g2 => (Z_of_nat 2) * (eval_expr s1  (Evar x )) =  (eval_expr s2  (Evar y) ) )
           (EbinOp Oge (Evar x) (Econst 0))).



