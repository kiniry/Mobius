Require Import  Logic.
Require Import LogicWithGhost.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Bool.Bool.

Export Logic.
Export LogicWithGhost.

(* THILE FILE CONTAINS A DEFINITION OF THE TRANSFORMATION FROM 
PROGRAMS WITH GHOST VARIABLES INTO PROGRAMS WHICH DO NOT TREAT GHOST.
THE FILE ALSO STATES THE MAIN LEMMA OF THIS FORMALIZATION :  
A DERIVABILITY OF A JUDGEMENT WITH GHOSTS ( PROGRAM STATEMENT 
 AND ASSERTION WITH GHOSTS )
 IN LOGIC SYSTEM FOR REASONING 
ABOUT PROGRAMS WITH GHOSTS IMPLIES DERIVABILITY OF 
THE RESPECTIVE STATTEMENT AND JUDGEMENT WITHOUT GHOST *)
Fixpoint  transform (gstmt: Gstmt){struct gstmt } :stmt  :=
match gstmt with 
 | (GAffect x e ) => (Affect x e) 
 | ( GIf e gst1 gst2) =>
   let st1 := transform gst1 in
   let st2 := transform gst2 in 
   (If e st1 st2)
 | (GWhile e gst) => 
   let st :=  transform gst in 
   (While e st)
 | (GSseq gst1 gst2 )  =>
   let st1 :=  transform gst1 in
   let st2 :=  transform gst2 in
   (Sseq st1 st2) 
 | GSkip  => Skip
 | (GSet gv e )=> Skip 
end.

(*
Inductive  transform : Gstmt -> stmt -> Prop := 
 | transfAffect : forall  ( e : expr) (x : var) ,
   transform  (GAffect x e ) (Affect x e) 
 | transfIf : forall (gst1  gst2 : Gstmt ) ( e : expr) (st1 st2 : stmt),
   transform gst1 st1 ->
   transform gst2 st2 ->
   transform ( GIf e gst1 gst2) (If e st1 st2)
 | transfWhile:  forall (gst : Gstmt ) ( e : expr) (st : stmt),
   transform gst st ->
   transform (GWhile e gst) (While e st)
 | transfGSseq : forall (gst1  gst2 : Gstmt )  (st1 st2 : stmt),
   transform gst1 st1 ->
   transform gst2 st2 ->
   transform (GSseq gst1 gst2 ) (Sseq st1 st2) 
 | transfGSkip : transform GSkip Skip 
 | transfSet : forall (e: gExpr) (gv : gVar) ,
   transform (GSet gv e ) Skip.    *)

(* THE LEMMA WHICH STATES THE RELATION BETWEEN THE GHOST 
AND NORMAL INFERENCE SYSTEM*)
Lemma ghostLogicImpliesStandardLogic: forall (gst: Gstmt )  ( Gpost : Gassertion), 
 let st := transform gst in 
 let post  :=   ( fun s1 s2 => forall (sg1: gState), exists sg2: gState, Gpost s1 sg1 s2 sg2 ) in
 GRULE gst Gpost -> RULE st (fun s1 s2 =>  post s1 s2 ).
Proof.
intros gst.  intros  Gpost ; simpl;auto;
intros grule.  induction grule.  
(* ASSIGN *)
unfold transform.
apply (AffectRule  x e    (fun s1 s2 : state =>
   forall sg1 : gState, exists sg2 : gState, post s1 sg1 s2 sg2) ).
intros.
exists sg1.

apply (H s1 s2 sg1 sg1).
split.
trivial.

(*******************************************************************************************************)

(* IF *)
apply( IfRule  e (transform stmtT)   (transform stmtF)  
            (fun s1 s2 : state =>  forall sg1 : gState, exists sg2 : gState, post1 s1 sg1 s2 sg2)
            (fun s1 s2 : state =>  forall sg1 : gState, exists sg2 : gState, post2 s1 sg1 s2 sg2)).
intros.

destruct H0.

assert (H01 := classic  ( eval_expr s1 e = 0) ).
elim H01.
intros.
assert (H02 := H1 H2 sg1).
elim H02.
intros.
exists x.
apply (H s1 s2 sg1 x).
split.
intros.
elim H4.
assumption.
intros.
assumption.


intros.
assert (H02 := H0 H2 sg1).
elim H02.
intros.
exists x.
apply (H s1 s2 sg1 x).
split.
intros.
assumption.
intros.
elim H2.
assumption.
assumption.
assumption.

   
(**************************************************************************************************)
(*WHILE*)
(*apply ( WhileRule  (transform stmt)  
   (fun s1 s2 : state => forall  (sg1 : gState), exists sg2 : gState, post s1 sg1 s2 sg2)  
   (fun  s1 s2 => forall ( sg1: gState ) , exists sg2 : gState, post1 s1 sg1 s2 sg2  )
   
 ) . *)
 
assert( forall (s : state) ,   eval_expr s e = 0 -> forall gs1, exists gs2,  post1 s gs1 s gs2 ).
intros.
exists gs1.
apply ( H1 s gs1 H2).

assert(  forall (s p t : state),   eval_expr s e <> 0 -> (forall gs, exists gp, inv s gs p gp ) -> 
 (forall gp, exists gt, post1 p gp t gt) -> ( forall gs, exists gt, post1 s gs t gt)).
intros s p t  H3 H4 H5 gs.
assert (H11 := H4 gs).
elim H11.
intros.
assert (H12 := H5 x).
elim H12.
intros.
assert (Hex := H0 s p t gs x x0).
exists x0.
apply Hex.
assumption.
assumption.
assumption.

assert ( 
forall s1 s2 : state,
  (fun s3 s4 : state =>
   forall sg1 : gState, exists sg2 : gState, post1 s3 sg1 s4 sg2) s1 s2 /\
  eval_expr s2 e = 0 ->
  (fun s3 s4 : state =>
   forall sg1 : gState, exists sg2 : gState, post s3 sg1 s4 sg2) s1 s2

).
intros.
destruct H4.
assert ( H7 := H4 sg1).
elim H7.
intros x post1Atx.
exists x.
assert (H10 := H s1 s2 sg1 x).
apply H10.
split.
assumption.
assumption.

apply (  WhileRule  _  
             (fun s1 s2 : state =>
             forall sg1 : gState,
             exists sg2 : gState, post s1 sg1 s2 sg2 ) 

             (fun s1 s2 : state =>
             forall sg1 : gState,
             exists sg2 : gState, post1 s1 sg1 s2 sg2 ) 
             
             e
              (fun s1 s2 : state =>
             forall sg1 : gState, exists sg2 : gState, inv s1 sg1 s2 sg2)
             H4
             H3
             H2
             IHgrule
).

(*******************************************************************************************)
(* COMPOSITION *)
assert (   forall (s1 s2 : state), 
    (exists p : state,
        ( forall ( g1 : gState) , exists g2: gState,  post1 s1 g1 p g2 ) /\ 
                             ( forall ( g1 : gState) , exists g2: gState,    post2 p g1 s2 g2)) ->
  ( forall ( g1 : gState) , exists g2: gState,   post s1 g1 s2 g2  )).

intros.
elim H0.
intros.
clear H0.
destruct H1.
assert (H10 := H0 g1 ).
elim H10.
intros.

assert (H11 := H1 x0 ).
elim H11.
intros.
exists x1.
apply (   H s1 s2 g1 x1).
exists x. 
exists x0.
split.
assumption.
assumption.

apply (  SeqRule _ _   
           (fun s1 s2 : state =>forall sg1 : gState, exists sg2 : gState, post1 s1 sg1 s2 sg2) 
           (fun s1 s2 : state =>forall sg1 : gState, exists sg2 : gState, post2 s1 sg1 s2 sg2)  
           (fun s1 s2 : state =>forall sg1 : gState, exists sg2 : gState, post s1 sg1 s2 sg2)  
           H0 IHgrule1   IHgrule2  ).

(*****************************************************************)
(*SKIP*)
unfold transform.
apply ( SkipRule   (fun s1 s2 : state => forall sg1 : gState, exists sg2 : gState, post s1 sg1 s2 sg2) ).
intros.
exists sg1.
apply (H s1 s2 sg1 sg1).
split.
trivial.
assumption.


(*********************************)
(*SET*)
unfold transform.
apply ( SkipRule  (fun s1 s2 : state =>
   forall sg1 : gState, exists sg2 : gState, post s1 sg1 s2 sg2) ).
intros.
exists ( gUpdate sg1 x (gEval_expr s1 sg1 e)  ).
apply  (H  s1 s2 sg1 (gUpdate sg1 x (gEval_expr s1 sg1 e))) .
split.
trivial.
assumption.
Qed.  


Lemma correctGhost: forall (s: Gstmt)  (s1 s2 : state ) , (  exec_stmt  s1 ( transform s) s2)  ->
   forall ( post : Gassertion),   GRULE s post   -> forall g1 , exists g2, post s1 g1 s2 g2.
Proof.
intros  st s1 s2 exec gPost rule.
apply ( correct (transform st) s1 s2 exec);
apply ( ghostLogicImpliesStandardLogic st gPost); simpl;auto.
Qed.



Lemma exi: forall (post : assertion) (s1 s2 : state ), (forall ( g1 : gState), exists  g2: gState, post  s1 s2 ) -> post s1 s2.
Proof.
intros.
assert ( H1 := H (fun (g : gVar ) => 1 )).
elim H1.
intros.
assumption.
Qed.


Lemma conservative: forall (s: Gstmt)  ( post : assertion) ,   
GRULE s (fun (s1 : state) (g1 : gState ) (s2 : state) ( g2 : gState ) =>   post s1 s2)  -> RULE (transform s) post.
Proof.
intros .  
assert (H1 := ghostLogicImpliesStandardLogic s   (fun (s1 : state) (_ : gState) (s2 : state) (_ : gState) => post s1 s2)  H);
simpl;auto.
simpl in H1.

apply ( conseqRule   (transform s)     (fun s1 s2 : state => gState -> ex (fun _ : gState => post s1 s2))  post  ).
intros. 
apply ( exi  post s1 s2). 
simpl;auto.
assumption.
Qed.


