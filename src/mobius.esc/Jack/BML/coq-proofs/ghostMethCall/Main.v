Require Import  Logic.
Require Import LogicWithGhost.
Require Import Coq.Logic.Classical_Prop.


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
 | (GSet gv e ) => Skip 
 | ( GCall mName gst) => 
   let st :=  transform gst in 
    (Call mName st)	
end.

Fixpoint  transformCtx (gctx: GCTX){struct gctx } : CTX  :=
match gctx with
 | Gnil  => nil 
 | ( Gcons  name gbody gass gt) =>  
   let body  :=  transform gbody in 
   let gass  := (fun s1 s2 => forall g1, exists g2, gass s1 g1 s2 g2) in
   let t := (transformCtx gt  ) in
   ( cons name body gass t)
end.


Lemma inListTrPres: forall  gctx gbody (gpost : Gassertion) mName, 
ginList  gctx mName gbody gpost -> 
inList  (transformCtx gctx)  mName  (transform gbody )  
( fun s1 s2 => forall g1 , exists g2, gpost s1 g1 s2 g2 )   .
Proof.
intros ctx. induction ctx. intros;


simpl;auto.
intros.
assert (IH := IHctx gbody gpost mName).

unfold inList; intros.  simpl;auto. 
unfold ginList in H.
 simpl;auto. 

elim H.
intros.
left.
destruct H0 as ( n1, (n2, n3)).
split.
assumption.
split.
rewrite n2.
trivial.
rewrite n3.
trivial.

right.
unfold ginList in IH.
assert ( I := IH H0).
simpl;auto.
Qed.

(* MAIN THEOREM : derivability in logic with ghosts
 implies derivability of the respective interpretation of formulas in a logic without ghosts  *)
Lemma ghostLogicImpliesStandardLogic: forall gtx (gst: Gstmt )  ( Gpost : Gassertion), 
 let st := transform gst in 
 let post  :=   ( fun s1 s2 => forall (sg1: gState), exists sg2: gState, Gpost s1 sg1 s2 sg2 ) in
 let ctx := transformCtx gtx in 
 GRULE gtx gst Gpost -> RULE ctx st (fun s1 s2 =>  post s1 s2 ).

Proof.
intros gtx gst.  intros  Gpost ; simpl;auto;
intros grule.  induction grule.  
(* ASSIGN *)
unfold transform.
apply (AffectRule (transformCtx gctx)  x e    (fun s1 s2 : state =>
   forall sg1 : gState, exists sg2 : gState, post s1 sg1 s2 sg2) ).
intros.
exists sg1.

apply (H s1 s2 sg1 sg1).
split.
trivial.
assumption.

(*******************************************************************************************************)

(* IF *)
apply( IfRule  (transformCtx gctx)  e (transform stmtT)   (transform stmtF)  
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

assert(  forall (s p t : state),   eval_expr s e <> 0 -> (forall gs, exists gp, post1 s gs p gp ) -> 
 (forall gp, exists gt, post1 p gp t gt) -> ( forall gs, exists gt, post1 s gs t gt)).
intros.
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

apply (  WhileRule  (transformCtx gctx)  (transform stmt)
             (fun s1 s2 : state =>
             forall sg1 : gState,
             exists sg2 : gState, post s1 sg1 s2 sg2 ) 

             (fun s1 s2 : state =>
             forall sg1 : gState,
             exists sg2 : gState, post1 s1 sg1 s2 sg2 ) 
             
             e ).


simpl in H4.
assumption.
assumption.
assumption.
assumption.


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

apply (  SeqRule _  _ _   
           (fun s1 s2 : state =>forall sg1 : gState, exists sg2 : gState, post1 s1 sg1 s2 sg2) 
           (fun s1 s2 : state =>forall sg1 : gState, exists sg2 : gState, post2 s1 sg1 s2 sg2)  
           (fun s1 s2 : state =>forall sg1 : gState, exists sg2 : gState, post s1 sg1 s2 sg2)  
           H0 IHgrule1   IHgrule2  ).

(*****************************************************************)
(*SKIP*)
unfold transform.
apply ( SkipRule   (transformCtx gctx)   (fun s1 s2 : state => forall sg1 : gState, exists sg2 : gState, post s1 sg1 s2 sg2) ).
intros.
exists sg1.
apply (H s1 s2 sg1 sg1).
split.
trivial.
assumption.


(*********************************)
(*SET*)
unfold transform.
apply ( SkipRule   (transformCtx gctx)  (fun s1 s2 : state =>
   forall sg1 : gState, exists sg2 : gState, post s1 sg1 s2 sg2) ).
intros.
exists ( gUpdate sg1 x (gEval_expr s1 sg1 e)  ).
apply  (H  s1 s2 sg1 (gUpdate sg1 x (gEval_expr s1 sg1 e))) .
split.
trivial.
assumption.


(*********************************)
(*CALL case when the context does not contain the right assumption *)
assert ( H11 := CallRule (transformCtx gctx)  (transform body)   mName 
(fun s1 s2 : state =>
   forall sg1 : gState, exists sg2 : gState, post s1 sg1 s2 sg2) 

  (fun s1 s2 : state =>
   forall sg1 : gState, exists sg2 : gState, post1 s1 sg1 s2 sg2) ). 
assert( (forall s1 s2 : state,
       (fun s3 s4 : state =>
        forall sg1 : gState, exists sg2 : gState, post1 s3 sg1 s4 sg2) s1 s2 ->
       (fun s3 s4 : state =>
        forall sg1 : gState, exists sg2 : gState, post s3 sg1 s4 sg2) s1 s2) ).
intros.
elim ( H0 sg1).
intros.
exists x.
apply (H s1 s2 sg1 x). assumption.

assert (H111 := H11 H0 ).
unfold transform in *. simpl;auto.

(*********************************)
(*CALL *) 
assert ( H01 := CallRuleCtx  (transformCtx gctx)  ( transform body)  mName 
   (fun s1 s2 : state => forall sg1 : gState, exists sg2 : gState, post s1 sg1 s2 sg2)  
   (fun s1 s2 : state => forall sg1 : gState, exists sg2 : gState, post1 s1 sg1 s2 sg2)  
 ) . 
assert( B: (forall s1 s2 : state,
       (fun s3 s4 : state =>
        forall sg1 : gState, exists sg2 : gState, post1 s3 sg1 s4 sg2) s1 s2 ->
       (fun s3 s4 : state =>
        forall sg1 : gState, exists sg2 : gState, post s3 sg1 s4 sg2) s1 s2) ).
intros.
elim ( H1 sg1).
intros.
exists x.
apply (H s1 s2 sg1 x). assumption.
assert (H111 := H01 B ).

assert ( inList (transformCtx gctx) mName (transform body)
         (fun s1 s2 : state =>
          forall sg1 : gState, exists sg2 : gState, post1 s1 sg1 s2 sg2) ).

apply ( inListTrPres  gctx body post1 mName H0).  
apply H111.
assumption.
Qed.  



Lemma correctGhost: forall gctx (s: Gstmt)  ( post : Gassertion),   
  GRULE gctx s post   -> 
  forall n, 
  (forall t1 t2  b ( a : assertion)  (mName : methodNames ), 
                          ( inList  (transformCtx gctx) mName  b  a  ) ->  
                           exec_stmtN n t1 (Call mName b ) t2 -> a t1 t2 ) ->
  forall  (s1 s2 : state ),  exec_stmtN  n s1 (transform s) s2 -> forall g1, exists g2,  post s1 g1 s2 g2.
Proof.
intros gctx  st   gPost gRule.
apply ( correct (transform st)  (transformCtx gctx)  
            ( fun s1 s2 =>forall g1, exists g2,  gPost s1 g1 s2 g2)).

apply ( ghostLogicImpliesStandardLogic gctx st gPost); simpl;auto.
Qed.



Lemma exi: forall (post : assertion) (s1 s2 : state ), (forall ( g1 : gState), exists  g2: gState, post  s1 s2 ) -> post s1 s2.
Proof.
intros.
assert ( H1 := H (fun (g : gVar ) => 1 )).
elim H1.
intros.
assumption.
Qed.

(* CONSEQUENCE RULE IS DERIVABLE *)
Lemma  conseqRule : forall ctx (st : stmt )(post1 post2 : assertion), 
(forall s1 s2, (post1 s1 s2)  ->  (post2 s1 s2) ) -> 
 RULE ctx st post1 -> RULE  ctx st post2.
Proof.
intros ctx st. induction st; 
intros post1 post2 conseq rule;
inversion rule;simpl;subst;auto.

(* ASSIGN *)
apply ( AffectRule  ctx  v e post2 )  .      
intros.
apply conseq.
apply H3 .
assumption.

(* IF *)
apply ( IfRule ctx e st1 st2 post0 post3 post2 ) .  
intros.
apply conseq.
apply H3.
assumption.
assumption.
assumption.

(* WHILE *)
assert (H1_1 :   forall s1 s2 : state, post0 s1 s2 /\ eval_expr s2 e = 0 -> post2 s1 s2 ).
intros.
apply conseq.
apply H1.
assumption.
apply ( WhileRule ctx st post2 post0 e H1_1  ). 
assumption.
assumption.
assumption.


(* CONSEQ *)
apply ( SeqRule ctx st1 st2 post0 post3 post2) .  
intros.
apply conseq.
apply H1.
assumption.
assumption.
assumption.


(* SKIP *)
apply (SkipRule ctx post2).
intros; simpl;auto.

(*CALL*)
apply ( CallRule ctx st  m post2 post0  ) .
intros.
apply conseq.
apply H2.
assumption.
assumption.

(*CALL IN CONTEXT*)
apply ( CallRuleCtx ctx st  m post2 post0  ) .
intros.
apply conseq.
apply H2.
assumption.
assumption.
Qed.

Lemma conservative: forall gctx (s: Gstmt)  ( post : assertion) ,   
GRULE gctx s (fun (s1 : state) (g1 : gState ) (s2 : state) ( g2 : gState ) =>   post s1 s2)  -> 
RULE (transformCtx gctx) (transform s) post.
Proof.
intros .  
assert (H1 := ghostLogicImpliesStandardLogic gctx s   (fun (s1 : state) (_ : gState) (s2 : state) (_ : gState) => post s1 s2)  H);
simpl;auto.
simpl in H1.

apply ( conseqRule  (transformCtx gctx)  (transform s)     (fun s1 s2 : state => gState -> ex (fun _ : gState => post s1 s2))  post  ).
intros. 
apply ( exi  post s1 s2). 
simpl;auto.
assumption.
Qed.


