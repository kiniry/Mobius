Require Import  LogicPartial.
Require Import LogicPartialGhost.
Require Import Coq.Logic.Classical_Prop.
Require Import Language.

Export Logic.
Export LogicPartialGhost. 

(* THILE FILE CONTAINS A DEFINITION OF THE TRANSFORMATION FROM 
PROGRAMS WITH GHOST VARIABLES INTO PROGRAMS WHICH DO NOT TREAT GHOST.
THE FILE ALSO STATES THE MAIN LEMMA OF THIS FORMALIZATION :  
A DERIVABILITY OF A JUDGEMENT WITH GHOSTS ( PROGRAM STATEMENT 
 AND ASSERTION WITH GHOSTS )
 IN LOGIC SYSTEM FOR REASONING 
ABOUT PROGRAMS WITH GHOSTS IMPLIES DERIVABILITY OF 
THE RESPECTIVE STATTEMENT AND JUDGEMENT WITHOUT GHOST *)
Fixpoint  transform (B: Gbody)(gstmt: Gstmt){struct gstmt } :stmt  :=
match gstmt with 
 | (GAffect x e ) => (Affect x e) 
 | ( GIf e gst1 gst2) =>
   let st1 := transform B gst1 in
   let st2 := transform B gst2 in 
   (If e st1 st2)
 | (GWhile e gst) => 
   let st :=  transform B gst in 
   (While e st)
 | (GSseq gst1 gst2 )  =>
   let st1 :=  transform B gst1 in
   let st2 :=  transform B gst2 in
   (Sseq st1 st2) 
 | GSkip  => Skip
 | (GSet gv e ) => Skip 
 | ( GCall mName ) => 
   let st :=  transform B ( B mName) in 
    (Call mName )	
  | ( GSignal event) => 
    ( Signal event) 
end.

Definition  transformPost (GSpec: GmethPost) : methPost   :=
fun mName => ( fun s1 events s2=> forall g1, exists g2, ( GSpec mName) s1 g1 events s2 g2 ).

Definition  transformBody (gb: Gbody) : body   :=
fun mName => ( transform gb (gb mName )   ).
                        
(*  
Definition  transformInv (GInv: GmethInv) : methInv   :=
fun mName => ( fun s1 events s2=> forall g1, exists g2, ( GInv mName) s1 g1 events s2 g2 ).

*)

(* MAIN THEOREM : derivability in logic with ghosts
 implies derivability of the respective interpretation of formulas in a logic without ghosts  *)
Lemma ghostLogicImpliesStandardLogic: forall  (gst: Gstmt )  (Body : Gbody )( Gpost : Gassertion)  (GSpec: GmethPost)    , 
 let st := transform Body gst in 
 (* let post  :=   ( fun s1 s2 => forall (sg1: gState), exists sg2: gState, Gpost s1 sg1 s2 sg2 ) in *)
 (* let ctx := transformCtx gtx in *)
 RULETG GSpec gst Gpost -> RULET ( transformPost GSpec) st (fun s1 event s2 =>  forall g1, exists g2, Gpost s1 g1 event s2 g2 ).

Proof.
intros  gst Body .  intros  Gpost ; simpl;auto;
intros Gspec grule.  induction grule.  
(* ASSIGN *)
unfold transform.
apply (AffectRule  ( transformPost Gspec)  x e    (fun s1 e  s2  =>
   forall sg1 : gState, exists sg2 : gState, post s1 sg1 e s2 sg2) ).
intros.
exists sg1.

apply (H s1 s2 sg1 sg1).
split.
trivial.
assumption.

(*******************************************************************************************************)

(* IF *)
apply( IfRule    ( transformPost Gspec)  e (transform Body stmtT)   (transform Body stmtF)  
            (fun s1 ev s2  =>  forall sg1 : gState, exists sg2 : gState, post1 s1 sg1 ev s2 sg2)
            (fun s1  ev s2  =>  forall sg1 : gState, exists sg2 : gState, post2 s1  sg1  ev s2 sg2)).
intros.

destruct H0.

assert (H01 := classic  ( eval_expr s1 e = 0) ).
elim H01.
intros.
assert (H02 := H1 H2 g1).
elim H02.
intros.
exists x.
apply (H s1 s2 g1 x).
split.
intros.
elim H4.
assumption.
intros.
assumption.


intros.
assert (H02 := H0 H2 g1).
elim H02.
intros.
exists x.
apply (H s1 s2 g1 x).
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
 
assert( forall (s : state) ,   eval_expr s e = 0 -> forall gs1, exists gs2,  post1 s gs1 nil s gs2 ).
intros.
exists gs1.
apply ( H1 s gs1  H2).

assert(  forall (s p t : state) e1 e2 ,   eval_expr s e <> 0 -> (forall gs, exists gp, post1 s gs e1 p gp ) -> 
 (forall gp, exists gt, post1 p gp e2 t gt) -> ( forall gs, exists gt, post1 s gs (e1 ++ e2) t gt)).
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
forall (s1 s2  : state)  ev,
  (fun s3  event s4  =>
   forall sg1 : gState, exists sg2 : gState, post1 s3 sg1 event  s4 sg2) s1 ev s2 /\
  eval_expr s2 e = 0 ->
  (fun s3 event s4  =>
   forall sg1 : gState, exists sg2 : gState, post s3 sg1 event s4 sg2) s1 ev s2

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

apply (  WhileRule    ( transformPost Gspec  ) (transform Body stmt)
             (fun s1 ev s2  =>
             forall sg1 : gState,
             exists sg2 : gState, post s1 sg1 ev s2 sg2 ) 

             (fun s1  ev  s2 =>
             forall sg1 : gState,
             exists sg2 : gState, post1 s1 sg1 ev s2 sg2 ) 
             
             e 
          
).


simpl in H4.
assumption.
assumption.
assumption.
assumption.


(*******************************************************************************************)
(* COMPOSITION *)
assert (   forall (s1 s2 : state) ev1 ev2 , 
    (exists p : state,
        ( forall ( g1 : gState) , exists g2: gState,  post1 s1 g1 ev1 p g2 ) /\ 
                             ( forall ( g1 : gState) , exists g2: gState,    post2 p g1  ev2 s2 g2)) ->
  ( forall ( g1 : gState) , exists g2: gState,   post s1 g1 (ev1 ++ ev2 )  s2 g2  )).

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
           (fun s1 e s2  =>forall sg1 : gState, exists sg2 : gState, post1 s1 sg1 e s2 sg2) 
           (fun s1 e s2  =>forall sg1 : gState, exists sg2 : gState, post2 s1 sg1 e s2 sg2)  
           (fun s1 e s2  =>forall sg1 : gState, exists sg2 : gState, post s1 sg1 e s2 sg2)  
           H0 IHgrule1   IHgrule2  ).

(*****************************************************************)
(*SKIP*)
unfold transform.
apply ( SkipRule    (transformPost Gspec)   (fun s1  e   s2  => forall sg1 : gState, exists sg2 : gState, post s1 sg1 e  s2 sg2) ).
intros.
exists sg1.
apply (H s1 s2 sg1 sg1).
split.
trivial.
assumption.


(*********************************)
(*SET*)
unfold transform.
apply ( SkipRule    (transformPost Gspec)    (fun s1 e s2=>
   forall sg1 : gState, exists sg2 : gState, post s1 sg1 e s2 sg2) ).
intros.
exists ( gUpdate sg1 x (gEval_expr s1 sg1 e)  ).
apply  (H  s1 s2 sg1 (gUpdate sg1 x (gEval_expr s1 sg1 e))) .
split.
trivial.
assumption.


(*********************************)
(*METHOD CALL*)
unfold transform.
apply (  CallRule (transformPost Gspec) mName ).

intros.
unfold transformPost in H0.
assert (H2 := H0 g1 ).
elim H2.
intros.
exists x.
apply H.
assumption.

(*********************************)
(* SIGNAL *)
apply (SignalRule (transformPost Gspec)     (fun (s1 : state) (event0 : list BasicDef.event) (s2 : state) =>
   forall g1 : gState, exists g2 : gState, post s1 g1 event0 s2 g2) event).
intros;simpl; subst;auto.
exists g1.
apply H.
trivial.
trivial.
Qed.  



Lemma correctGhost: forall P (gb  : Gbody )  (GSpec: GmethPost)  (s: Gstmt)  ( post : Gassertion),   
   RULETG GSpec s post   -> 
   (forall st (N : methodNames) (spec : Gassertion),  (In N P) -> spec = (GSpec N) -> st = gb N -> RULETG GSpec st spec )  -> 
  forall  (s1 s2 : state ) ev ,    t_exec  P (transformBody gb )  s1 (transform gb s) ev s2 -> forall g1, exists g2,  post s1 g1 ev s2 g2.
Proof.
intros Prog gb Gspec  st   gPost gRule methVerif.
intros s1 s2 ev exec.
assert ( forall (st : stmt) (N : methodNames) (spec : assertion),
            In N Prog -> spec = (transformPost Gspec) N -> st = ( transformBody gb)  N -> RULET (transformPost Gspec) st spec ).
intros.
simpl;subst;auto.
apply  (ghostLogicImpliesStandardLogic  (gb N) gb  (Gspec N) Gspec ). 
apply (  methVerif (gb N) N (Gspec N) ). 
assumption.
trivial.
trivial.


assert (A := correctAux  (transformPost Gspec)  (transform gb st) (transformBody gb) Prog  H s1 s2 ev exec 
(  fun s1 e s2 => forall g1 : gState, exists g2 : gState, gPost s1 g1 e s2 g2 )

).
apply A.
assert ( B:=  ghostLogicImpliesStandardLogic  st gb  gPost Gspec  ).

apply ( B gRule) .     
Qed. 


Lemma exi: forall (post : assertion) (s1 s2 : state ) event, 
(forall ( g1 : gState), exists  g2: gState, post  s1 event s2 ) -> post s1 event s2.
Proof.
intros.
assert ( H1 := H (fun (g : gVar ) => 1 )).
elim H1.
intros.
assumption.
Qed.

Lemma conservative: forall GSP  (gb : Gbody) (s: Gstmt)  ( post : assertion) ,   
RULETG GSP s (fun (s1 : state) (g1 : gState ) ev (s2 : state) ( g2 : gState ) =>   post s1 ev s2)  -> 
RULET (transformPost GSP) (transform gb  s) post.
Proof.
intros .  
assert (H1 := ghostLogicImpliesStandardLogic s gb     (fun (s1 : state) (_ : gState) (e : list event)(s2 : state) (_ : gState) => post s1 e s2)  GSP H);
simpl;auto.
simpl in H1.

apply ( conseqRule  (transformPost GSP)  (transform gb  s)     (fun s1 e s2  => gState -> ex (fun _ : gState => post s1 e s2))  post  ).
intros. 
apply ( exi  post s1 s2). 
simpl;auto.
assumption.
Qed.


