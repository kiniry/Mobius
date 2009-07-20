Require Import  LogicPartial.
Require Import LogicPartialGhost.
Require Import LogicReach.
Require Import LogicReachGhost.
Require Import Coq.Logic.Classical_Prop.
Require Import Language.
Require Import MainPartial.

Export Logic.
Export LogicPartialGhost. 


Definition  transformInv (GInv: GmethInv) : methInv   :=
fun mName => ( fun s1 events s2=> forall g1, exists g2, ( GInv mName) s1 g1 events s2 g2 ).



(* MAIN THEOREM : derivability in logic with ghosts
 implies derivability of the respective interpretation of formulas in a logic without ghosts  *)
Lemma ghostReachImpliesStandardReach: forall  (gst: Gstmt )  (Body : Gbody )( Gpost : Gassertion)  (GSpec: GmethPost) (GInv : GmethInv)   , 
 let st := transform Body gst in 
 RULERG GSpec GInv gst Gpost -> RULER ( transformPost GSpec) (transformInv  GInv) st (fun s1 event s2 =>  forall g1, exists g2, Gpost s1 g1 event s2 g2 ).

Proof.
intros  gst Body .  intros  Gpost ; simpl;auto;
intros Gspec Ginv grule.  induction grule.  
(* ASSIGN *)
unfold transform.
apply (AffectRuleR  ( transformPost Gspec) (transformInv Ginv)  x e    (fun s1 e  s2  =>
   forall sg1 : gState, exists sg2 : gState, post s1 sg1 e s2 sg2) ).
intros.
exists sg1.

apply (H s1 s2 sg1 sg1).
assumption.
trivial.
intros.
exists sg1.
apply H0.
assumption.
trivial.
(*******************************************************************************************************)

(* IF *)
apply( IfRuleR    ( transformPost Gspec)  (transformInv Ginv)  e (transform Body stmtT)   (transform Body stmtF)  
            (fun s1 ev s2  =>  forall sg1 : gState, exists sg2 : gState, post1 s1 sg1 ev s2 sg2)
            (fun s1  ev s2  =>  forall sg1 : gState, exists sg2 : gState, post2 s1  sg1  ev s2 sg2)).
intros.

destruct H1.

assert (H01 := classic  ( eval_expr s1 e = 0) ).
elim H01.
intros.
assert (H02 := H2 H3 g1).
elim H02.
intros.
exists x.
apply (H s1 s2 g1 x).
split.
intros.
elim H5.
assumption.
intros.
assumption.


intros.
assert (H02 := H1 H3 g1).
elim H02.
intros.
exists x.
apply (H s1 s2 g1 x).
split.
intros.
assumption.
intros.
elim H3.
assumption.

intros.
exists g1.
apply H0.
assumption.
trivial.
assumption.
assumption.


   
(**************************************************************************************************)
(*WHILE*)
apply ( WhileRuleR    ( transformPost Gspec)  (transformInv Ginv)  (transform Body  st )  
   (fun (s1 : state) (event : list event) (s2 : state) => forall g1 : gState, exists g2 : gState, post s1 g1 event s2 g2)
   (fun (s1 : state) (event : list event) (s2 : state) => forall g1 : gState, exists g2 : gState, post1 s1 g1 event s2 g2)
   e 
    (fun (s1 : state) (event : list event) (s2 : state) => forall g1 : gState, exists g2 : gState, inv s1 g1 event s2 g2)

).

(*second side condition concerning weakening of postcondition *)
intros.
assert (Help := H4 g1).
elim Help. intros.

exists x.
apply H.
assumption.

intros.
exists g1.
apply H0.
assumption.
trivial.
(*side condition in case of loop termination *)
intros.
exists g1.
apply H1.
assumption.

(*inductive case for the loop body for the logic concerning properties over reachable  statements *)
assumption.

(* inductive case for the logic concerning partial correctness. Here  apply the lemma for the relation btw partial logic without and with ghost *)
apply (ghostLogicImpliesStandardLogic st  Body inv Gspec  ).
assumption.

(* side condition for the reachable states in an nonterminating execution after one iteration  *)
intros.

assert (Help := H4 g1 ).
elim Help. intros x1 INV.
clear Help.

assert (Help := H6 x1 ).
elim Help. intros x2 POST1.
exists x2.
apply (H3 s1 s2 s3 g1 x1 x2) .
assumption.
assumption.
assumption.

(*******************************************************************************************)
(* COMPOSITION *)
apply ( SeqRuleR    ( transformPost Gspec)  (transformInv Ginv)  (transform Body stmt1) 
 (transform Body stmt2)   
   (fun (s1 : state) (event : list event) (s2 : state) => forall g1 : gState, exists g2 : gState, post s1 g1 event s2 g2)
   (fun (s1 : state) (event : list event) (s2 : state) => forall g1 : gState, exists g2 : gState, post1 s1 g1 event s2 g2)
    (fun (s1 : state) (event : list event) (s2 : state) => forall g1 : gState, exists g2 : gState, postT s1 g1 event s2 g2)
 (fun (s1 : state) (event : list event) (s2 : state) => forall g1 : gState, exists g2 : gState, postRst2 s1 g1 event s2 g2)

 
).

(*side condition about weakening*)
intros.
assert (Help :=  H3 g1).
elim Help. 
intros.
exists x.
apply H.
assumption.



intros.
assert (Help := H3 g1).
elim Help. intros x1 POSTT.
clear Help.


assert (Help := H4 x1).
elim Help. intros x2 POSRT2.
clear Help.
exists x2.

apply (H0 s1 s2 s3  e1 e2 g1 x1 x2) .
assumption.
assumption.
assumption.


apply (ghostLogicImpliesStandardLogic stmt1  Body postT Gspec  ).
assumption.
assumption.

intros.
exists g1.
apply H2.
assumption.
trivial.

(*****************************************************************)
(*SKIP*)
unfold transform.
apply ( SkipRuleR    (transformPost Gspec)    (transformInv Ginv)  
   (fun s1  e   s2  => forall sg1 : gState, exists sg2 : gState, post s1 sg1 e  s2 sg2) ).
intros.
exists sg1.
apply (H s1 s2 sg1 sg1).

trivial.
trivial.



(*********************************)
(*SET*)
unfold transform.
apply ( SkipRuleR    (transformPost Gspec)    (transformInv Ginv)   (fun s1 e s2=>
   forall sg1 : gState, exists sg2 : gState, post s1 sg1 e s2 sg2) ).
intros.

exists ( gUpdate sg1 x (gEval_expr s1 sg1 e)  ).
apply  (H  s1 s2 sg1 (gUpdate sg1 x (gEval_expr s1 sg1 e))) .

trivial.
assumption.


(*********************************)
(*METHOD CALL*)
unfold transform.
apply ( CallRuleR    (transformPost Gspec)    (transformInv Ginv)  mName  (fun s1 e s2=>
   forall sg1 : gState, exists sg2 : gState, post s1 sg1 e s2 sg2) ).
intros.
unfold transformInv in H1.
assert (Help := H1 sg1).
elim Help.
intros.
exists x.
apply H.
assumption.

intros.
exists sg1.
apply H0.
assumption.
trivial.

(*********************************)
(* SIGNAL *)
apply (SignalRuleR (transformPost Gspec)   (transformInv Ginv)   (fun (s1 : state) (event0 : list BasicDef.event) (s2 : state) =>
   forall g1 : gState, exists g2 : gState, post s1 g1 event0 s2 g2) event).
intros;simpl; subst;auto.
exists g1.
apply H.
trivial.
trivial.
intros.
exists g1.
apply H0.
assumption.
trivial.
Qed.  



Lemma correctReachGhost: forall P (gb  : Gbody )  (GSpec: GmethPost) (GInv : GmethInv)   (s: Gstmt)  ( post : Gassertion),   
   RULERG GSpec GInv s post   -> 
   (forall st (N : methodNames) (spec : Gassertion),  (In N P) -> spec = (GSpec N) -> st = gb N -> RULETG GSpec st spec )  -> 
   (forall st (N : methodNames) (spec : Gassertion),  (In N P) -> spec = (GInv N) -> st = gb N -> RULERG GSpec GInv st spec )  -> 
  forall  (s1 s2 : state ) ev ,    reach  P (transformBody gb )  s1 (transform gb s) ev s2 -> forall g1, exists g2,  post s1 g1 ev s2 g2.
Proof.
intros Prog gb Gspec  Ginv st   gPost gRule methVerif methReachVerif.
intros s1 s2 ev exec.
assert ( forall (st : stmt) (N : methodNames) (spec : assertion),
            In N Prog -> spec = (transformInv Ginv) N -> st = ( transformBody gb)  N -> RULER  (transformPost Gspec) (transformInv Ginv) st spec ).
intros.
simpl;subst;auto.
unfold transformInv.
apply (  ghostReachImpliesStandardReach  (gb N) gb  (Ginv N)  Gspec Ginv  ). 


apply (  methReachVerif (gb N) N (Ginv N) ). 
assumption.
trivial.
trivial.

assert ( forall (st : stmt) (N : methodNames) (spec : assertion),
            In N Prog -> spec = (transformPost Gspec) N -> st = ( transformBody gb)  N -> RULET (transformPost Gspec) st spec ).
intros.
simpl;subst;auto.
apply  (ghostLogicImpliesStandardLogic  (gb N) gb  (Gspec N) Gspec ). 
apply (  methVerif (gb N) N (Gspec N) ). 
assumption.
trivial.
trivial.

assert (A := correctAuxReach  (transformPost Gspec)  (transformInv Ginv)  (transform gb st)  (transformBody gb) Prog  H0 H s1 s2 ev exec 
(  fun s1 e s2 => forall g1 : gState, exists g2 : gState, gPost s1 g1 e s2 g2 )

).
simpl in *.

apply A.
assert ( B:=  ghostReachImpliesStandardReach  st gb  gPost Gspec Ginv  ).

apply ( B gRule) .     
Qed. 




Lemma conservativeReach: forall GSP GINV (gb : Gbody) (s: Gstmt)  ( post : assertion) ,   
RULERG GSP GINV s (fun (s1 : state) (g1 : gState ) ev (s2 : state) ( g2 : gState ) =>   post s1 ev s2)  -> 
RULER (transformPost GSP) (transformInv GINV) (transform gb  s) post.
Proof.
intros .  
assert (H1 := ghostReachImpliesStandardReach s gb     (fun (s1 : state) (_ : gState) (e : list event)(s2 : state) (_ : gState) => post s1 e s2)  GSP GINV H);
simpl;auto.
simpl in H1.

apply ( conseqRuleReach  (transformPost GSP)    (transformInv GINV)  (transform gb  s) 
             (fun s1 e s2  => gState -> ex (fun _ : gState => post s1 e s2))  post  ).
intros. 
apply ( exi  post s1 s2). 
simpl;auto.
assumption.
Qed. 


